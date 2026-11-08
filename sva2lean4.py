"""Translate a documented subset of concurrent SVA into Lean 4 propositions.

Supported syntax: assert property, a single posedge/negedge clocking event,
Boolean signals/constants, !, &&, ||, ==, !=, $rose/$fell, ##N, |->, and |=>.
This is intentionally not a complete SystemVerilog parser; unsupported syntax
is rejected rather than translated approximately.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass


class SVACompileError(ValueError):
    """Raised when an assertion uses syntax outside the supported subset."""


@dataclass(frozen=True)
class Token:
    value: str
    position: int


class ExpressionParser:
    _unsupported_keywords = {
        "accept_on",
        "and",
        "always",
        "assert",
        "assume",
        "before",
        "cover",
        "else",
        "eventually",
        "first_match",
        "iff",
        "if",
        "implies",
        "intersect",
        "let",
        "nexttime",
        "not",
        "negedge",
        "or",
        "posedge",
        "property",
        "reject_on",
        "sequence",
        "s_always",
        "s_eventually",
        "s_nexttime",
        "s_until",
        "s_until_with",
        "strong",
        "sync_accept_on",
        "sync_reject_on",
        "throughout",
        "until",
        "until_with",
        "weak",
        "within",
    }
    _token_re = re.compile(
        r"\s+|"
        r"(?P<op>\|=>|\|->|##|&&|\|\||==|!=|[()!,])|"
        r"(?P<literal>[0-9]+'[bB][01xXzZ]+|[0-9]+)|"
        r"(?P<identifier>[A-Za-z_$][A-Za-z0-9_$]*)"
    )

    def __init__(self, expression: str):
        self.tokens: list[Token] = []
        position = 0
        while position < len(expression):
            match = self._token_re.match(expression, position)
            if not match:
                raise SVACompileError(
                    f"Unsupported token at character {position}: "
                    f"{expression[position:position + 20]!r}"
                )
            if not match.group().isspace():
                self.tokens.append(Token(match.group(), position))
            position = match.end()
        self.index = 0

    def _peek(self) -> str | None:
        return self.tokens[self.index].value if self.index < len(self.tokens) else None

    def _take(self, expected: str | None = None) -> str:
        value = self._peek()
        if value is None:
            raise SVACompileError("Unexpected end of assertion")
        if expected is not None and value != expected:
            raise SVACompileError(f"Expected {expected!r}, found {value!r}")
        self.index += 1
        return value

    def parse(self):
        result = self._parse_implication()
        if self._peek() is not None:
            token = self.tokens[self.index]
            raise SVACompileError(
                f"Unexpected token {token.value!r} at character {token.position}"
            )
        _validate_expression(result)
        return result

    def _parse_implication(self):
        left = self._parse_or()
        if self._peek() in ("|->", "|=>"):
            operator = self._take()
            return (operator, left, self._parse_implication())
        return left

    def _parse_or(self):
        result = self._parse_and()
        while self._peek() == "||":
            self._take()
            result = ("or", result, self._parse_and())
        return result

    def _parse_and(self):
        result = self._parse_sequence()
        while self._peek() == "&&":
            self._take()
            result = ("and", result, self._parse_sequence())
        return result

    def _parse_sequence(self):
        result = ("empty",) if self._peek() == "##" else self._parse_unary()
        while self._peek() == "##":
            self._take()
            delay_token = self._take()
            if not delay_token.isdecimal():
                raise SVACompileError(
                    "Only fixed nonnegative delays of the form ##N are supported"
                )
            result = ("delay", result, int(delay_token), self._parse_unary())
        return result

    def _parse_unary(self):
        if self._peek() == "!":
            self._take()
            return ("not", self._parse_unary())
        return self._parse_primary()

    def _parse_primary(self):
        if self._peek() == "(":
            self._take("(")
            result = self._parse_implication()
            self._take(")")
            return result

        value = self._take()
        if value in ("0", "1"):
            result = ("const", value == "1")
        elif re.fullmatch(r"[0-9]+'[bB][01xXzZ]+", value):
            bits = value.split("'")[1][1:].lower()
            if any(bit in "xz" for bit in bits) or len(bits) != 1:
                raise SVACompileError(
                    f"Only one-bit known Boolean literals are supported: {value}"
                )
            result = ("const", bits == "1")
        elif value.isdecimal():
            raise SVACompileError(
                f"Only Boolean 0/1 literals are supported in expressions: {value}"
            )
        elif value in ("!", "&&", "||", "##", "|->", "|=>", "==", "!=", ",", ")"):
            raise SVACompileError(f"Expected an expression, found {value!r}")
        elif value.startswith("$"):
            if value not in ("$rose", "$fell"):
                raise SVACompileError(f"Unsupported system function {value}")
            self._take("(")
            signal = self._take()
            if (
                not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", signal)
                or signal in self._unsupported_keywords
            ):
                raise SVACompileError(f"Expected a signal name in {value}(...)")
            self._take(")")
            result = (value[1:], signal)
        elif value in self._unsupported_keywords:
            raise SVACompileError(f"Unsupported SVA keyword {value!r}")
        else:
            result = ("signal", value)

        if self._peek() in ("==", "!="):
            operator = self._take()
            right = self._take()
            if right in ("0", "1"):
                rhs = ("const", right == "1")
            elif re.fullmatch(r"[0-9]+'[bB][01xXzZ]+", right):
                bits = right.split("'")[1][1:].lower()
                if any(bit in "xz" for bit in bits) or len(bits) != 1:
                    raise SVACompileError(
                        f"Only one-bit known Boolean literals are supported: {right}"
                    )
                rhs = ("const", bits == "1")
            elif (
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", right)
                and right not in self._unsupported_keywords
            ):
                rhs = ("signal", right)
            else:
                raise SVACompileError(f"Expected a Boolean signal or literal, found {right!r}")
            result = ("eq" if operator == "==" else "ne", result, rhs)
        return result


def _strip_comments(text: str) -> str:
    """Remove SystemVerilog comments while preserving comment-like string text."""
    output: list[str] = []
    index = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        if in_string:
            output.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif char == '"':
            in_string = True
            output.append(char)
            index += 1
        elif text.startswith("//", index):
            end = text.find("\n", index)
            if end < 0:
                break
            output.append("\n")
            index = end + 1
        elif text.startswith("/*", index):
            end = text.find("*/", index + 2)
            if end < 0:
                raise SVACompileError("Unterminated block comment")
            output.append(" ")
            index = end + 2
        else:
            output.append(char)
            index += 1
    if in_string:
        raise SVACompileError("Unterminated string literal")
    return "".join(output)


def _extract_assertions(text: str) -> list[str]:
    assertions: list[str] = []
    start_pattern = re.compile(r"\bassert\s+property\s*\(", re.IGNORECASE)
    searchable = list(text)
    index = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        if in_string:
            if char != "\n":
                searchable[index] = " "
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            searchable[index] = " "
            in_string = True
        index += 1
    searchable_text = "".join(searchable)
    position = 0
    while match := start_pattern.search(searchable_text, position):
        opening = text.find("(", match.start(), match.end())
        depth = 1
        index = opening + 1
        in_string = False
        escaped = False
        while index < len(text) and depth:
            char = text[index]
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
            elif char == '"':
                in_string = True
            elif char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            index += 1
        if depth:
            raise SVACompileError("Unterminated assert property expression")
        semicolon = index
        while semicolon < len(text) and text[semicolon].isspace():
            semicolon += 1
        if semicolon >= len(text) or text[semicolon] != ";":
            raise SVACompileError("Expected ';' after assert property")
        assertions.append(text[opening + 1:index - 1].strip())
        position = semicolon + 1
    if not assertions:
        raise SVACompileError("No 'assert property (...)' statements found")
    return assertions


def _strip_clocking_event(body: str) -> str:
    body = body.strip()
    if not body.startswith("@"):
        return body
    index = 1
    while index < len(body) and body[index].isspace():
        index += 1
    if index >= len(body) or body[index] != "(":
        raise SVACompileError("Clocking event must use @(posedge signal) or @(negedge signal)")
    depth = 1
    end = index + 1
    while end < len(body) and depth:
        if body[end] == "(":
            depth += 1
        elif body[end] == ")":
            depth -= 1
        end += 1
    if depth:
        raise SVACompileError("Unterminated clocking event")
    event = body[index + 1:end - 1].strip()
    if not re.fullmatch(r"(?:posedge|negedge)\s+[A-Za-z_][A-Za-z0-9_$]*", event):
        raise SVACompileError(f"Unsupported clocking event: {event!r}")
    return body[end:].strip()


def _contains_temporal_operator(node) -> bool:
    kind = node[0]
    if kind in ("delay", "|->", "|=>"):
        return True
    if kind == "not":
        return _contains_temporal_operator(node[1])
    if kind in ("and", "or", "eq", "ne"):
        return _contains_temporal_operator(node[1]) or _contains_temporal_operator(node[2])
    return False


def _contains_implication(node) -> bool:
    kind = node[0]
    if kind in ("|->", "|=>"):
        return True
    if kind == "not":
        return _contains_implication(node[1])
    if kind in ("and", "or", "eq", "ne"):
        return _contains_implication(node[1]) or _contains_implication(node[2])
    if kind == "delay":
        return _contains_implication(node[1]) or _contains_implication(node[3])
    return False


def _validate_expression(node) -> None:
    kind = node[0]
    if kind in ("not", "and", "or", "eq", "ne"):
        if _contains_temporal_operator(node[1] if kind == "not" else node):
            raise SVACompileError(
                "Boolean operators cannot contain temporal operators in this subset; "
                "parenthesize the Boolean expression as a sequence element"
            )
        if kind == "not":
            _validate_expression(node[1])
        else:
            _validate_expression(node[1])
            _validate_expression(node[2])
    elif kind == "delay":
        if _contains_implication(node):
            raise SVACompileError("Implication cannot be nested inside a delayed sequence")
        _validate_expression(node[1])
        _validate_expression(node[3])
    elif kind in ("|->", "|=>"):
        if _contains_implication(node[1]):
            raise SVACompileError("An implication cannot appear inside another implication's antecedent")
        _validate_expression(node[1])
        _validate_expression(node[2])


def _signals(node) -> set[str]:
    kind = node[0]
    if kind == "signal":
        return {node[1]}
    if kind in ("rose", "fell"):
        return {node[1]}
    if kind in ("const",):
        return set()
    if kind == "empty":
        return set()
    if kind == "not":
        return _signals(node[1])
    if kind in ("and", "or", "|->", "|=>", "eq", "ne"):
        return _signals(node[1]) | _signals(node[2])
    if kind == "delay":
        return _signals(node[1]) | _signals(node[3])
    raise SVACompileError(f"Internal error: unknown expression node {kind!r}")


def _duration(node) -> int:
    """Return a fixed sequence's end offset from its start."""
    if node[0] == "delay":
        return _duration(node[1]) + node[2] + _duration(node[3])
    return 0


def _lean_time(time: str, offset: int) -> str:
    return time if offset == 0 else f"({time} + {offset})"


def _compile_node(node, time: str, offset: int, names: dict[str, str]) -> str:
    kind = node[0]
    at = _lean_time(time, offset)
    if kind == "const":
        return "True" if node[1] else "False"
    if kind == "empty":
        return "True"
    if kind == "signal":
        return f"(trace {at}).{names[node[1]]} = true"
    if kind in ("rose", "fell"):
        current = f"(trace {at}).{names[node[1]]}"
        previous = f"(trace ({at} - 1)).{names[node[1]]}"
        before, after = (f"¬ ({previous} = true)", f"{current} = true")
        if kind == "fell":
            before, after = f"{previous} = true", f"¬ ({current} = true)"
        return f"({at} > 0) ∧ ({before}) ∧ ({after})"
    if kind == "not":
        return f"¬ ({_compile_node(node[1], time, offset, names)})"
    if kind in ("and", "or", "|->", "|=>"):
        left = _compile_node(node[1], time, offset, names)
        right_offset = offset
        if kind == "|->":
            right_offset += _duration(node[1])
        elif kind == "|=>":
            right_offset += _duration(node[1]) + 1
        right = _compile_node(node[2], time, right_offset, names)
        operator = {"and": "∧", "or": "∨", "|->": "→", "|=>": "→"}[kind]
        return f"({left}) {operator} ({right})"
    if kind in ("eq", "ne"):
        left = _compile_node(node[1], time, offset, names)
        right = _compile_node(node[2], time, offset, names)
        operator = "↔" if kind == "eq" else "≠"
        if kind == "ne":
            return f"¬ (({left}) ↔ ({right}))"
        return f"({left}) ↔ ({right})"
    if kind == "delay":
        left = _compile_node(node[1], time, offset, names)
        right_offset = offset + _duration(node[1]) + node[2]
        right = _compile_node(node[3], time, right_offset, names)
        return f"({left}) ∧ ({right})"
    raise SVACompileError(f"Internal error: unknown expression node {kind!r}")


class SVAToLeanCompilerFixed:
    def preprocess(self, sva_text: str) -> str:
        return _strip_comments(sva_text)

    def extract_signals(self, expr: str) -> set[str]:
        return _signals(ExpressionParser(expr).parse())

    def compile_expression(self, expr: str, time_offset: str = "t") -> str:
        tree = ExpressionParser(expr).parse()
        signal_names = {signal: f"sv_{index}" for index, signal in enumerate(sorted(_signals(tree)))}
        return _compile_node(tree, time_offset, 0, signal_names)

    def compile_to_lean(self, sva_code: str, module_name: str = "Hardware") -> str:
        assertions = []
        for assertion in _extract_assertions(self.preprocess(sva_code)):
            body = _strip_clocking_event(assertion)
            if body.startswith("(") and body.endswith(")"):
                # Only remove a pair if it encloses the complete expression.
                depth = 0
                closes_at_end = True
                for index, char in enumerate(body):
                    if char == "(":
                        depth += 1
                    elif char == ")":
                        depth -= 1
                        if depth == 0 and index != len(body) - 1:
                            closes_at_end = False
                            break
                if closes_at_end and depth == 0:
                    body = body[1:-1].strip()
            assertions.append(ExpressionParser(body).parse())

        all_signals = sorted(set().union(*(_signals(tree) for tree in assertions)))
        names = {signal: f"sv_{index}" for index, signal in enumerate(all_signals)}
        lines = [
            f"-- Generated Lean 4 propositions for {' '.join(str(module_name).split())}",
            "structure State where",
        ]
        lines.extend(f"  {names[signal]} : Bool" for signal in all_signals)
        if not all_signals:
            lines.append("  unit : Unit")
        lines.extend(["", "def Trace := Nat → State", ""])

        for index, tree in enumerate(assertions):
            proposition = _compile_node(tree, "t", 0, names)
            trace_parameter = "trace" if _signals(tree) else "_trace"
            time_parameter = "t" if _signals(tree) else "_t"
            lines.extend(
                [
                    f"def property_{index} ({trace_parameter} : Trace) "
                    f"({time_parameter} : Nat) : Prop :=",
                    f"  {proposition}",
                    "",
                ]
            )
        return "\n".join(lines)


if __name__ == "__main__":
    example = """
    assert property (@(posedge clk) req |=> ack);
    assert property (@(posedge clk) start |-> ##1 busy ##2 done);
    """
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    print(SVAToLeanCompilerFixed().compile_to_lean(example, "Bus"))
