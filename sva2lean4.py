import re

class SVAToLeanCompilerFixed:
    def __init__(self):
        self.clean_regex = re.compile(r'(//.*)|(/\*[\s\S]*?\*/)')

    def preprocess(self, sva_text: str) -> str:
        text_no_comments = self.clean_regex.sub('', sva_text)
        return " ".join(text_no_comments.split())

    def extract_signals(self, expr: str) -> set:
        # Isolate tokens while ignoring SVA keywords, operators, and timing hooks
        tokens = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', expr)
        ignored = {
            'assert', 'property', 'posedge', 'clk', 'and', 'or', 'not', 
            'intersect', 'within', 'throughout', 'if', 'else', 'True', 'False'
        }
        return {t for t in tokens if t not in ignored and not t.startswith('$')}

    def compile_expression(self, expr: str, time_offset: str = "t") -> str:
        """
        Recursively converts SVA operators to Lean 4.
        Keeps time tracking mathematical (e.g. "t + 1") instead of nesting trace calls.
        """
        expr = expr.strip()

        # Handle explicit outer parenthesis matching to avoid stripping structure mid-tree
        if expr.startswith('(') and expr.endswith(')'):
            # Simple check to see if outer parentheses are matching pairs
            if expr.count('(') == expr.count(')'):
                inner = expr[1:-1].strip()
                return f"({self.compile_expression(inner, time_offset)})"

        # 1. Non-Overlapping Implication (|=>) -> P t → Q (t + 1)
        if '|=>' in expr:
            left, right = [x.strip() for x in expr.split('|=>', 1)]
            return f"{self.compile_expression(left, time_offset)} → {self.compile_expression(right, f'({time_offset} + 1)')}"

        # 2. Overlapping Implication (|->) -> P t → Q t
        if '|->' in expr:
            left, right = [x.strip() for x in expr.split('|->', 1)]
            return f"{self.compile_expression(left, time_offset)} → {self.compile_expression(right, time_offset)}"

        # 3. Static Temporal Delays (##n)
        # Fix: Parse from left to right for sequential delays
        static_delay_match = re.search(r'##(\d+)\s*(.*)', expr)
        if static_delay_match:
            delay = int(static_delay_match.group(1))
            right = static_delay_match.group(2).strip()
            # If there's a left-hand side before the delay token
            left_part = expr.split(f"##{delay}", 1)[0].strip()
            
            new_time = f"({time_offset} + {delay})"
            compiled_right = self.compile_expression(right, new_time)
            
            if left_part:
                compiled_left = self.compile_expression(left_part, time_offset)
                return f"{compiled_left} ∧ {compiled_right}"
            return compiled_right

        # 4. Handle System Functions ($rose) cleanly before structural variable processing
        rose_match = re.search(r'\$rose\s*\(\s*([a-zA-Z0-9_]+)\s*\)', expr)
        if rose_match:
            var = rose_match.group(1).strip()
            rose_lean = f"(if {time_offset} = 0 then False else ¬ (trace ({time_offset} - 1)).{var}) ∧ (trace {time_offset}).{var}"
            # Replace the literal match with a safe token identifier to avoid double processing
            expr = expr.replace(rose_match.group(0), f"__ROSE_PLACEHOLDER_{var}__")

        # 5. Translate common Verilog operators to safe mathematical Lean symbols
        expr = expr.replace('&&', '∧').replace('||', '∨').replace('!', '¬ ')

        # 6. Apply trace projections to raw signals, leaving placeholders and constants intact
        signals = self.extract_signals(expr)
        for sig in signals:
            expr = re.sub(rf'\b{sig}\b', f"(trace {time_offset}).{sig}", expr)

        # Restore Rose definitions without corrupting the trace structures
        if rose_match:
            expr = expr.replace(f"__ROSE_PLACEHOLDER_{var}__", rose_lean)

        return expr

    def compile_to_lean(self, sva_code: str, module_name: str = "Hardware") -> str:
        normalized = self.preprocess(sva_code)
        statements = [s.strip() + ";" for s in normalized.split(';') if s.strip()]
        
        all_signals = set()
        assertions = []
        for stmt in statements:
            if "assert" in stmt:
                assertions.append(stmt)
                all_signals.update(self.extract_signals(stmt))
                
        lean_output = [
            f"-- Generated Lean 4 formal environment for {module_name}",
            "structure State where"
        ]
        for signal in sorted(all_signals):
            lean_output.append(f"  {signal} : Bool")
        
        lean_output.extend([
            "",
            "def Trace := Nat → State",
            ""
        ])

        for idx, assert_stmt in enumerate(assertions):
            body_match = re.search(r'assert\s+property\s*\(\s*(?:@\s*\([^)]+\))?\s*(.*?)\s*\)\s*;', assert_stmt)
            body = body_match.group(1).strip() if body_match else assert_stmt.replace('assert', '').strip().rstrip(';')
            
            compiled_body = self.compile_expression(body, "t")
            theorem_name = f"property_proof_{idx}"
            lean_output.extend([
                f"/-- SVA Source: {assert_stmt} --/",
                f"theorem {theorem_name} (trace : Trace) (t : Nat) :",
                f"  {compiled_body} := by",
                "    sorry",
                ""
            ])
            
        return "\n".join(lean_output)

# --- Verification & Execution ---
if __name__ == "__main__":
    sva_input = """
    assert property (@(posedge clk) req |=> ack);
    assert property (@(posedge clk) start |-> ##1 busy ##2 done);
    """
    compiler = SVAToLeanCompilerFixed()
    print(compiler.compile_to_lean(sva_input, "BusFix"))

