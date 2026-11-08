# Limitations of `sva2lean4_v2.py`

`sva2lean4_v2.py` is a small tokenizer and recursive-descent parser for a deliberately restricted subset of concurrent SVA. It builds a simple expression tree; it is **not** a complete SystemVerilog parser, and it does not prove that an assertion holds. Unsupported syntax is intended to raise `SVACompileError` rather than be translated approximately.

## Supported subset and model

The script extracts `assert property (...)` statements and translates Boolean signals and constants, `!`, `&&`, `||`, `==`, `!=`, `$rose(signal)`, `$fell(signal)`, fixed `##N` delays, and `|->` / `|=>` implications. It accepts an optional single `@(posedge signal)` or `@(negedge signal)` event. Signals are modeled as `Bool` fields in a Lean `State`, and `Trace` is `Nat → State`.

The generated declarations are Lean `def`s with type `Prop`; they describe translated properties but do not establish their validity. Every signal is treated as a two-state Boolean. The clocking event is syntax-checked and then discarded, so the model assumes the trace index already represents sampling ticks for the property.

## Unsupported SVA constructs

1. **Unbounded delays and repetition** (`##[m:n]`, `##[1:$]`, `[*]`, `[+]`, `[=n]`, `[->n]`): only fixed nonnegative `##N` delays are supported. Ranged delays and repetition operators are rejected; there is no generated quantification or inductive sequence matcher.
2. **Concurrent sequence operators** (`and`, `intersect`, `within`, `throughout`, and related forms): these express sequence-match relationships that a single fixed-offset conjunction cannot represent. They are rejected rather than approximated.
3. **Local variables and assignments**: property-local declarations, sampled assignments such as `(data, v = data_in)`, and later references to `v` are not modeled. The parser supports only named Boolean signals, not typed values such as `BitVec 32`.
4. **Multiple clocks and sampling semantics**: only one simple edge event is accepted per assertion, and its clock name and edge are not represented in `Trace`. Multiple clock domains, clocking blocks, event controls, sampling regions, and synchronization relationships are unsupported.
5. **General SystemVerilog expressions and declarations**: arithmetic, relational operators, bit/vector operations, concatenation, indexing, hierarchy, macros, `disable iff`, property/sequence declarations, and most system functions are outside the grammar. Only known one-bit Boolean literals (`0`, `1`, `1'b0`, `1'b1`) are supported; X/Z and wider values are rejected.

## Semantic scope

Fixed-delay sequences are translated to predicates over the trace at calculated offsets. The parser rejects Boolean operators mixed with temporal operators in ambiguous positions, but the supported subset still does not model all SVA details, including four-state logic, sampled-value regions, vacuity/reporting behavior, or assertion action blocks. A successful translation therefore means only that the input matched this limited grammar and produced Lean syntax—not that the model captures the complete semantics of the original SystemVerilog property.
