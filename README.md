# SVA to Lean 4: A python based system to convert limited set of SystemVerilog assertions to Lean 4 syntax.

`sva2lean4_v2.py` translates a limited subset of concurrent SystemVerilog Assertions (SVA) into Lean 4 propositions. It is intended as a small starting point for exploring formal models of assertions — not as a complete SystemVerilog compiler or a proof that the assertions hold.

The translator uses only the Python standard library. Generated Lean models each signal as a `Bool` field in a `State` structure and represents a trace as `Nat → State`. Assertions become `Prop` definitions over that trace.

## Usage

Import the compiler and pass it one or more `assert property (...)` statements:

```python
from sva2lean4_v2 import SVAToLeanCompilerFixed

sva = """
assert property (@(posedge clk) req |=> ack);
assert property (@(posedge clk) start |-> ##1 busy ##2 done);
"""

lean_source = SVAToLeanCompilerFixed().compile_to_lean(sva, module_name="Bus")
with open("Bus.lean", "w", encoding="utf-8") as lean_file:
    lean_file.write(lean_source)
```

With Python and Lean 4 installed, type-check the generated file with:

```sh
lean Bus.lean
```

Running the script directly prints Lean output for the built-in example:

```sh
python sva2lean4_v2.py
```

The compiler also provides `compile_expression(expr, time_offset="t")` for translating a supported expression and `extract_signals(expr)` for retrieving its signal names.

## Supported syntax

The current subset includes:

- `assert property (...)`, optionally prefixed by one `@(posedge signal)` or `@(negedge signal)` event
- Boolean signals and known one-bit constants (`0`, `1`, `1'b0`, `1'b1`)
- `!`, `&&`, `||`, `==`, and `!=`
- `$rose(signal)` and `$fell(signal)`
- Fixed delays `##N` and implications `|->` and `|=>`

Unsupported or malformed syntax raises `SVACompileError` rather than being intentionally approximated.

## Limitations

See [sva_to_lean_shortcomings.md](sva_to_lean_shortcomings.md) for unsupported constructs, modeling assumptions, and semantic limitations.

