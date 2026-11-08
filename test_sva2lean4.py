import unittest

from sva2lean4_v2 import SVACompileError, SVAToLeanCompilerFixed


class SVAToLeanCompilerTests(unittest.TestCase):
    def setUp(self):
        self.compiler = SVAToLeanCompilerFixed()

    def test_non_overlapping_implication_emits_prop(self):
        output = self.compiler.compile_to_lean(
            "assert property (@(posedge clk) req |=> ack);"
        )
        self.assertIn("(trace t).sv_1 = true", output)
        self.assertIn("(trace (t + 1)).sv_0 = true", output)
        self.assertIn("def property_0 (trace : Trace) (t : Nat) : Prop :=", output)
        self.assertNotIn("sorry", output)
        self.assertNotIn("clk :", output)

    def test_sequential_delays_accumulate_and_preserve_precedence(self):
        output = self.compiler.compile_to_lean(
            "assert property (@(posedge clk) start |-> ##1 busy ##2 done);"
        )
        self.assertIn("(trace (t + 1)).sv_0 = true", output)
        self.assertIn("(trace (t + 3)).sv_1 = true", output)

    def test_rose_and_comment_handling(self):
        output = self.compiler.compile_to_lean(
            "assert property (@(posedge clk) $rose(req)); // ##[1:$]\n"
        )
        self.assertIn("(trace t).sv_0 = true", output)
        self.assertIn("(trace (t - 1)).sv_0", output)
        self.assertIn("(t > 0)", output)

    def test_boolean_precedence_and_no_signal_case(self):
        output = self.compiler.compile_to_lean(
            "assert property (@(posedge clk) a || b && c);"
        )
        self.assertIn(
            "((trace t).sv_0 = true) ∨ (((trace t).sv_1 = true) ∧ "
            "((trace t).sv_2 = true))",
            output,
        )

        constant_output = self.compiler.compile_to_lean("assert property (1'b1);")
        self.assertIn("  unit : Unit", constant_output)
        self.assertIn("(_trace : Trace) (_t : Nat)", constant_output)
        self.assertIn("  True", constant_output)

    def test_zero_delay_and_implication_after_sequence_end(self):
        output = self.compiler.compile_to_lean(
            "assert property (a ##0 b |=> c); "
            "assert property (a ##2 b |-> c ##1 d);"
        )
        self.assertIn("property_1", output)
        self.assertIn("(trace t).sv_0 = true", output)
        self.assertIn("(trace t).sv_1 = true", output)
        self.assertIn("(trace (t + 1)).sv_2 = true", output)
        self.assertIn("(trace (t + 2)).sv_1 = true", output)
        self.assertIn("(trace (t + 2)).sv_2 = true", output)
        self.assertIn("(trace (t + 3)).sv_3 = true", output)

    def test_parenthesized_boolean_sequence_atom_and_temporal_mixtures(self):
        output = self.compiler.compile_to_lean(
            "assert property ((a && b) ##1 c);"
        )
        self.assertIn("(trace (t + 1)).sv_2 = true", output)
        for expression in (
            "a && b ##1 c",
            "a ##1 b && c",
            "!(a ##1 b)",
            "a ##1 (b |-> c)",
            "a == always",
            "$rose(always)",
        ):
            with self.subTest(expression=expression):
                with self.assertRaises(SVACompileError):
                    self.compiler.compile_to_lean(
                        f"assert property ({expression});"
                    )

    def test_fell_equality_negedge_and_string_literals(self):
        output = self.compiler.compile_to_lean(
            'string ignored = "assert property (fake);"; '
            "assert property (@(negedge clk) $fell(req) && (req != ack));"
        )
        self.assertNotIn("fake", output)
        self.assertNotIn("clk :", output)
        self.assertIn("(t > 0)", output)
        self.assertIn("¬", output)
        self.assertIn("↔", output)
        self.assertEqual(output.count("def property_"), 1)

    def test_rejects_unbounded_delay_instead_of_approximating(self):
        with self.assertRaises(SVACompileError):
            self.compiler.compile_to_lean(
                "assert property (@(posedge clk) req ##[1:$] ack);"
            )
        with self.assertRaises(SVACompileError):
            self.compiler.compile_to_lean("assert property (req intersect ack);")
        for expression in ("$past(req)", "4'b0010", "always"):
            with self.subTest(expression=expression):
                with self.assertRaises(SVACompileError):
                    self.compiler.compile_to_lean(
                        f"assert property ({expression});"
                    )

    def test_rejects_unsupported_clocking_and_non_assert_input(self):
        with self.assertRaises(SVACompileError):
            self.compiler.compile_to_lean(
                "assert property (@(posedge a or posedge b) req);"
            )
        with self.assertRaises(SVACompileError):
            self.compiler.compile_to_lean("property p;")
        for source in (
            "assert property (req)",
            "assert property (req && );",
            "assert property (req;",
        ):
            with self.subTest(source=source):
                with self.assertRaises(SVACompileError):
                    self.compiler.compile_to_lean(source)


if __name__ == "__main__":
    unittest.main()
