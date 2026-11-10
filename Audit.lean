module

import BinaryPairBound

-- Guard the axiom output, so unexpected assumptions make this audit fail.
-- These are the standard foundations used by mathlib, not paper-specific assumptions.

/-- info: 'BinaryPairBound.D_eq_log_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.D_eq_log_ratio

/-- info: 'BinaryPairBound.hasDerivAt_entropyCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.hasDerivAt_entropyCurve

/-- info: 'BinaryPairBound.equation_4_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.equation_4_1

/-- info: 'BinaryPairBound.equation_4_1_log_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BinaryPairBound.equation_4_1_log_ratio

-- Also show the final theorem's audit in the command output.
#print axioms BinaryPairBound.equation_4_1_log_ratio

-- These are proposition definitions, deliberately not proofs of Theorem 2.1.
#check BinaryPairBound.SharpBound
#check BinaryPairBound.EqualityClassification
