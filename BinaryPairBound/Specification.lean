module

public import BinaryPairBound.Definitions

/-!
# Theorem specifications

These are definitions of propositions, not axioms. Their unconditional
proof is `BinaryPairBound.mainTheorem` in `MainProof.lean`. Compiling this
specification file alone only checks that the statements are well-formed.
-/

@[expose] public section

namespace BinaryPairBound

/-- The inequality in Theorem 2.1, for all binary channel parameters. -/
def SharpBound : Prop :=
  ∀ s c d : ℝ, Valid s c d → J s c d ≤ phi (S s c d)

/-- The complete equality statement, including degenerate inputs and relabelings. -/
def EqualityClassification : Prop :=
  ∀ s c d : ℝ, Valid s c d →
    (J s c d = phi (S s c d) ↔ Independent s c d ∨ DSBS s c d)

/-- The inequality and complete equality statement of Theorem 2.1. -/
def MainTheorem : Prop := SharpBound ∧ EqualityClassification

end BinaryPairBound
