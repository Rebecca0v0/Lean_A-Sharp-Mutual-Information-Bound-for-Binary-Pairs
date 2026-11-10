module

public import BinaryPairBound.Definitions

/-!
# Unproved targets

These are definitions of propositions, not proofs or axioms. Compiling this
file checks that the specifications are well-formed; it does NOT prove
Theorem 2.1. See `blueprint.md` for the remaining proof obligations.
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

/-- The initial project goal. This proposition has not yet been proved. -/
def MainTheorem : Prop := SharpBound ∧ EqualityClassification

end BinaryPairBound
