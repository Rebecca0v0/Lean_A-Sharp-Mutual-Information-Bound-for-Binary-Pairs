module

public import BinaryPairBound.Specification
public import BinaryPairBound.Endpoints
public import BinaryPairBound.Symmetry

/-!
# Reduction of the sharp bound to normalized, nonendpoint coefficients

This proves an equivalence of targets, not the remaining normalized bound.
The optimization and contact-geometry arguments in Sections 3–6 and 9 are
still required to produce a proof of `NormalizedSharpBound`.
-/

@[expose] public section

namespace BinaryPairBound

/-- The still-open core bound after endpoint cases and output relabeling. -/
def NormalizedSharpBound : Prop :=
  ∀ s c d : ℝ, Valid s c d → 0 < k c d → S s c d ∈ Set.Ioo (0 : ℝ) 1 →
    J s c d ≤ phi (S s c d)

/-- All deterministic, independent, cap-endpoint, and negative-slope cases
reduce to the positive-slope, nonendpoint problem. This is not a proof of
the remaining premise. -/
theorem sharpBound_of_normalized (hcore : NormalizedSharpBound) : SharpBound := by
  intro s c d hv
  by_cases hS0 : S s c d = 0
  · exact (sharp_equality_of_S_zero hv hS0).1.le
  by_cases hS1 : S s c d = 1
  · exact sharp_bound_of_S_one hv hS1
  have hS : S s c d ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (S_nonneg hv) (Ne.symm hS0), lt_of_le_of_ne (S_le_one hv) hS1⟩
  rcases lt_trichotomy (k c d) 0 with hk | hk | hk
  · have hflip : 0 < k (1 - c) (1 - d) := by rw [k_output_flip]; linarith
    have h := hcore s (1 - c) (1 - d) (valid_output_flip hv) hflip
      (by simpa only [S_output_flip] using hS)
    simpa only [J_output_flip, S_output_flip] using h
  · have hi : Independent s c d := Or.inr (Or.inr (by unfold k at hk; linarith))
    exact (hS0 (S_eq_zero_of_independent hi)).elim
  · exact hcore s c d hv hk hS

theorem sharpBound_iff_normalized : SharpBound ↔ NormalizedSharpBound := by
  constructor
  · intro h s c d hv _ _
    exact h s c d hv
  · exact sharpBound_of_normalized

end BinaryPairBound
