module

public import BinaryPairBound.Merging
public import BinaryPairBound.LocalCoefficient

/-!
# The sharp bound at the merging configuration

These statements use the exact distribution-dependent coefficient `S`, not
just the channel-wide expression `eta`. They cover the distinguished input
and do not assert that every cap-constrained maximizer has this form.
-/

public section

namespace BinaryPairBound

/-- Proposition 7.2, with the exact coefficient at the distinguished input. -/
theorem merging_sharp_bound {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d < 1) :
    J (distinguishedInput c d) c d ≤ phi (S (distinguishedInput c d) c d) := by
  rw [S_distinguishedInput_eq_eta hc hd (ne_of_lt hcd)]
  exact J_le_phi_eta (distinguishedInput_mem_Ioo hc hd) hc hd hcd

/-- The full DSBS equality characterization at the merging configuration. -/
theorem merging_sharp_eq_iff_dsbs {c d : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hd : d ∈ Set.Ioo (0 : ℝ) 1) (hcd : c + d < 1) :
    J (distinguishedInput c d) c d = phi (S (distinguishedInput c d) c d) ↔
      DSBS (distinguishedInput c d) c d := by
  rw [S_distinguishedInput_eq_eta hc hd (ne_of_lt hcd)]
  exact merging_eq_iff_dsbs (distinguishedInput_mem_Ioo hc hd) hc hd hcd rfl

end BinaryPairBound
