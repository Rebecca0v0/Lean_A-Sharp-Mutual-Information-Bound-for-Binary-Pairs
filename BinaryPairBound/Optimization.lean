module

public import BinaryPairBound.Compactness
public import BinaryPairBound.SymmetricSource

/-! # Fixed-cap maximizers: existence and nondegeneracy (Section 3) -/

@[expose] public section

namespace BinaryPairBound

/-- A maximizer over the entire cube of valid binary parameters at a fixed cap. -/
def IsCapMaximizer (lam s c d : ℝ) : Prop :=
  Valid s c d ∧ S s c d ≤ lam ∧
    ∀ s' c' d' : ℝ, Valid s' c' d' → S s' c' d' ≤ lam → J s' c' d' ≤ J s c d

theorem exists_normalized_maximizer {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ s c d : ℝ, IsCapMaximizer lam s c d ∧ c + d ≤ 1 := by
  obtain ⟨s, c, d, hv, hcd, hS, hmax⟩ := exists_normalized_cap_maximizer hlam
  exact ⟨s, c, d, ⟨hv, hS, hmax⟩, hcd⟩

theorem phi_le_J_of_cap_maximizer {lam s c d : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hm : IsCapMaximizer lam s c d) : phi lam ≤ J s c d := by
  obtain ⟨s', c', d', hv', hS', hJ'⟩ := exists_sharp_cap_witness hlam
  have h := hm.2.2 s' c' d' hv' (by rw [hS'])
  simpa only [hJ'] using h

theorem cap_maximizer_J_pos {lam s c d : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1)
    (hm : IsCapMaximizer lam s c d) : 0 < J s c d :=
  (phi_pos hlam).trans_le (phi_le_J_of_cap_maximizer ⟨hlam.1.le, hlam.2⟩ hm)

theorem cap_maximizer_nondegenerate {lam s c d : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1)
    (hm : IsCapMaximizer lam s c d) : Nondegenerate s c d := by
  apply nondegenerate_of_not_independent hm.1
  intro hi
  have hpos := cap_maximizer_J_pos hlam hm
  rw [J_eq_zero_of_independent hi] at hpos
  exact (lt_irrefl 0) hpos

theorem normalized_cap_maximizer_slope_pos {lam s c d : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (hm : IsCapMaximizer lam s c d)
    (hcd : c + d ≤ 1) : 0 < k c d := by
  have hne : c + d ≠ 1 := by
    intro heq
    have hpos := cap_maximizer_J_pos hlam hm
    rw [J_eq_zero_of_independent (Or.inr (Or.inr heq))] at hpos
    exact (lt_irrefl 0) hpos
  unfold k
  have hlt := lt_of_le_of_ne hcd hne
  linarith

theorem cap_maximizer_not_noiseless {lam s c d : ℝ}
    (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hm : IsCapMaximizer lam s c d) :
    ¬(c = 0 ∧ d = 0) := by
  rintro ⟨rfl, rfl⟩
  have hn := cap_maximizer_nondegenerate ⟨hlam.1, hlam.2.le⟩ hm
  have hS := hm.2.1
  rw [S_noiseless hn.1] at hS
  linarith [hlam.2]

/-- The existence and nondegeneracy conclusions of Lemma 3.1.
Interior channel transitions and cap saturation are not yet asserted. -/
theorem exists_nontrivial_normalized_maximizer {lam : ℝ}
    (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ s c d : ℝ, IsCapMaximizer lam s c d ∧ Nondegenerate s c d ∧
      0 < k c d ∧ phi lam ≤ J s c d := by
  obtain ⟨s, c, d, hm, hcd⟩ := exists_normalized_maximizer hlam.1.le
  exact ⟨s, c, d, hm, cap_maximizer_nondegenerate ⟨hlam.1, hlam.2.le⟩ hm,
    normalized_cap_maximizer_slope_pos ⟨hlam.1, hlam.2.le⟩ hm hcd,
    phi_le_J_of_cap_maximizer ⟨hlam.1.le, hlam.2.le⟩ hm⟩

end BinaryPairBound
