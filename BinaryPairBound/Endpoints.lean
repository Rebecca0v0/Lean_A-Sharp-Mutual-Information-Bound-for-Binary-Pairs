module

public import BinaryPairBound.Contraction
public import BinaryPairBound.Information
public import BinaryPairBound.ScalarEntropy

/-! # Endpoint contraction coefficients (Section 8) -/

public section

namespace BinaryPairBound

theorem S_eq_zero_iff_independent {s c d : ℝ} (hv : Valid s c d) :
    S s c d = 0 ↔ Independent s c d := by
  constructor
  · intro hS
    by_contra hi
    have hn := nondegenerate_of_not_independent hv hi
    have hcap := klCap_S hv hn 0 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    have hq0 : q c d 0 = c := by simp [q]
    rw [hS, zero_mul, hq0] at hcap
    have hD : D c (q c d s) = 0 := le_antisymm hcap (D_nonneg hv.2.1 hn.2)
    have heq := (D_eq_zero_iff hv.2.1 hn.2).mp hD
    have hmul : k c d * s = 0 := by unfold q at heq; linarith
    have hk : k c d = 0 := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hn.1.1)
    exact hi (Or.inr (Or.inr (by unfold k at hk; linarith)))
  · exact S_eq_zero_of_independent

theorem S_pos_iff_not_independent {s c d : ℝ} (hv : Valid s c d) :
    0 < S s c d ↔ ¬Independent s c d := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hn⟩ hi
    exact hn (S_eq_zero_of_independent hi).symm
  · intro hi
    exact ⟨S_nonneg hv, fun h => hi ((S_eq_zero_iff_independent hv).mp h.symm)⟩

theorem sharp_equality_of_independent {s c d : ℝ} (hi : Independent s c d) :
    J s c d = phi (S s c d) := by
  rw [J_eq_zero_of_independent hi, S_eq_zero_of_independent hi, phi_zero]

/-- Theorem 2.1, including equality, at contraction coefficient zero. -/
theorem sharp_equality_of_S_zero {s c d : ℝ} (hv : Valid s c d) (hS : S s c d = 0) :
    J s c d = phi (S s c d) ∧ Independent s c d := by
  have hi := (S_eq_zero_iff_independent hv).mp hS
  exact ⟨sharp_equality_of_independent hi, hi⟩

/-- Theorem 2.1 at contraction coefficient one. -/
theorem sharp_bound_of_S_one {s c d : ℝ} (hv : Valid s c d) (hS : S s c d = 1) :
    J s c d ≤ phi (S s c d) := by
  rw [hS, phi_one]
  exact J_le_log_two hv

/-- At coefficient one, equality forces the uniform noiseless/complementing source. -/
theorem sharp_equality_iff_of_S_one {s c d : ℝ} (hv : Valid s c d) (hS : S s c d = 1) :
    J s c d = phi (S s c d) ↔ s = 1 / 2 ∧ c = d ∧ (c = 0 ∨ c = 1) := by
  rw [hS, phi_one]
  exact J_eq_log_two_iff hv

theorem S_noiseless {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) : S s 0 0 = 1 := by
  have hv : Valid s 0 0 := ⟨⟨hs.1.le, hs.2.le⟩, by simp, by simp⟩
  have hn : Nondegenerate s 0 0 := by simpa [Nondegenerate, q, k] using And.intro hs hs
  have hD : D 0 s ≠ 0 := ne_of_gt (D_pos (by simp) hs (ne_of_lt hs.1))
  apply le_antisymm (S_le_one hv)
  have h := ratio_le_S hv hn (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (ne_of_lt hs.1)
  simpa [q, k, hD] using h

theorem J_symmetric (c : ℝ) : J (1 / 2) c c = Real.log 2 - H c := by
  have hq : q c c (1 / 2) = 1 / 2 := by unfold q k; ring
  have hH : H (1 / 2) = Real.log 2 := Real.binEntropy_eq_log_two.mpr (by norm_num)
  rw [J, hq, hH]
  ring

end BinaryPairBound
