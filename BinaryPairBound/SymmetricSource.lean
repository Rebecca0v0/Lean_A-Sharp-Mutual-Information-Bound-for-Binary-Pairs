module

public import BinaryPairBound.Endpoints
public import BinaryPairBound.Symmetry
public import BinaryPairBound.ChannelCap
public import BinaryPairBound.LocalCoefficient
public import BinaryPairBound.Merging

/-!
# Exact contraction coefficient and sharp attainment for symmetric sources

The coefficient calculation compares the actual distribution-dependent
supremum with its local curvature lower bound and its channel-wide upper
bound. It does not replace `S` by a separately defined coefficient.
-/

noncomputable section

@[expose] public section

namespace BinaryPairBound

lemma q_half_symmetric (c : ℝ) : q c c (1 / 2) = 1 / 2 := by
  unfold q k
  ring

lemma rhoSquared_half_symmetric (c : ℝ) :
    rhoSquared c c (1 / 2) = (1 - 2 * c) ^ 2 := by
  rw [rhoSquared, q_half_symmetric]
  unfold k
  norm_num
  ring

/-- The exact distribution-dependent coefficient of every doubly symmetric source. -/
theorem S_symmetric {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    S (1 / 2) c c = (1 - 2 * c) ^ 2 := by
  by_cases hc0 : c = 0
  · subst c
    simpa using S_noiseless (s := 1 / 2) (by norm_num)
  by_cases hc1 : c = 1
  · subst c
    have hflip := S_output_flip (1 / 2) 0 0
    have hz := S_noiseless (s := 1 / 2) (by norm_num)
    norm_num at hflip ⊢
    exact hflip.trans hz
  have hci : c ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1⟩
  have hv : Valid (1 / 2) c c := ⟨by norm_num, hc, hc⟩
  have hn : Nondegenerate (1 / 2) c c := by
    rw [Nondegenerate, q_half_symmetric]
    norm_num
  apply le_antisymm
  · simpa only [eta_symmetric hc] using S_le_eta (s := 1 / 2) (by norm_num) hci hci
  · simpa only [rhoSquared_half_symmetric] using rhoSquared_le_S hv hn

/-- Sufficiency of the DSBS equality case in Theorem 2.1. -/
theorem sharp_equality_of_dsbs {s c d : ℝ} (hv : Valid s c d) (hdsbs : DSBS s c d) :
    J s c d = phi (S s c d) := by
  rcases hdsbs with ⟨hs, hcd⟩
  subst s
  subst d
  rw [S_symmetric hv.2.1, ← eta_symmetric hv.2.1]
  exact J_half_symmetric_eq_phi_eta hv.2.1

/-- Both families asserted as equality cases by the paper do attain the bound.
The converse classification for arbitrary pairs remains a separate task. -/
theorem sharp_equality_of_independent_or_dsbs {s c d : ℝ} (hv : Valid s c d)
    (heq : Independent s c d ∨ DSBS s c d) : J s c d = phi (S s c d) := by
  rcases heq with hi | hd
  · exact sharp_equality_of_independent hi
  · exact sharp_equality_of_dsbs hv hd

/-- Crossover parameter used to attain a prescribed contraction cap. -/
def symmetricCrossover (lam : ℝ) : ℝ := (1 - Real.sqrt lam) / 2

lemma symmetricCrossover_mem_Icc {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    symmetricCrossover lam ∈ Set.Icc (0 : ℝ) 1 := by
  have hs0 := Real.sqrt_nonneg lam
  have hs1 : Real.sqrt lam ≤ 1 := (Real.sqrt_le_one).mpr hlam.2
  unfold symmetricCrossover
  constructor <;> linarith

lemma symmetricCrossover_mem_Ioo {lam : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    symmetricCrossover lam ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs0 := Real.sqrt_pos.mpr hlam.1
  have hs1 : Real.sqrt lam < 1 := (sqrt_mem_Ioo hlam).2
  unfold symmetricCrossover
  constructor <;> linarith

/-- The symmetric witness has exactly the prescribed coefficient, including endpoints. -/
theorem S_symmetricCrossover {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    S (1 / 2) (symmetricCrossover lam) (symmetricCrossover lam) = lam := by
  rw [S_symmetric (symmetricCrossover_mem_Icc hlam)]
  rw [show 1 - 2 * symmetricCrossover lam = Real.sqrt lam by unfold symmetricCrossover; ring]
  exact Real.sq_sqrt hlam.1

theorem J_symmetricCrossover (lam : ℝ) :
    J (1 / 2) (symmetricCrossover lam) (symmetricCrossover lam) = phi lam := by
  rw [J_symmetric]
  rfl

/-- The cap-constrained optimization problem has a sharp-value feasible witness. -/
theorem exists_sharp_cap_witness {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    ∃ s c d : ℝ, Valid s c d ∧ S s c d = lam ∧ J s c d = phi lam := by
  have hc := symmetricCrossover_mem_Icc hlam
  exact ⟨1 / 2, symmetricCrossover lam, symmetricCrossover lam,
    ⟨by norm_num, hc, hc⟩, S_symmetricCrossover hlam, J_symmetricCrossover lam⟩

end BinaryPairBound
