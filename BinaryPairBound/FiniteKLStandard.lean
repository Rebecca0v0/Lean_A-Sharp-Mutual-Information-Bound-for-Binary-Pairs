module

public import BinaryPairBound.FiniteKL

/-! # The standard KL coefficient with the unchanged input excluded

Alternative input laws may have zero masses, but must be supported on the
reference law. The standard coefficient below excludes `r = p` and explicitly
takes value zero when there is no such alternative. It equals the existing
density-based coefficient, without changing any previous definition.
-/

noncomputable section
@[expose] public section
open scoped BigOperators
namespace BinaryPairBound.FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Gibbs' equality case on finite laws, including zero-probability atoms. -/
theorem relativeEntropy_eq_zero_iff {r p : Law α} (h : Supported r p) :
    relativeEntropy r p = 0 ↔ r = p := by
  constructor
  · intro he
    have hm := sum_mass_mul_density h
    have hj := Real.strictConvexOn_mul_log.map_sum_eq_iff'
      (t := Finset.univ) (w := p.mass) (p := density r p)
      (fun a _ => p.nonneg a) p.total (fun a _ => density_nonneg r p a)
    simp only [smul_eq_mul] at hj
    have hsum : (∑ a, p.mass a * (density r p a * Real.log (density r p a))) = 0 := by
      rw [relativeEntropy_eq_entropy h] at he
      simpa only [entropy, hm, Real.log_one, mul_zero, sub_zero, mul_assoc] using he
    have hd : ∀ a, p.mass a ≠ 0 → density r p a = 1 := by
      have heq : (∑ a, p.mass a * density r p a) *
          Real.log (∑ a, p.mass a * density r p a) =
          ∑ a, p.mass a * (density r p a * Real.log (density r p a)) := by
        rw [hm, hsum, Real.log_one, mul_zero]
      intro a ha
      simpa only [hm] using hj.mp heq a (Finset.mem_univ a) ha
    have hmass : r.mass = p.mass := by
      funext a
      by_cases hp : p.mass a = 0
      · rw [hp, h a hp]
      · have he := mass_mul_density h a
        rw [hd a hp, mul_one] at he
        exact he.symm
    cases r
    cases p
    cases hmass
    rfl
  · rintro rfl
    simp

/-- The denominator in every supported, nontrivial KL test is strictly positive. -/
theorem relativeEntropy_pos_iff {r p : Law α} (h : Supported r p) :
    0 < relativeEntropy r p ↔ r ≠ p := by
  rw [lt_iff_le_and_ne]
  simp only [relativeEntropy_nonneg h, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    relativeEntropy_eq_zero_iff h]

/-- The standard supported KL ratios, excluding the unchanged input law. -/
def standardKLRatios (p : Law α) (K : Channel α β) : Set ℝ :=
  {v | ∃ r : Law α, Supported r p ∧ r ≠ p ∧
    v = relativeEntropy (out r K) (out p K) / relativeEntropy r p}

/-- The standard KL contraction coefficient, with an explicit zero convention
when no supported alternative input law exists. -/
def standardKLCoefficient (p : Law α) (K : Channel α β) : ℝ := by
  classical
  exact if (standardKLRatios p K).Nonempty then sSup (standardKLRatios p K) else 0

/-- The finite-KL domain is expressed by `Supported`; within that domain the
usual positive-denominator condition is exactly the exclusion of `Q = P`. -/
theorem standardKLRatios_eq_positive (p : Law α) (K : Channel α β) :
    standardKLRatios p K =
      {v | ∃ r : Law α, Supported r p ∧ 0 < relativeEntropy r p ∧
        v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  ext v
  constructor
  · rintro ⟨r, hr, hne, hv⟩
    exact ⟨r, hr, (relativeEntropy_pos_iff hr).mpr hne, hv⟩
  · rintro ⟨r, hr, hpos, hv⟩
    exact ⟨r, hr, (relativeEntropy_pos_iff hr).mp hpos, hv⟩

theorem standardKLRatios_subset (p : Law α) (K : Channel α β) :
    standardKLRatios p K ⊆ probabilityRatios p K := by
  rintro v ⟨r, hr, _, hv⟩
  exact ⟨r, hr, hv⟩

theorem standardKLRatios_bddAbove (p : Law α) (K : Channel α β) :
    BddAbove (standardKLRatios p K) := by
  have h : BddAbove (probabilityRatios p K) := by
    rw [← ratios_eq_probabilityRatios]
    exact ratios_bddAbove p K
  exact h.mono (standardKLRatios_subset p K)

theorem standardKLRatios_nonneg {p : Law α} {K : Channel α β} {v : ℝ}
    (hv : v ∈ standardKLRatios p K) : 0 ≤ v := by
  rcases hv with ⟨r, hr, _, rfl⟩
  exact div_nonneg (relativeEntropy_nonneg (supported_out hr K))
    (relativeEntropy_nonneg hr)

/-- Keeping the unchanged input adds exactly the single value zero. -/
theorem probabilityRatios_eq_insert_standard (p : Law α) (K : Channel α β) :
    probabilityRatios p K = insert 0 (standardKLRatios p K) := by
  classical
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases he : r = p
    · subst r
      simp
    · exact Set.mem_insert_of_mem 0 ⟨r, hr, he, rfl⟩
  · intro hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact ⟨p, (fun _ h => h), by simp⟩
    · exact standardKLRatios_subset p K hv

/-- The existing coefficient is exactly the standard one excluding `Q = P`,
including the explicit empty-test convention. -/
theorem coefficient_eq_standardKLCoefficient (p : Law α) (K : Channel α β) :
    coefficient p K = standardKLCoefficient p K := by
  classical
  rw [coefficient_eq_sup_KL, probabilityRatios_eq_insert_standard]
  unfold standardKLCoefficient
  split_ifs with h
  · rw [csSup_insert (standardKLRatios_bddAbove p K) h]
    exact sup_eq_right.mpr (Real.sSup_nonneg (fun _ hv => standardKLRatios_nonneg hv))
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    simp

/-- When an alternative exists, no empty-set convention is needed. -/
theorem coefficient_eq_sup_KL_ne (p : Law α) (K : Channel α β)
    (h : ∃ r : Law α, Supported r p ∧ r ≠ p) :
    coefficient p K = sSup (standardKLRatios p K) := by
  rw [coefficient_eq_standardKLCoefficient]
  have hn : (standardKLRatios p K).Nonempty := by
    rcases h with ⟨r, hr, hne⟩
    exact ⟨_, r, hr, hne, rfl⟩
  simp [standardKLCoefficient, hn]

/-- The standard positive-KL formula for any reference with an alternative.
`Supported` is essential because `relativeEntropy` is real-valued, not an
extended-real divergence on unsupported laws. -/
theorem coefficient_eq_sup_positive_KL (p : Law α) (K : Channel α β)
    (h : ∃ r : Law α, Supported r p ∧ r ≠ p) :
    coefficient p K = sSup {v | ∃ r : Law α, Supported r p ∧
      0 < relativeEntropy r p ∧
      v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  rw [coefficient_eq_sup_KL_ne p K h, standardKLRatios_eq_positive]

/-- If the reference law is the only supported law, the coefficient is zero. -/
theorem coefficient_eq_zero_of_no_alternative (p : Law α) (K : Channel α β)
    (h : ∀ r : Law α, Supported r p → r = p) : coefficient p K = 0 := by
  rw [coefficient_eq_standardKLCoefficient]
  have hn : ¬(standardKLRatios p K).Nonempty := by
    rintro ⟨_, r, hr, hne, _⟩
    exact hne (h r hr)
  simp [standardKLCoefficient, hn]

/-- A supported law cannot differ from a point-mass reference. -/
theorem supported_eq_of_pointMass {r p : Law α} (h : Supported r p)
    {a : α} (hp : p.mass a = 1) : r = p := by
  classical
  have hpzero (b : α) (hb : b ≠ a) : p.mass b = 0 := by
    have he : ∑ i ∈ Finset.univ.erase a, p.mass i = 0 := by
      have hs := Finset.sum_erase_add Finset.univ p.mass (Finset.mem_univ a)
      rw [p.total, hp] at hs
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => p.nonneg i)).mp he b (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)
  have hrzero (b : α) (hb : b ≠ a) : r.mass b = 0 := h b (hpzero b hb)
  have hra : r.mass a = 1 := by
    calc
      r.mass a = ∑ b, r.mass b :=
        (Finset.sum_eq_single a (fun b _ hb => hrzero b hb) (by simp)).symm
      _ = 1 := r.total
  have hmass : r.mass = p.mass := by
    funext b
    by_cases hb : b = a
    · subst b
      rw [hra, hp]
    · rw [hrzero b hb, hpzero b hb]
  cases r
  cases p
  cases hmass
  rfl

/-- Deterministic inputs have zero coefficient, without any condition on the channel. -/
theorem coefficient_eq_zero_of_pointMass (p : Law α) (K : Channel α β)
    {a : α} (hp : p.mass a = 1) : coefficient p K = 0 :=
  coefficient_eq_zero_of_no_alternative p K (fun _ h => supported_eq_of_pointMass h hp)

/-- With full-support reference input, support restrictions remove no law. -/
theorem standardKLRatios_of_fullSupport (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) :
    standardKLRatios p K =
      {v | ∃ r : Law α, r ≠ p ∧
        v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  ext v
  constructor
  · rintro ⟨r, _, hne, hv⟩
    exact ⟨r, hne, hv⟩
  · rintro ⟨r, hne, hv⟩
    exact ⟨r, (fun a ha => False.elim ((ne_of_gt (hp a)) ha)), hne, hv⟩

/-- The familiar full-support formula, whose only test restriction is `Q ≠ P`.
The existence hypothesis separates the one-point alphabet convention. -/
theorem coefficient_eq_sup_KL_ne_of_fullSupport (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (h : ∃ r : Law α, r ≠ p) :
    coefficient p K = sSup {v | ∃ r : Law α, r ≠ p ∧
      v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  have hs : ∃ r : Law α, Supported r p ∧ r ≠ p := by
    rcases h with ⟨r, hne⟩
    exact ⟨r, (fun a ha => False.elim ((ne_of_gt (hp a)) ha)), hne⟩
  rw [coefficient_eq_sup_KL_ne p K hs, standardKLRatios_of_fullSupport p K hp]

end BinaryPairBound.FiniteInfo
