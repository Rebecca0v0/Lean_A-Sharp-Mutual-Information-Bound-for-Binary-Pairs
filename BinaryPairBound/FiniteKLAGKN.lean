module

public import BinaryPairBound.FiniteKLStandard
public import BinaryPairBound.BinaryKernel
public import BinaryPairBound.Section10

/-! # The AGKN coefficient on full-support input laws

This is the direct full-support definition: the reference input law `p` must
have positive mass at every symbol, and the test laws `r` must differ from `p`.
There is no support restriction on the test law and no test with `r = p`.
The coefficient is zero if the test set is empty (the one-symbol input case).

The existing `coefficient` applies more generally to reference laws with zeros.
The theorems below identify that general extension with this AGKN definition
on its full-support domain, so the existing bounds can be used directly here.
-/

noncomputable section
@[expose] public section
namespace BinaryPairBound.FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- AGKN KL ratios: a full-support reference and only distinct alternative laws.
An alternative law itself may have zero-probability symbols. -/
def agknRatios (p : Law α) (K : Channel α β)
    (_hp : ∀ a, 0 < p.mass a) : Set ℝ :=
  {v | ∃ r : Law α, r ≠ p ∧
    v = relativeEntropy (out r K) (out p K) / relativeEntropy r p}

/-- The AGKN full-support coefficient, directly excluding the unchanged input.
The explicit zero branch covers an input alphabet with no alternative law. -/
def agknCoefficient (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) : ℝ := by
  classical
  exact if (agknRatios p K hp).Nonempty then sSup (agknRatios p K hp) else 0

/-- Full support makes every distinct test law have a positive KL denominator. -/
theorem agkn_denominator_pos (p r : Law α) (hp : ∀ a, 0 < p.mass a)
    (hne : r ≠ p) : 0 < relativeEntropy r p := by
  have hs : Supported r p := fun a ha => False.elim ((ne_of_gt (hp a)) ha)
  exact (relativeEntropy_pos_iff hs).mpr hne

/-- On a full-support reference, the supported and AGKN test sets coincide. -/
theorem agknRatios_eq_standardKLRatios (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) :
    agknRatios p K hp = standardKLRatios p K := by
  exact (standardKLRatios_of_fullSupport p K hp).symm

/-- The direct AGKN definition equals the previously verified general extension. -/
theorem agknCoefficient_eq_coefficient (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) : agknCoefficient p K hp = coefficient p K := by
  rw [coefficient_eq_standardKLCoefficient]
  unfold agknCoefficient standardKLCoefficient
  have he := agknRatios_eq_standardKLRatios p K hp
  split_ifs with ha hs hs
  · exact congrArg sSup he
  · exact False.elim (hs (he ▸ ha))
  · exact False.elim (ha (he.symm ▸ hs))
  · rfl

/-- If an alternative input law exists, AGKN is the displayed supremum over `r ≠ p`. -/
theorem agknCoefficient_eq_sup (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (h : ∃ r : Law α, r ≠ p) :
    agknCoefficient p K hp = sSup {v | ∃ r : Law α, r ≠ p ∧
      v = relativeEntropy (out r K) (out p K) / relativeEntropy r p} := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_eq_sup_KL_ne_of_fullSupport p K hp h

/-- The direct definition is zero when no distinct input law exists. -/
theorem agknCoefficient_eq_zero_of_no_alternative (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (h : ∀ r : Law α, r = p) :
    agknCoefficient p K hp = 0 := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_eq_zero_of_no_alternative p K (fun r _ => h r)

/-- A deterministic output has zero AGKN coefficient, for every full-support input. -/
theorem agknCoefficient_eq_zero_of_output_pointMass (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) {b : β} (hb : (out p K).mass b = 1) :
    agknCoefficient p K hp = 0 := by
  rw [agknCoefficient_eq_coefficient, coefficient_eq_sup_KL]
  have hz : probabilityRatios p K = {0} := by
    ext v
    constructor
    · rintro ⟨r, hr, rfl⟩
      have ho := supported_eq_of_pointMass (supported_out hr K) hb
      simp [ho]
    · intro hv
      have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨p, (fun _ h => h), by simp⟩
  rw [hz]
  simp

/-- The AGKN coefficient lies in the usual interval. -/
theorem agknCoefficient_mem (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) : agknCoefficient p K hp ∈ Set.Icc (0 : ℝ) 1 := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_mem p K

/-- A non-deterministic Bernoulli input has full support on `Bool`. -/
theorem bernoulli_fullSupport {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hvalid : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ b, 0 < (bernoulli s hvalid).mass b := by
  intro b
  cases b <;> simp [bernoulli, hs.1, sub_pos.mpr hs.2]

/-- The direct AGKN coefficient is the paper's scalar `S` for binary laws.
The input is non-deterministic; the output is allowed to be deterministic. -/
theorem agknCoefficient_binary {s c d : ℝ} (hv : Valid s c d)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    agknCoefficient (bernoulli s hv.1) (binaryChannel c d hv.2.1 hv.2.2)
      (bernoulli_fullSupport hs hv.1) = S s c d := by
  rw [agknCoefficient_eq_coefficient]
  exact coefficient_binary hv

/-- Section 10 stated directly with the AGKN full-support coefficient. -/
theorem iid_binary_bound_agkn (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    (iidBinaryLaw p K n f g).mutualInfo ≤ phi (agknCoefficient p K hp) := by
  rw [agknCoefficient_eq_coefficient]
  exact iid_binary_bound p K n f g

end BinaryPairBound.FiniteInfo
