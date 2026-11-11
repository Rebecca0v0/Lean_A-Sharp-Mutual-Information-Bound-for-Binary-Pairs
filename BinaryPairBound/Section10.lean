module

public import BinaryPairBound.FiniteTensorization
public import BinaryPairBound.FiniteProcessing
public import BinaryPairBound.FiniteJoint

/-! # Section 10: binary observations of IID finite-alphabet sources

Functions have the ordinary vector type `(Fin n → α) → Bool`. The law below
is the actual pushforward of the independent source law; tensorization is
proved in `FiniteTensorization`, not supplied as a hypothesis.
-/

noncomputable section
@[expose] public section
open scoped BigOperators
namespace BinaryPairBound.FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Joint binary law obtained by separately observing two IID sequences. -/
def iidBinaryLaw (p : Law α) (K : Channel α β) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) : BinaryLaw :=
  processedLaw (p.power n) (K.power n)
    (fun x => f (Sample.toVector n x)) (fun y => g (Sample.toVector n y))

/-- Exact atom formula: this is the pushforward of the IID source, not an abstract cap model. -/
theorem iidBinaryLaw_mass (p : Law α) (K : Channel α β) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) (a b : Bool) :
    (iidBinaryLaw p K n f g).mass a b =
      ∑ x : Fin n → α, ∑ y : Fin n → β,
        if f x = a ∧ g y = b then ∏ i, p.mass (x i) * K.prob (x i) (y i) else 0 := by
  rw [iidBinaryLaw, processedLaw_mass]
  apply Fintype.sum_equiv (Sample.equivVector n)
  intro x
  apply Fintype.sum_equiv (Sample.equivVector n)
  intro y
  simp only [Law.power_mass, Channel.power_prob, Sample.equivVector, Equiv.coe_fn_mk,
    Finset.prod_mul_distrib]

/-- Atom formula for independent copies of an arbitrary finite joint distribution. -/
theorem iid_joint_binary_mass (P : Law (α × β)) (default : β) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) (a b : Bool) :
    (iidBinaryLaw (first P) (conditional P default) n f g).mass a b =
      ∑ x : Fin n → α, ∑ y : Fin n → β,
        if f x = a ∧ g y = b then ∏ i, P.mass (x i, y i) else 0 := by
  rw [iidBinaryLaw_mass]
  simp_rw [first_mul_conditional]

/-- Section 10, for every finite-alphabet source and every number of observations. -/
theorem iid_binary_bound (p : Law α) (K : Channel α β) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    (iidBinaryLaw p K n f g).mutualInfo ≤ phi (coefficient p K) :=
  processedLaw_bound_of_cap (coefficient_mem p K)
    ((contracts_coefficient p K).power (coefficient_nonneg p K) n) _ _

/-- The binary output coefficient is at most the one-copy source coefficient. -/
theorem iid_binary_contraction_le (p : Law α) (K : Channel α β) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    (iidBinaryLaw p K n f g).contraction ≤ coefficient p K :=
  (processedLaw_contraction_le _ _ _ _).trans (coefficient_power_le p K n)

/-- The same consequence expressed directly in terms of an arbitrary joint source law. -/
theorem iid_joint_binary_bound (P : Law (α × β)) (default : β) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    (iidBinaryLaw (first P) (conditional P default) n f g).mutualInfo ≤
      phi (jointCoefficient P default) :=
  iid_binary_bound (first P) (conditional P default) n f g

/-- For a DSBS, Boolean observations retain at most the one-coordinate information. -/
theorem iid_dsbs_binary_bound {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (n : ℕ)
    (f g : (Fin n → Bool) → Bool) :
    (iidBinaryLaw (bernoulli (1 / 2) (by norm_num)) (binaryChannel c c hc hc) n f g).mutualInfo ≤
      J (1 / 2) c c := by
  have hv : Valid (1 / 2) c c := ⟨by norm_num, hc, hc⟩
  have h := iid_binary_bound (bernoulli (1 / 2) hv.1) (binaryChannel c c hc hc) n f g
  rw [coefficient_binary hv, ← sharp_equality_of_dsbs hv ⟨rfl, rfl⟩] at h
  exact h

/-- The familiar DSBS expression in nats, valid for crossover in the whole unit interval. -/
theorem iid_dsbs_binary_bound_entropy {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (n : ℕ)
    (f g : (Fin n → Bool) → Bool) :
    (iidBinaryLaw (bernoulli (1 / 2) (by norm_num)) (binaryChannel c c hc hc) n f g).mutualInfo ≤
      Real.log 2 - H c := by
  simpa only [J_symmetric] using iid_dsbs_binary_bound hc n f g

end BinaryPairBound.FiniteInfo
