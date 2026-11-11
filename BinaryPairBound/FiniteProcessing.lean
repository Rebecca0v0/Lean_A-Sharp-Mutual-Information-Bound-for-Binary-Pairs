module

public import BinaryPairBound.BinaryKernel

/-! # Deterministic processing of a finite pair to two binary observations -/
noncomputable section
@[expose] public section
open scoped BigOperators
namespace BinaryPairBound.FiniteInfo
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- A deterministic finite channel. -/
def Channel.det [DecidableEq β] (f : α → β) : Channel α β where
  prob a b := if f a = b then 1 else 0
  nonneg a b := by split_ifs <;> norm_num
  total a := by simp

/-- The joint law of a binary function of the input and a binary channel output. -/
def binaryImage (p : Law α) (K : Channel α Bool) (f : α → Bool) : BinaryLaw where
  mass a b := ∑ x, if f x = a then p.mass x * K.prob x b else 0
  nonneg a b := Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact mul_nonneg (p.nonneg x) (K.nonneg x b)
    · exact le_rfl
  total := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      _ = ∑ x, p.mass x := by
        apply Finset.sum_congr rfl
        intro x _
        have ht := K.total x
        simp only [Fintype.sum_bool] at ht
        cases f x <;> simp <;> nlinarith [congrArg (fun t : ℝ => p.mass x * t) ht]
      _ = 1 := p.total

lemma binaryLaw_joint (P : BinaryLaw) (a b : Bool) :
    (bernoulli P.input P.valid.1).mass a *
      (binaryChannel P.left P.right P.valid.2.1 P.valid.2.2).prob a b = P.mass a b := by
  cases a <;> cases b <;> simp only [bernoulli, binaryChannel, Bool.false_eq_true, ↓reduceIte]
  · exact P.mass00.symm
  · exact P.mass01.symm
  · exact P.mass10.symm
  · exact P.mass11.symm

lemma binaryLaw_input (P : BinaryLaw) (a : Bool) :
    (bernoulli P.input P.valid.1).mass a = P.mass a false + P.mass a true := by
  cases a
  · have h := P.total
    simp only [bernoulli, Bool.false_eq_true, ↓reduceIte, BinaryLaw.input]
    linarith
  · rfl

lemma binaryImage_input (p : Law α) (K : Channel α Bool) (f : α → Bool) (a : Bool) :
    (bernoulli (binaryImage p K f).input (binaryImage p K f).valid.1).mass a =
      ∑ x, if f x = a then p.mass x else 0 := by
  rw [binaryLaw_input]
  simp only [binaryImage]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have ht := K.total x
  simp only [Fintype.sum_bool] at ht
  by_cases h : f x = a
  · simp [h]
    nlinarith [congrArg (fun t : ℝ => p.mass x * t) ht]
  · simp [h]

lemma binaryImage_sum (p : Law α) (K : Channel α Bool) (f : α → Bool) (h : Bool → ℝ) :
    ∑ a, (bernoulli (binaryImage p K f).input (binaryImage p K f).valid.1).mass a * h a =
      ∑ x, p.mass x * h (f x) := by
  simp_rw [binaryImage_input, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases f x <;> simp

lemma binaryImage_entropy (p : Law α) (K : Channel α Bool) (f : α → Bool) (h : Bool → ℝ) :
    entropy (bernoulli (binaryImage p K f).input (binaryImage p K f).valid.1).mass h =
      entropy p.mass (fun x => h (f x)) := by
  unfold entropy
  simp only [mul_assoc]
  rw [binaryImage_sum, binaryImage_sum]

lemma binaryImage_out (p : Law α) (K : Channel α Bool) (f : α → Bool) (b : Bool) :
    (out (bernoulli (binaryImage p K f).input (binaryImage p K f).valid.1)
      (binaryChannel (binaryImage p K f).left (binaryImage p K f).right
        (binaryImage p K f).valid.2.1 (binaryImage p K f).valid.2.2)).mass b =
      (out p K).mass b := by
  simp only [out, binaryLaw_joint, binaryImage]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases f x <;> simp

lemma binaryImage_transfer (p : Law α) (K : Channel α Bool) (f : α → Bool) (h : Bool → ℝ) :
    transfer (bernoulli (binaryImage p K f).input (binaryImage p K f).valid.1)
      (binaryChannel (binaryImage p K f).left (binaryImage p K f).right
        (binaryImage p K f).valid.2.1 (binaryImage p K f).valid.2.2) h =
      transfer p K (fun x => h (f x)) := by
  funext b
  simp only [transfer]
  rw [binaryImage_out]
  simp only [binaryLaw_joint, binaryImage]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases f x <;> simp

/-- Deterministic preprocessing preserves a contraction cap of the original law. -/
theorem Contracts.binaryImage {p : Law α} {K : Channel α Bool} {lam : ℝ}
    (hc : Contracts p K lam) (f : α → Bool) :
    Contracts (bernoulli (binaryImage p K f).input (binaryImage p K f).valid.1)
      (binaryChannel (binaryImage p K f).left (binaryImage p K f).right
        (binaryImage p K f).valid.2.1 (binaryImage p K f).valid.2.2) lam := by
  intro h hh
  have hout := funext (binaryImage_out p K f)
  rw [hout, binaryImage_transfer, binaryImage_entropy]
  exact hc (fun x => h (f x)) (fun x => hh (f x))

/-- The actual binary joint law obtained from two deterministic observations. -/
def processedLaw (p : Law α) (K : Channel α β) (f : α → Bool) (g : β → Bool) : BinaryLaw :=
  binaryImage p (K.comp (Channel.det g)) f

/-- The atom masses are the pushforward of the original joint law `p(x)K(y|x)`. -/
theorem processedLaw_mass (p : Law α) (K : Channel α β) (f : α → Bool) (g : β → Bool)
    (a b : Bool) :
    (processedLaw p K f g).mass a b =
      ∑ x, ∑ y, if f x = a ∧ g y = b then p.mass x * K.prob x y else 0 := by
  simp only [processedLaw, binaryImage, Channel.comp, Channel.det]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hf : f x = a
  · simp only [hf, ↓reduceIte, true_and, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hg : g y = b <;> simp [hg]
  · simp [hf]

/-- Data processing for both observations, with the exact source coefficient. -/
theorem processedLaw_contraction_le (p : Law α) (K : Channel α β)
    (f : α → Bool) (g : β → Bool) :
    (processedLaw p K f g).contraction ≤ coefficient p K := by
  have hc := ((contracts_coefficient p K).postprocess (Channel.det g)).binaryImage f
  exact (contracts_binary_iff (processedLaw p K f g).valid (coefficient_nonneg p K)).mp hc

/-- A cap on a finite source bounds the mutual information of any two binary observations. -/
theorem processedLaw_bound_of_cap {p : Law α} {K : Channel α β} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hc : Contracts p K lam)
    (f : α → Bool) (g : β → Bool) :
    (processedLaw p K f g).mutualInfo ≤ phi lam := by
  have hcap : (processedLaw p K f g).contraction ≤ lam :=
    (processedLaw_contraction_le p K f g).trans ((coefficient_le_iff hlam.1).mpr hc)
  exact (processedLaw p K f g).sharp_bound.trans
    (phi_strictMonoOn.monotoneOn (S_mem_Icc (processedLaw p K f g).valid) hlam hcap)

/-- The one-observation case of the finite-source consequence in Section 10. -/
theorem processedLaw_bound (p : Law α) (K : Channel α β)
    (f : α → Bool) (g : β → Bool) :
    (processedLaw p K f g).mutualInfo ≤ phi (coefficient p K) :=
  processedLaw_bound_of_cap (coefficient_mem p K) (contracts_coefficient p K) f g

end BinaryPairBound.FiniteInfo
