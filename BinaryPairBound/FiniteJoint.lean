module

public import BinaryPairBound.FiniteKL

/-! # Arbitrary finite joint distributions and their conditional channels -/

noncomputable section
@[expose] public section
open scoped BigOperators
namespace BinaryPairBound.FiniteInfo

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

def joint (p : Law α) (K : Channel α β) : Law (α × β) where
  mass z := p.mass z.1 * K.prob z.1 z.2
  nonneg z := mul_nonneg (p.nonneg _) (K.nonneg _ _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, K.total, mul_one]
    exact p.total

def first (P : Law (α × β)) : Law α where
  mass a := ∑ b, P.mass (a,b)
  nonneg a := Finset.sum_nonneg fun b _ => P.nonneg (a,b)
  total := by simpa only [Fintype.sum_prod_type] using P.total

def second (P : Law (α × β)) : Law β where
  mass b := ∑ a, P.mass (a,b)
  nonneg b := Finset.sum_nonneg fun a _ => P.nonneg (a,b)
  total := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using P.total

theorem atom_zero_of_first_zero (P : Law (α × β)) {a : α}
    (ha : (first P).mass a = 0) (b : β) : P.mass (a,b) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => P.nonneg (a,b))).mp ha b (Finset.mem_univ b)

/-- The conditional distribution is arbitrary only on null input atoms. -/
def conditional (P : Law (α × β)) (default : β) : Channel α β where
  prob a b := if (first P).mass a = 0 then (if b = default then 1 else 0)
    else P.mass (a,b) / (first P).mass a
  nonneg a b := by
    split_ifs <;> first | positivity | exact div_nonneg (P.nonneg _) ((first P).nonneg _)
  total a := by
    classical
    by_cases ha : (first P).mass a = 0
    · simp [ha]
    · simp only [ha, ↓reduceIte, div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ ha

/-- Reconstructing a conditional channel recovers every atom of the original law. -/
theorem first_mul_conditional (P : Law (α × β)) (default : β) (a : α) (b : β) :
    (first P).mass a * (conditional P default).prob a b = P.mass (a,b) := by
  by_cases ha : (first P).mass a = 0
  · simp [ha, atom_zero_of_first_zero P ha b]
  · simp only [conditional, ha, ↓reduceIte]
    exact mul_div_cancel₀ _ ha

theorem joint_conditional_mass (P : Law (α × β)) (default : β) (z : α × β) :
    (joint (first P) (conditional P default)).mass z = P.mass z :=
  first_mul_conditional P default z.1 z.2

theorem out_conditional_mass (P : Law (α × β)) (default : β) (b : β) :
    (out (first P) (conditional P default)).mass b = (second P).mass b := by
  simp only [out, first_mul_conditional, second]

theorem transfer_conditional (P : Law (α × β)) (default : β) (f : α → ℝ) (b : β) :
    transfer (first P) (conditional P default) f b =
      (∑ a, P.mass (a,b) * f a) / (second P).mass b := by
  simp only [transfer, first_mul_conditional, out_conditional_mass]

/-- The exact KL contraction coefficient of an arbitrary finite-alphabet pair. -/
def jointCoefficient (P : Law (α × β)) (default : β) : ℝ :=
  coefficient (first P) (conditional P default)

/-- Choices of a conditional channel on null atoms have no effect on the coefficient. -/
theorem jointCoefficient_default_irrel (P : Law (α × β)) (b₀ b₁ : β) :
    jointCoefficient P b₀ = jointCoefficient P b₁ := by
  unfold jointCoefficient coefficient
  apply congrArg sSup
  ext v
  simp only [ratios, Set.mem_ofPred_eq]
  have he (f : α → ℝ) :
      entropy (out (first P) (conditional P b₀)).mass
        (transfer (first P) (conditional P b₀) f) =
      entropy (out (first P) (conditional P b₁)).mass
        (transfer (first P) (conditional P b₁) f) := by
    have ho₀ : (out (first P) (conditional P b₀)).mass = (second P).mass :=
      funext (out_conditional_mass P b₀)
    have ho₁ : (out (first P) (conditional P b₁)).mass = (second P).mass :=
      funext (out_conditional_mass P b₁)
    rw [ho₀, ho₁]
    congr 1
    funext b
    rw [transfer_conditional, transfer_conditional]
  simp_rw [he]

end BinaryPairBound.FiniteInfo
