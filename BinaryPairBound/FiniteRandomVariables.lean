module

public import BinaryPairBound.RandomVariables

/-! # Finite random-variable laws on arbitrary probability spaces -/
noncomputable section
@[expose] public section
open MeasureTheory
open scoped BigOperators

namespace BinaryPairBound

attribute [local instance] Classical.propDecidable

variable {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Probabilities of finite observations sum over the actual singleton events. -/
theorem measureReal_finite_preimage (X : Ω → α) (hX : Measurable X) (A : Set α) :
    μ.real (X ⁻¹' A) = ∑ a, if a ∈ A then μ.real (X ⁻¹' {a}) else 0 := by
  classical
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ.filter (· ∈ A))
    (fun a _ => hX (measurableSet_singleton a))
  simp only [Finset.sum_filter] at h
  simpa using h.symm

/-- The finite law of a measurable random variable, with no assumptions on its support. -/
def finiteLaw (X : Ω → α) (hX : Measurable X) : FiniteInfo.Law α where
  mass a := μ.real (X ⁻¹' {a})
  nonneg _ := measureReal_nonneg
  total := by
    have h := measureReal_finite_preimage μ X hX Set.univ
    simpa only [Set.preimage_univ, probReal_univ, Set.mem_univ, ↓reduceIte] using h.symm

/-- The probability table of deterministic binary observations is the actual pushforward
of the finite joint probability table. -/
theorem binaryLaw_mass_eq_sum (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) (f : α → Bool) (g : β → Bool) (a b : Bool) :
    (binaryLaw μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY)).mass a b =
      ∑ x, ∑ y, if f x = a ∧ g y = b then μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) else 0 := by
  have h := measureReal_finite_preimage μ (fun ω => (X ω, Y ω)) (hX.prodMk hY)
    {z : α × β | f z.1 = a ∧ g z.2 = b}
  rw [Fintype.sum_prod_type] at h
  have hp (x : α) (y : β) :
      (fun ω => (X ω, Y ω)) ⁻¹' {(x,y)} = X ⁻¹' {x} ∩ Y ⁻¹' {y} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff]
  simp only [hp, Set.mem_ofPred_eq] at h
  exact h

end BinaryPairBound
