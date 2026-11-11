module

public import BinaryPairBound.BinaryKernel
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

noncomputable section
@[expose] public section

open MeasureTheory

namespace BinaryPairBound

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

private lemma real_bool_partition (X : Ω → Bool) (hX : Measurable X)
    (E : Set Ω) (hE : MeasurableSet E) :
    μ.real (E ∩ X ⁻¹' {false}) + μ.real (E ∩ X ⁻¹' {true}) = μ.real E := by
  rw [← measureReal_union]
  · congr 1
    ext ω
    cases h : X ω <;> simp [h]
  · apply Set.disjoint_left.mpr
    intro ω hf ht
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hf ht
    exact Bool.false_ne_true (hf.2.symm.trans ht.2)
  · exact hE.inter (hX (measurableSet_singleton true))

/-- The actual joint law of two binary random variables on any probability space. -/
def binaryLaw (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) : BinaryLaw where
  mass a b := μ.real (W ⁻¹' {a} ∩ Z ⁻¹' {b})
  nonneg _ _ := measureReal_nonneg
  total := by
    have h0 := real_bool_partition μ Z hZ (W ⁻¹' {false})
      (hW (measurableSet_singleton false))
    have h1 := real_bool_partition μ Z hZ (W ⁻¹' {true})
      (hW (measurableSet_singleton true))
    have ht := real_bool_partition μ W hW Set.univ MeasurableSet.univ
    simp only [Set.univ_inter, probReal_univ] at ht
    linarith

namespace binaryLaw

variable {μ} {W Z : Ω → Bool} (hW : Measurable W) (hZ : Measurable Z)

lemma row (a : Bool) :
    (binaryLaw μ W Z hW hZ).mass a false + (binaryLaw μ W Z hW hZ).mass a true =
      μ.real (W ⁻¹' {a}) :=
  real_bool_partition μ Z hZ _ (hW (measurableSet_singleton a))

lemma column (b : Bool) :
    (binaryLaw μ W Z hW hZ).mass false b + (binaryLaw μ W Z hW hZ).mass true b =
      μ.real (Z ⁻¹' {b}) := by
  simpa only [binaryLaw, Set.inter_comm] using
    real_bool_partition μ W hW (Z ⁻¹' {b}) (hZ (measurableSet_singleton b))

lemma input_eq : (binaryLaw μ W Z hW hZ).input = μ.real (W ⁻¹' {true}) := row hW hZ true
lemma output_eq : (binaryLaw μ W Z hW hZ).output = μ.real (Z ⁻¹' {true}) := column hW hZ true

private lemma bool_set_cases (s : Set Bool) :
    s = ∅ ∨ s = {false} ∨ s = {true} ∨ s = Set.univ := by
  classical
  by_cases hf : false ∈ s <;> by_cases ht : true ∈ s
  · right; right; right; ext b; cases b <;> simp_all
  · right; left; ext b; cases b <;> simp_all
  · right; right; left; ext b; cases b <;> simp_all
  · left; ext b; cases b <;> simp_all

/-- The table's product-factorization criterion is mathlib probabilistic independence. -/
theorem independent_iff :
    (binaryLaw μ W Z hW hZ).IsIndependent ↔ ProbabilityTheory.IndepFun W Z μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  constructor
  · intro h s t _ _
    have hsingle (a b : Bool) :
        μ (W ⁻¹' {a} ∩ Z ⁻¹' {b}) = μ (W ⁻¹' {a}) * μ (Z ⁻¹' {b}) := by
      have h' := h a b
      rw [row hW hZ, column hW hZ] at h'
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simpa only [ENNReal.toReal_mul, Measure.real, binaryLaw] using h'
    rcases bool_set_cases s with rfl | rfl | rfl | rfl <;>
      rcases bool_set_cases t with rfl | rfl | rfl | rfl
    all_goals try simp only [Set.preimage_empty, Set.empty_inter, Set.inter_empty, measure_empty,
      zero_mul, mul_zero, Set.preimage_univ, Set.univ_inter, Set.inter_univ, measure_univ,
      one_mul, mul_one]
    all_goals first | exact hsingle false false | exact hsingle false true |
      exact hsingle true false | exact hsingle true true
  · intro h a b
    have h' := congrArg ENNReal.toReal
      (h {a} {b} (measurableSet_singleton a) (measurableSet_singleton b))
    rw [row hW hZ, column hW hZ]
    simpa only [ENNReal.toReal_mul, Measure.real, binaryLaw] using h'

end binaryLaw

/-- Shannon mutual information of two measurable binary random variables, in nats. -/
def binaryMutualInfo (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) : ℝ :=
  (binaryLaw μ W Z hW hZ).mutualInfo

/-- The exact distribution-dependent coefficient from equation (2.2), with the paper's
zero convention at deterministic marginals. The conditional channel is reconstructed from
the actual joint law; no distributional representation is an extra assumption. -/
def binaryContraction (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) : ℝ :=
  (binaryLaw μ W Z hW hZ).contraction

/-- DSBS means equality of opposite joint atom probabilities. -/
def BinaryDSBS (W Z : Ω → Bool) : Prop :=
  μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {false}) = μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {true}) ∧
  μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {true}) = μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {false})

/-- The entropy definition is the sum over the actual four joint events. -/
theorem binaryMutualInfo_eq_entropy (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ =
      H (μ.real (W ⁻¹' {true})) + H (μ.real (Z ⁻¹' {true})) -
        (Real.negMulLog (μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {false})) +
         Real.negMulLog (μ.real (W ⁻¹' {false} ∩ Z ⁻¹' {true})) +
         Real.negMulLog (μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {false})) +
         Real.negMulLog (μ.real (W ⁻¹' {true} ∩ Z ⁻¹' {true}))) := by
  unfold binaryMutualInfo BinaryLaw.mutualInfo
  rw [binaryLaw.input_eq hW hZ, binaryLaw.output_eq hW hZ]
  rfl

/-- The random-variable coefficient agrees with the finite-alphabet KL coefficient,
not merely with a chosen scalar expression. -/
theorem binaryContraction_eq_coefficient (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    let P := binaryLaw μ W Z hW hZ
    binaryContraction μ W Z hW hZ =
      FiniteInfo.coefficient (FiniteInfo.bernoulli P.input P.valid.1)
        (FiniteInfo.binaryChannel P.left P.right P.valid.2.1 P.valid.2.2) := by
  dsimp only
  exact (FiniteInfo.coefficient_binary (binaryLaw μ W Z hW hZ).valid).symm

/-- Theorem 2.1 on an arbitrary probability space. -/
theorem binary_random_variable_bound (W Z : Ω → Bool) (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ ≤ phi (binaryContraction μ W Z hW hZ) :=
  BinaryLaw.sharp_bound _

/-- The complete equality statement in ordinary probabilistic terms. -/
theorem binary_random_variable_equality_iff (W Z : Ω → Bool)
    (hW : Measurable W) (hZ : Measurable Z) :
    binaryMutualInfo μ W Z hW hZ = phi (binaryContraction μ W Z hW hZ) ↔
      ProbabilityTheory.IndepFun W Z μ ∨ BinaryDSBS μ W Z := by
  change (binaryLaw μ W Z hW hZ).mutualInfo = phi (binaryLaw μ W Z hW hZ).contraction ↔ _
  rw [BinaryLaw.sharp_equality_iff, binaryLaw.independent_iff hW hZ]
  rfl

end BinaryPairBound
