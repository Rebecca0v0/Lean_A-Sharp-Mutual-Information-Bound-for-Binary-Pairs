module

public import BinaryPairBound.FiniteRandomVariables
public import BinaryPairBound.Section10

/-! # Section 10 on an arbitrary probability space

The hypotheses below specify the actual joint atom probabilities of the observations.
Their product factorization is precisely the IID source law; no contraction bound,
tensorization principle, or information inequality is assumed.
-/
noncomputable section
@[expose] public section
open MeasureTheory
open scoped BigOperators

namespace BinaryPairBound
open FiniteInfo

variable {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem binaryLaw_ext {P Q : BinaryLaw} (h : P.mass = Q.mass) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- Joint atom factorization for independent observations with common joint law `P`. -/
def HasIIDJointLaw (P : Law (α × β)) {n : ℕ}
    (X : Ω → (Fin n → α)) (Y : Ω → (Fin n → β)) : Prop :=
  ∀ x y, μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) = ∏ i, P.mass (x i, y i)

/-- The event-based law agrees exactly with the finite tensor-product pushforward. -/
theorem binaryLaw_iid_joint_eq (P : Law (α × β)) (default : β) {n : ℕ}
    (X : Ω → (Fin n → α)) (Y : Ω → (Fin n → β))
    (hX : Measurable X) (hY : Measurable Y) (hLaw : HasIIDJointLaw μ P X Y)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    binaryLaw μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY) =
      iidBinaryLaw (first P) (conditional P default) n f g := by
  apply binaryLaw_ext
  funext a b
  rw [binaryLaw_mass_eq_sum μ X Y hX hY f g a b, iid_joint_binary_mass]
  unfold HasIIDJointLaw at hLaw
  simp_rw [hLaw]

/-- The finite-source consequence in Section 10, for actual measurable random variables
on any probability space and any finite number of observations. -/
theorem iid_joint_random_variable_bound (P : Law (α × β)) (default : β) {n : ℕ}
    (X : Ω → (Fin n → α)) (Y : Ω → (Fin n → β))
    (hX : Measurable X) (hY : Measurable Y) (hLaw : HasIIDJointLaw μ P X Y)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    binaryMutualInfo μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY) ≤ phi (jointCoefficient P default) := by
  unfold binaryMutualInfo
  rw [binaryLaw_iid_joint_eq μ P default X Y hX hY hLaw f g]
  exact iid_joint_binary_bound P default n f g

/-- The corresponding exact coefficient data-processing inequality. -/
theorem iid_joint_random_variable_contraction_le (P : Law (α × β)) (default : β) {n : ℕ}
    (X : Ω → (Fin n → α)) (Y : Ω → (Fin n → β))
    (hX : Measurable X) (hY : Measurable Y) (hLaw : HasIIDJointLaw μ P X Y)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    binaryContraction μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY) ≤ jointCoefficient P default := by
  unfold binaryContraction
  rw [binaryLaw_iid_joint_eq μ P default X Y hX hY hLaw f g]
  exact iid_binary_contraction_le (first P) (conditional P default) n f g

/-- The same exact law identity in input/channel coordinates. -/
theorem binaryLaw_iid_channel_eq (p : Law α) (K : Channel α β) {n : ℕ}
    (X : Ω → (Fin n → α)) (Y : Ω → (Fin n → β))
    (hX : Measurable X) (hY : Measurable Y) (hLaw : HasIIDJointLaw μ (joint p K) X Y)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    binaryLaw μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY) = iidBinaryLaw p K n f g := by
  apply binaryLaw_ext
  funext a b
  rw [binaryLaw_mass_eq_sum μ X Y hX hY f g a b, iidBinaryLaw_mass]
  unfold HasIIDJointLaw at hLaw
  simp_rw [hLaw]
  rfl

/-- The Boolean-function inequality for IID DSBS observations, including deterministic
channels and either sign of the correlation. -/
theorem iid_dsbs_random_variable_bound {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) {n : ℕ}
    (X Y : Ω → (Fin n → Bool)) (hX : Measurable X) (hY : Measurable Y)
    (hLaw : HasIIDJointLaw μ
      (joint (bernoulli (1 / 2) (by norm_num)) (binaryChannel c c hc hc)) X Y)
    (f g : (Fin n → Bool) → Bool) :
    binaryMutualInfo μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY) ≤ Real.log 2 - H c := by
  unfold binaryMutualInfo
  rw [binaryLaw_iid_channel_eq μ _ _ X Y hX hY hLaw f g]
  exact iid_dsbs_binary_bound_entropy hc n f g

/-- The paper's exact DSBS display `I(f(Xⁿ);g(Yⁿ)) ≤ I(U;V)`, where `(U,V)`
is the one-copy source and the observation vectors have its IID joint law. -/
theorem iid_dsbs_random_variable_bound_source
    (U V : Ω → Bool) (hU : Measurable U) (hV : Measurable V)
    (hdsbs : BinaryDSBS μ U V) {n : ℕ}
    (X Y : Ω → (Fin n → Bool)) (hX : Measurable X) (hY : Measurable Y)
    (hLaw : HasIIDJointLaw μ (finiteLaw μ (fun ω => (U ω, V ω)) (hU.prodMk hV)) X Y)
    (f g : (Fin n → Bool) → Bool) :
    binaryMutualInfo μ (f ∘ X) (g ∘ Y) ((measurable_of_finite f).comp hX)
      ((measurable_of_finite g).comp hY) ≤ binaryMutualInfo μ U V hU hV := by
  let P := binaryLaw μ U V hU hV
  let p := bernoulli P.input P.valid.1
  let K := binaryChannel P.left P.right P.valid.2.1 P.valid.2.2
  have hsource (a b : Bool) :
      (finiteLaw μ (fun ω => (U ω, V ω)) (hU.prodMk hV)).mass (a,b) = P.mass a b := by
    change μ.real ((fun ω => (U ω, V ω)) ⁻¹' {(a,b)}) =
      μ.real (U ⁻¹' {a} ∩ V ⁻¹' {b})
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff]
  have hchannel : HasIIDJointLaw μ (joint p K) X Y := by
    intro x y
    rw [hLaw x y]
    apply Finset.prod_congr rfl
    intro i _
    change _ = (bernoulli P.input P.valid.1).mass (x i) *
      (binaryChannel P.left P.right P.valid.2.1 P.valid.2.2).prob (x i) (y i)
    rw [binaryLaw_joint, hsource]
  have heq : P.mutualInfo = phi P.contraction :=
    P.sharp_equality_iff.mpr (Or.inr hdsbs)
  have h := iid_binary_bound p K n f g
  dsimp only [p, K] at h
  rw [coefficient_binary P.valid] at h
  change (iidBinaryLaw p K n f g).mutualInfo ≤ phi P.contraction at h
  rw [← heq] at h
  unfold binaryMutualInfo
  rw [binaryLaw_iid_channel_eq μ p K X Y hX hY hchannel f g]
  exact h

end BinaryPairBound
