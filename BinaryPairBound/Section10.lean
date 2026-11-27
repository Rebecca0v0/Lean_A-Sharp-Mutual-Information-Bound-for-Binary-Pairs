module

public import BinaryPairBound.FiniteInformation
public import BinaryPairBound.BinaryRandomVariables
public import BinaryPairBound.Tensorization

/-!
# Section 10 for Boolean functions of IID observations

在同一文件中证明两端函数处理、有限IID推论、DSBS特例和任意概率空间接口。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## Two-sided deterministic processing

证明对两边分别应用二元值函数不会增大系数，并把主定理应用到函数输出。
-/

@[expose] public noncomputable section FiniteProcessing

open scoped BigOperators

namespace FiniteInfo

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

end FiniteInfo

end FiniteProcessing

/-! ## The finite-source IID bound and DSBS corollary

对有限字母表来源的 IID 样本和任意二元值函数，证明论文第 10 节的上界及 DSBS 推论。
-/

@[expose] public noncomputable section Section10

open scoped BigOperators

namespace FiniteInfo

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

end FiniteInfo

end Section10

/-! ## The IID bound with the full-support coefficient -/

@[expose] public noncomputable section AGKNIID

namespace FiniteInfo

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Section 10 stated directly with the AGKN full-support coefficient. -/
theorem iid_binary_bound_agkn (p : Law α) (K : Channel α β)
    (hp : ∀ a, 0 < p.mass a) (n : ℕ)
    (f : (Fin n → α) → Bool) (g : (Fin n → β) → Bool) :
    (iidBinaryLaw p K n f g).mutualInfo ≤ phi (agknCoefficient p K hp) := by
  rw [agknCoefficient_eq_coefficient]
  exact iid_binary_bound p K n f g

end FiniteInfo

end AGKNIID

/-! ## The same IID conclusions on arbitrary probability spaces

把有限乘积概率表上的结论接到任意概率空间上满足 IID 联合分布条件的随机变量。
-/

@[expose] public noncomputable section Section10RandomVariables

open MeasureTheory
open scoped BigOperators

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

end Section10RandomVariables

end BinaryPairBound
