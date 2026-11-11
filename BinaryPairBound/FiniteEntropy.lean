module

public import BinaryPairBound.Entropy
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Finite laws, channels, and homogeneous relative entropy

The density formulation includes zero-mass atoms without choosing a conditional
law there. For a nonnegative density of mean one, `entropy` is exactly KL.
-/

noncomputable section
@[expose] public section
open scoped BigOperators

namespace BinaryPairBound.FiniteInfo

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

structure Channel (α β : Type*) [Fintype β] where
  prob : α → β → ℝ
  nonneg : ∀ a b, 0 ≤ prob a b
  total : ∀ a, ∑ b, prob a b = 1

def entropy {α : Type*} [Fintype α] (p f : α → ℝ) : ℝ :=
  (∑ a, p a * f a * Real.log (f a)) -
    (∑ a, p a * f a) * Real.log (∑ a, p a * f a)

def out {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) : Law β where
  mass b := ∑ a, p.mass a * K.prob a b
  nonneg b := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (K.nonneg a b)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, K.total, mul_one]
    exact p.total

def transfer {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (f : α → ℝ) (b : β) : ℝ :=
  (∑ a, p.mass a * K.prob a b * f a) / (out p K).mass b

def Contracts {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (lam : ℝ) : Prop :=
  ∀ f : α → ℝ, (∀ a, 0 ≤ f a) →
    entropy (out p K).mass (transfer p K f) ≤ lam * entropy p.mass f

theorem entropy_nonneg {α : Type*} [Fintype α] (p : Law α)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ entropy p.mass f := by
  have h := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := p.mass) (p := f) (fun a _ => p.nonneg a) p.total (fun a _ => hf a)
  simp only [smul_eq_mul] at h
  unfold entropy
  simpa only [mul_assoc] using sub_nonneg.mpr h

theorem transfer_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (b : β) :
    0 ≤ transfer p K f b :=
  div_nonneg (Finset.sum_nonneg fun a _ =>
    mul_nonneg (mul_nonneg (p.nonneg a) (K.nonneg a b)) (hf a)) ((out p K).nonneg b)

theorem joint_zero_of_out_zero {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) {b : β} (hb : (out p K).mass b = 0) (a : α) :
    p.mass a * K.prob a b = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    mul_nonneg (p.nonneg a) (K.nonneg a b))).mp hb a (Finset.mem_univ a)

theorem out_mul_transfer {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (f : α → ℝ) (b : β) :
    (out p K).mass b * transfer p K f b = ∑ a, p.mass a * K.prob a b * f a := by
  by_cases hb : (out p K).mass b = 0
  · simp [hb, joint_zero_of_out_zero p K hb]
  · exact mul_div_cancel₀ _ hb

theorem sum_out_mul_transfer {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) (f : α → ℝ) :
    ∑ b, (out p K).mass b * transfer p K f b = ∑ a, p.mass a * f a := by
  simp_rw [out_mul_transfer]
  rw [Finset.sum_comm]
  congr 1
  funext a
  simp_rw [mul_right_comm (p.mass a), ← Finset.mul_sum, K.total, mul_one]

theorem entropy_transfer_le {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (K : Channel α β) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    entropy (out p K).mass (transfer p K f) ≤ entropy p.mass f := by
  have hpoint (b : β) :
      (out p K).mass b * transfer p K f b * Real.log (transfer p K f b) ≤
        ∑ a, p.mass a * K.prob a b * f a * Real.log (f a) := by
    by_cases hb : (out p K).mass b = 0
    · simp [hb, joint_zero_of_out_zero p K hb]
    have hbpos : 0 < (out p K).mass b := lt_of_le_of_ne ((out p K).nonneg b) (Ne.symm hb)
    have hw : ∑ a, p.mass a * K.prob a b / (out p K).mass b = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      change (out p K).mass b * ((out p K).mass b)⁻¹ = 1
      exact mul_inv_cancel₀ hb
    have h := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
      (w := fun a => p.mass a * K.prob a b / (out p K).mass b) (p := f)
      (fun a _ => div_nonneg (mul_nonneg (p.nonneg a) (K.nonneg a b)) hbpos.le)
      hw (fun a _ => hf a)
    simp only [smul_eq_mul] at h
    have he : (∑ a, p.mass a * K.prob a b / (out p K).mass b * f a) =
        transfer p K f b := by
      simp only [transfer, div_eq_mul_inv, mul_right_comm _ _ (f _), Finset.sum_mul]
    rw [he] at h
    have hm := mul_le_mul_of_nonneg_left h hbpos.le
    convert hm using 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      field_simp
  unfold entropy
  rw [sum_out_mul_transfer]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ b, ∑ a, p.mass a * K.prob a b * f a * Real.log (f a) :=
      Finset.sum_le_sum fun b _ => hpoint b
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [show ∀ b, p.mass a * K.prob a b * f a * Real.log (f a) =
        (p.mass a * f a * Real.log (f a)) * K.prob a b by intro b; ring]
      rw [← Finset.mul_sum, K.total, mul_one]

end BinaryPairBound.FiniteInfo
