module

public import BinaryPairBound.FiniteEntropy

/-! # Convexity of homogeneous relative entropy, including zero-mass atoms -/
noncomputable section
@[expose] public section
open scoped BigOperators
namespace BinaryPairBound.FiniteInfo

lemma convex_mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) = y * (x * Real.log x) + x * (y * Real.log y) := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog_def] at h
  nlinarith

lemma div_mul_log {a b : ℝ} (hz : b = 0 → a = 0) :
    b * (a / b * Real.log (a / b)) = a * Real.log a - a * Real.log b := by
  by_cases hb : b = 0
  · simp [hb, hz hb]
  · have he : b * (a / b) = a := mul_div_cancel₀ a hb
    have h := convex_mul_log_mul b (a / b)
    rw [he] at h
    calc
      b * (a / b * Real.log (a / b)) = a * Real.log a - (a / b) * (b * Real.log b) := by linarith
      _ = a * Real.log a - a * Real.log b := by congr 1; field_simp

/-- Log-sum inequality with absolute continuity, allowing zero cells. -/
theorem log_sum_inequality {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hz : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log (∑ i, a i) - (∑ i, a i) * Real.log (∑ i, b i) ≤
      ∑ i, (a i * Real.log (a i) - a i * Real.log (b i)) := by
  by_cases hB : ∑ i, b i = 0
  · have hb0 : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).mp hB i (Finset.mem_univ i)
    have ha0 : ∀ i, a i = 0 := fun i => hz i (hb0 i)
    simp [ha0, hb0]
  have hBpos : 0 < ∑ i, b i :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hb i) (Ne.symm hB)
  have hmass (i : ι) : b i * (a i / b i) = a i := by
    by_cases h : b i = 0
    · simp [h, hz i h]
    · exact mul_div_cancel₀ _ h
  have hw : ∑ i, b i / (∑ j, b j) = 1 := by simp only [div_eq_mul_inv, ← Finset.sum_mul]; exact mul_inv_cancel₀ hB
  have havg : ∑ i, b i / (∑ j, b j) * (a i / b i) = (∑ i, a i) / (∑ j, b j) := by
    simp_rw [div_mul_eq_mul_div, hmass, div_eq_mul_inv, ← Finset.sum_mul]
  have h := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := fun i => b i / (∑ j, b j)) (p := fun i => a i / b i)
    (fun i _ => div_nonneg (hb i) hBpos.le) hw (fun i _ => div_nonneg (ha i) (hb i))
  simp only [smul_eq_mul, havg] at h
  have hh := mul_le_mul_of_nonneg_left h hBpos.le
  rw [div_mul_log (fun h0 => (hB h0).elim)] at hh
  calc
    _ ≤ (∑ j, b j) * ∑ i, b i / (∑ j, b j) * (a i / b i * Real.log (a i / b i)) := hh
    _ = ∑ i, b i * (a i / b i * Real.log (a i / b i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ = _ := by simp_rw [div_mul_log (hz _)]

lemma scaled_log_term (w x y : ℝ) (hz : y = 0 → x = 0) :
    (w * x) * Real.log (w * x) - (w * x) * Real.log (w * y) =
      w * (x * Real.log x - x * Real.log y) := by
  by_cases hw : w = 0
  · simp [hw]
  by_cases hy : y = 0
  · simp [hy, hz hy]
  rw [convex_mul_log_mul, Real.log_mul hw hy]
  ring

/-- Homogeneous relative entropy is convex in the density. No normalization
of the nonnegative mixture weights is necessary. -/
theorem entropy_mix_le {α ι : Type*} [Fintype α] [Fintype ι]
    (p : Law α) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ι → α → ℝ) (hf : ∀ i a, 0 ≤ f i a) :
    entropy p.mass (fun a => ∑ i, w i * f i a) ≤
      ∑ i, w i * entropy p.mass (f i) := by
  let m : ι → ℝ := fun i => ∑ a, p.mass a * f i a
  let M : ℝ := ∑ i, w i * m i
  let g : α → ℝ := fun a => ∑ i, w i * f i a
  have hm (i : ι) : 0 ≤ m i := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (hf i a)
  have hmean : ∑ a, p.mass a * g a = M := by
    dsimp [M, g, m]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hpoint (a : α) :
      p.mass a * (g a * Real.log (g a) - g a * Real.log M) ≤
        p.mass a * ∑ i, w i * (f i a * Real.log (f i a) - f i a * Real.log (m i)) := by
    by_cases hp : p.mass a = 0
    · simp [hp]
    have hp' : 0 < p.mass a := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
    have hz (i : ι) (hmi : m i = 0) : f i a = 0 := by
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => mul_nonneg (p.nonneg b) (hf i b))).mp hmi a (Finset.mem_univ a)
      exact (mul_eq_zero.mp hzero).resolve_left hp
    have hh := log_sum_inequality (fun i => w i * f i a) (fun i => w i * m i)
      (fun i => mul_nonneg (hw i) (hf i a)) (fun i => mul_nonneg (hw i) (hm i))
      (fun i hi => by
        rcases mul_eq_zero.mp hi with hi | hi
        · simp [hi]
        · simp [hz i hi])
    simp_rw [scaled_log_term _ _ _ (hz _)] at hh
    exact mul_le_mul_of_nonneg_left hh hp'.le
  calc
    entropy p.mass g = ∑ a, p.mass a * (g a * Real.log (g a) - g a * Real.log M) := by
      unfold entropy
      rw [hmean]
      simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hmean]
    _ ≤ ∑ a, p.mass a * ∑ i, w i * (f i a * Real.log (f i a) - f i a * Real.log (m i)) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ i, w i * entropy p.mass (f i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [entropy, mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
      dsimp [m]
      simp only [← Finset.sum_mul]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      · congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring

end BinaryPairBound.FiniteInfo
