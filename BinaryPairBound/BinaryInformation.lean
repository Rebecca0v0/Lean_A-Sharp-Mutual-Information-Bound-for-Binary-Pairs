module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Binary entropy, KL divergence, and equation (4.1)

在同一文件中完整读到参数定义、熵与KL、实际导数、带lambda的切线公式(4.1)，以及系数与KL上界的等价关系。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.

For equation (4.1), the definitions below introduce the actual curve
F_lambda(x) = H(q(x)) - lambda H(x) and its derivative-based tangent.
The proof then establishes H's derivative, applies the chain rule, and combines
the two entropy-gap identities. The reference probabilities s and q(s) lie in
(0,1); test probabilities x may include 0 and 1.
-/

namespace BinaryPairBound

/-! ## Parameters, entropy, KL, and the lambda curve

定义文章使用的概率参数、互信息 J、系数 S 和取等条件；先检查各个定义允许哪些输入。
-/

@[expose] public noncomputable section Definitions

abbrev H : ℝ → ℝ := Real.binEntropy

/-- Cross-entropy form of Bernoulli KL, with interior reference parameter. -/
def D (x y : ℝ) : ℝ := -H x - x * Real.log y - (1 - x) * Real.log (1 - y)

/-- The channel slope. -/
def k (c d : ℝ) : ℝ := 1 - c - d

/-- Output-one probability at input-one probability `x`. -/
def q (c d x : ℝ) : ℝ := c + k c d * x

/-- All binary input/channel parameters, without a sign normalization on `k`. -/
def Valid (s c d : ℝ) : Prop :=
  s ∈ Set.Icc (0 : ℝ) 1 ∧ c ∈ Set.Icc (0 : ℝ) 1 ∧ d ∈ Set.Icc (0 : ℝ) 1

/-- Both marginal distributions have full support. -/
def Nondegenerate (s c d : ℝ) : Prop :=
  s ∈ Set.Ioo (0 : ℝ) 1 ∧ q c d s ∈ Set.Ioo (0 : ℝ) 1

/-- Mutual information, equation (2.1). -/
def J (s c d : ℝ) : ℝ := H (q c d s) - (1 - s) * H c - s * H d

/-- The set of ratios in equation (2.2), excluding the diagonal `x = s`. -/
def klRatios (s c d : ℝ) : Set ℝ :=
  {r | ∃ x ∈ Set.Icc (0 : ℝ) 1, x ≠ s ∧ r = D (q c d x) (q c d s) / D x s}

/-- Distribution-dependent contraction coefficient, with the paper's zero convention.

Nonemptiness and boundedness of `klRatios` under `Valid` and
`Nondegenerate` are proved in `BinaryInformation.lean`, using binary data processing.
-/
def S (s c d : ℝ) : ℝ := by
  classical
  exact if Nondegenerate s c d then sSup (klRatios s c d) else 0

/-- The sharp upper-bound function from Theorem 2.1. -/
def phi (u : ℝ) : ℝ := Real.log 2 - H ((1 - Real.sqrt u) / 2)

/-- Scalar independence, including deterministic inputs. -/
def Independent (s c d : ℝ) : Prop := s = 0 ∨ s = 1 ∨ c + d = 1

/-- Doubly symmetric binary source; crossover may lie anywhere in `[0,1]`. -/
def DSBS (s c d : ℝ) : Prop := s = 1 / 2 ∧ c = d

/-- An interior reference is required when interpreting this predicate as a KL cap. -/
def KLCap (lam s c d : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, D (q c d x) (q c d s) ≤ lam * D x s

/-- Entropy curve from Section 4. -/
def entropyCurve (lam c d x : ℝ) : ℝ := H (q c d x) - lam * H x

/-- The actual derivative-based tangent line at `s`, not an independently chosen slope. -/
def tangent (lam s c d x : ℝ) : ℝ :=
  entropyCurve lam c d s + deriv (entropyCurve lam c d) s * (x - s)

end Definitions

/-! ## The statement of Theorem 2.1

把主定理的不等式与完整取等条件写成 Lean 命题；这里陈述目标，还没有证明目标。
-/

@[expose] public section Specification

/-- The inequality in Theorem 2.1, for all binary channel parameters. -/
def SharpBound : Prop :=
  ∀ s c d : ℝ, Valid s c d → J s c d ≤ phi (S s c d)

/-- The complete equality statement, including degenerate inputs and relabelings. -/
def EqualityClassification : Prop :=
  ∀ s c d : ℝ, Valid s c d →
    (J s c d = phi (S s c d) ↔ Independent s c d ∨ DSBS s c d)

/-- The inequality and complete equality statement of Theorem 2.1. -/
def MainTheorem : Prop := SharpBound ∧ EqualityClassification

end Specification

/-! ## The entropy formula and the usual Bernoulli KL expression

证明代码中的熵与 KL 公式等于通常的数学表达，并写出熵曲线到切线的差。
-/

public noncomputable section Entropy

/-- Binary entropy written using ordinary natural logarithms. -/
theorem H_eq (x : ℝ) :
    H x = -x * Real.log x - (1 - x) * Real.log (1 - x) := by
  rw [H, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  ring

/-- The cross-entropy definition agrees with the paper's Bernoulli KL formula.

The cases `x = 0` and `x = 1` use the usual zero-mass convention. No claim is
made here about KL divergence with a deterministic reference distribution.
-/
theorem D_eq_log_ratio {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    D x y = x * Real.log (x / y) +
      (1 - x) * Real.log ((1 - x) / (1 - y)) := by
  by_cases hx_zero : x = 0
  · subst x
    simp [D, H, one_div, Real.log_inv]
  by_cases hx_one : x = 1
  · subst x
    simp [D, H, one_div, Real.log_inv]
  have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
  have hx_lt_one : x < 1 := lt_of_le_of_ne hx.2 hx_one
  rw [D, H_eq, Real.log_div (ne_of_gt hx_pos) (ne_of_gt hy.1),
    Real.log_div (ne_of_gt (sub_pos.mpr hx_lt_one)) (ne_of_gt (sub_pos.mpr hy.2))]
  ring

end Entropy

/-! ## Actual derivatives and the complete proof of equation (4.1)

证明论文公式 (4.1)：曲线与切线之间的差，可以写成两个 KL 项的差。
-/

public section TangentGap

lemma q_sub (c d x s : ℝ) : q c d x - q c d s = k c d * (x - s) := by
  unfold q
  ring

lemma hasDerivAt_q (c d s : ℝ) : HasDerivAt (q c d) (k c d) s := by
  convert! ((hasDerivAt_id s).const_mul (k c d)).const_add c using 1
  simp

/-- The slope of binary entropy at an interior probability.
This invokes mathlib's proved derivative formula; it is not an assumption. -/
lemma hasDerivAt_H_log {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt H (Real.log (1 - s) - Real.log s) s :=
  Real.hasDerivAt_binEntropy (ne_of_gt hs.1) (ne_of_lt hs.2)

lemma hasDerivAt_entropyCurve (lam s c d : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (entropyCurve lam c d)
      ((Real.log (1 - q c d s) - Real.log (q c d s)) * k c d -
        lam * (Real.log (1 - s) - Real.log s)) s := by
  have hsH := hasDerivAt_H_log hs
  have hqH := (hasDerivAt_H_log hqs).comp s (hasDerivAt_q c d s)
  convert! hqH.sub (hsH.const_mul lam) using 1

lemma deriv_entropyCurve (lam s c d : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (entropyCurve lam c d) s =
      (Real.log (1 - q c d s) - Real.log (q c d s)) * k c d -
        lam * (Real.log (1 - s) - Real.log s) :=
  (hasDerivAt_entropyCurve lam s c d hs hqs).deriv

/-- The entropy tangent-gap identity underlying equation (4.1).

This algebraic identity also holds for the total real-valued extensions of
`H` and `D`. Interpreting the displayed coefficient as an actual entropy
derivative requires an interior reference, supplied in the tangent theorem.
-/
theorem entropy_tangent_gap (x s : ℝ) :
    H x - H s - (Real.log (1 - s) - Real.log s) * (x - s) = -D x s := by
  rw [D, H_eq s]
  ring

/-- Equation (4.1), with minimal analytic assumptions on the reference marginals.
No sign condition on `lam` or the channel slope is needed for this identity. -/
theorem equation_4_1 (lam s c d x : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    entropyCurve lam c d x - tangent lam s c d x =
      lam * D x s - D (q c d x) (q c d s) := by
  calc
    entropyCurve lam c d x - tangent lam s c d x =
        (H (q c d x) - H (q c d s) -
          (Real.log (1 - q c d s) - Real.log (q c d s)) * (q c d x - q c d s)) -
        lam * (H x - H s - (Real.log (1 - s) - Real.log s) * (x - s)) := by
      rw [tangent, deriv_entropyCurve lam s c d hs hqs, q_sub]
      unfold entropyCurve
      ring
    _ = lam * D x s - D (q c d x) (q c d s) := by
      rw [entropy_tangent_gap, entropy_tangent_gap]
      ring

/-- A valid binary channel maps the probability interval to itself. -/
lemma q_mem_Icc (c d x : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    q c d x ∈ Set.Icc (0 : ℝ) 1 := by
  have hxc := mul_nonneg (sub_nonneg.mpr hx.2) hc.1
  have hxd := mul_nonneg hx.1 (sub_nonneg.mpr hd.2)
  have hxc' := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hc.2)
  have hxd' := mul_nonneg hx.1 hd.1
  dsimp [q, k]
  constructor <;> nlinarith

/-- Equation (4.1) in the paper's original logarithm-of-ratio notation.
This includes both endpoint test inputs, with `0 * log 0 = 0`. -/
theorem equation_4_1_log_ratio (lam s c d x : ℝ)
    (hv : Valid s c d) (hn : Nondegenerate s c d) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    entropyCurve lam c d x - tangent lam s c d x =
      lam * (x * Real.log (x / s) + (1 - x) * Real.log ((1 - x) / (1 - s))) -
        (q c d x * Real.log (q c d x / q c d s) +
          (1 - q c d x) * Real.log ((1 - q c d x) / (1 - q c d s))) := by
  rw [equation_4_1 lam s c d x hn.1 hn.2]
  rw [D_eq_log_ratio hx hn.1, D_eq_log_ratio (q_mem_Icc c d x hv.2.1 hv.2.2 hx) hn.2]

end TangentGap

/-! ## KL positivity and contraction through a binary channel

在明确的概率范围内证明 KL 的正性，以及通过信道后 KL 不会增加。
-/

public section Divergence

@[simp] theorem D_self (x : ℝ) : D x x = 0 := by
  rw [D, H_eq]
  ring

theorem D_pos {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hxy : x ≠ y) : 0 < D x y := by
  have hdy := Real.hasDerivAt_binEntropy (ne_of_gt hy.1) (ne_of_lt hy.2)
  have hyc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  have hid := entropy_tangent_gap x y
  rcases lt_or_gt_of_ne hxy with h | h
  · have hs := Real.strictConcave_binEntropy.lt_slope_of_hasDerivAt hx hyc h hdy
    rw [slope_def_field] at hs
    have ht := (lt_div_iff₀ (sub_pos.mpr h)).mp hs
    dsimp [H] at hid
    nlinarith
  · have hs := Real.strictConcave_binEntropy.slope_lt_of_hasDerivAt hyc hx h hdy
    rw [slope_def_field] at hs
    have ht := (div_lt_iff₀ (sub_pos.mpr h)).mp hs
    dsimp [H] at hid
    linarith

theorem D_nonneg {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : 0 ≤ D x y := by
  by_cases hxy : x = y
  · subst x
    simp
  · exact (D_pos hx hy hxy).le

theorem D_eq_zero_iff {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : D x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    exact (ne_of_gt (D_pos hx hy hxy)) h
  · rintro rfl
    simp

private lemma mul_log_mix_le {a b u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (a * u + b * v) * Real.log (a * u + b * v) ≤
      a * (u * Real.log u) + b * (v * Real.log v) := by
  simpa only [smul_eq_mul] using Real.convexOn_mul_log.2 hu hv ha hb hab

/-- Binary data processing, including zero transition probabilities and endpoint test inputs. -/
theorem D_dataProcessing {s c d x : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hqs : q c d s ∈ Set.Ioo (0 : ℝ) 1) :
    D (q c d x) (q c d s) ≤ D x s := by
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have hs1 : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs.2)
  have hq0 : q c d s ≠ 0 := ne_of_gt hqs.1
  have hq1 : 1 - q c d s ≠ 0 := ne_of_gt (sub_pos.mpr hqs.2)
  have hu : 0 ≤ (1 - x) / (1 - s) := div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hs.2).le
  have hv : 0 ≤ x / s := div_nonneg hx.1 hs.1.le
  have hsum1 : (1 - s) * c / q c d s + s * (1 - d) / q c d s = 1 := by
    field_simp
    dsimp [q, k]
    ring
  have havg1 : (1 - s) * c / q c d s * ((1 - x) / (1 - s)) +
      s * (1 - d) / q c d s * (x / s) = q c d x / q c d s := by
    field_simp
    dsimp [q, k]
    ring
  have hsum0 : (1 - s) * (1 - c) / (1 - q c d s) + s * d / (1 - q c d s) = 1 := by
    field_simp
    dsimp [q, k]
    ring
  have havg0 : (1 - s) * (1 - c) / (1 - q c d s) * ((1 - x) / (1 - s)) +
      s * d / (1 - q c d s) * (x / s) = (1 - q c d x) / (1 - q c d s) := by
    field_simp
    dsimp [q, k]
    ring
  have j1 := mul_log_mix_le
    (div_nonneg (mul_nonneg (sub_pos.mpr hs.2).le hc.1) hqs.1.le)
    (div_nonneg (mul_nonneg hs.1.le (sub_nonneg.mpr hd.2)) hqs.1.le) hsum1 hu hv
  rw [havg1] at j1
  have j0 := mul_log_mix_le
    (div_nonneg (mul_nonneg (sub_pos.mpr hs.2).le (sub_nonneg.mpr hc.2))
      (sub_pos.mpr hqs.2).le)
    (div_nonneg (mul_nonneg hs.1.le hd.1) (sub_pos.mpr hqs.2).le) hsum0 hu hv
  rw [havg0] at j0
  have h1 := mul_le_mul_of_nonneg_left j1 hqs.1.le
  have h0 := mul_le_mul_of_nonneg_left j0 (sub_pos.mpr hqs.2).le
  have e1 : q c d s *
      ((1 - s) * c / q c d s * ((1 - x) / (1 - s) * Real.log ((1 - x) / (1 - s))) +
       s * (1 - d) / q c d s * (x / s * Real.log (x / s))) =
      c * (1 - x) * Real.log ((1 - x) / (1 - s)) + (1 - d) * x * Real.log (x / s) := by
    field_simp
  have e0 : (1 - q c d s) *
      ((1 - s) * (1 - c) / (1 - q c d s) *
        ((1 - x) / (1 - s) * Real.log ((1 - x) / (1 - s))) +
       s * d / (1 - q c d s) * (x / s * Real.log (x / s))) =
      (1 - c) * (1 - x) * Real.log ((1 - x) / (1 - s)) + d * x * Real.log (x / s) := by
    field_simp
  rw [e1] at h1
  rw [e0] at h0
  have eq1 : q c d s * (q c d x / q c d s * Real.log (q c d x / q c d s)) =
      q c d x * Real.log (q c d x / q c d s) := by field_simp
  have eq0 : (1 - q c d s) * ((1 - q c d x) / (1 - q c d s) *
      Real.log ((1 - q c d x) / (1 - q c d s))) =
      (1 - q c d x) * Real.log ((1 - q c d x) / (1 - q c d s)) := by field_simp
  rw [eq1] at h1
  rw [eq0] at h0
  rw [D_eq_log_ratio (q_mem_Icc c d x hc hd hx) hqs, D_eq_log_ratio hx hs]
  nlinarith

end Divergence

/-! ## Derivatives of the KL expression

计算概率位于 0 与 1 之间时 KL 对各个参数的导数。
-/

@[expose] public noncomputable section DivergenceCalculus

/-- Log odds on the interior probability interval, with a total real extension. -/
def logOdds (x : ℝ) : ℝ := Real.log x - Real.log (1 - x)

theorem logOdds_strictMonoOn : StrictMonoOn logOdds (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have h1 := Real.log_lt_log hx.1 hxy
  have h2 := Real.log_lt_log (sub_pos.mpr hy.2) (show 1 - y < 1 - x by linarith)
  unfold logOdds
  linarith

theorem hasDerivAt_logOdds {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt logOdds (1 / (x * (1 - x))) x := by
  have h := (hasDerivAt_id x).log (ne_of_gt hx.1)
  have h' := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt (sub_pos.mpr hx.2))
  convert! h.sub h' using 1
  simp only [id_eq]
  field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
  ring

/-- Chain rule when both Bernoulli parameters vary along a real curve. -/
theorem hasDerivAt_D_comp {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hft : f t ∈ Set.Ioo (0 : ℝ) 1) (hgt : g t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => D (f z) (g z))
      (f' * (logOdds (f t) - logOdds (g t)) +
        g' * (g t - f t) / (g t * (1 - g t))) t := by
  have hH := (Real.hasDerivAt_binEntropy (ne_of_gt hft.1) (ne_of_lt hft.2)).comp t hf
  have hlg := hg.log (ne_of_gt hgt.1)
  have hl1g := (hg.const_sub 1).log (ne_of_gt (sub_pos.mpr hgt.2))
  have h := (hH.neg.sub (hf.mul hlg)).sub ((hf.const_sub 1).mul hl1g)
  convert! h using 1
  unfold logOdds
  field_simp [ne_of_gt hgt.1, ne_of_gt (sub_pos.mpr hgt.2)]
  ring

theorem hasDerivAt_D_left {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => D z y) (logOdds x - logOdds y) x := by
  simpa only [id_eq, one_mul, zero_mul, zero_div, add_zero] using
    (hasDerivAt_D_comp (hasDerivAt_id x) (hasDerivAt_const x y) hx hy)

theorem hasDerivAt_D_right {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => D x z) ((y - x) / (y * (1 - y))) y := by
  simpa only [id_eq, one_mul, zero_mul, zero_add] using
    (hasDerivAt_D_comp (hasDerivAt_const y x) (hasDerivAt_id y) hx hy)

end DivergenceCalculus

/-! ## The coefficient S and its equivalent KL and tangent constraints

证明 S 确实位于 0 与 1 之间，并把系数上界改写为对所有测试输入都成立的 KL 不等式和支撑切线条件。
-/

public section Contraction

lemma klRatios_nonempty {s c d : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (klRatios s c d).Nonempty := by
  refine ⟨D (q c d 0) (q c d s) / D 0 s, 0, ?_, ne_of_lt hs.1, rfl⟩
  exact ⟨le_rfl, zero_le_one⟩

lemma S_eq_sSup {s c d : ℝ} (hn : Nondegenerate s c d) :
    S s c d = sSup (klRatios s c d) := by
  simp [S, hn]

lemma S_eq_zero_of_not_nondegenerate {s c d : ℝ} (hn : ¬Nondegenerate s c d) :
    S s c d = 0 := by
  simp [S, hn]

lemma ratio_le_S_of_bddAbove {s c d x : ℝ}
    (hn : Nondegenerate s c d) (hb : BddAbove (klRatios s c d))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxs : x ≠ s) :
    D (q c d x) (q c d s) / D x s ≤ S s c d := by
  rw [S_eq_sSup hn]
  exact le_csSup hb ⟨x, hx, hxs, rfl⟩

lemma S_le_iff_ratios_le_of_bddAbove {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hb : BddAbove (klRatios s c d)) :
    S s c d ≤ lam ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ s →
        D (q c d x) (q c d s) / D x s ≤ lam := by
  rw [S_eq_sSup hn, csSup_le_iff hb (klRatios_nonempty hn.1)]
  constructor
  · intro h x hx hxs
    exact h _ ⟨x, hx, hxs, rfl⟩
  · rintro h r ⟨x, hx, hxs, rfl⟩
    exact h x hx hxs

lemma klRatios_bddAbove_of_klCap {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hcap : KLCap lam s c d) :
    BddAbove (klRatios s c d) := by
  refine ⟨lam, ?_⟩
  rintro r ⟨x, hx, hxs, rfl⟩
  exact (div_le_iff₀ (D_pos hx hn.1 hxs)).2 (hcap x hx)

lemma S_le_of_klCap {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hcap : KLCap lam s c d) :
    S s c d ≤ lam := by
  rw [S_eq_sSup hn]
  apply csSup_le (klRatios_nonempty hn.1)
  rintro r ⟨x, hx, hxs, rfl⟩
  exact (div_le_iff₀ (D_pos hx hn.1 hxs)).2 (hcap x hx)

lemma S_le_iff_klCap_of_bddAbove {lam s c d : ℝ}
    (hn : Nondegenerate s c d) (hb : BddAbove (klRatios s c d)) :
    S s c d ≤ lam ↔ KLCap lam s c d := by
  constructor
  · intro h x hx
    by_cases hxs : x = s
    · subst x
      simp only [D_self, mul_zero, le_refl]
    · apply (div_le_iff₀ (D_pos hx hn.1 hxs)).1
      exact (ratio_le_S_of_bddAbove hn hb hx hxs).trans h
  · exact S_le_of_klCap hn

lemma klCap_one {s c d : ℝ} (hv : Valid s c d) (hn : Nondegenerate s c d) :
    KLCap 1 s c d := by
  intro x hx
  simpa only [one_mul] using D_dataProcessing hv.2.1 hv.2.2 hx hn.1 hn.2

/-- The ratio set has the genuine upper bound `1`, by binary data processing. -/
theorem klRatios_bddAbove {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) : BddAbove (klRatios s c d) :=
  klRatios_bddAbove_of_klCap hn (klCap_one hv hn)

theorem S_nonneg {s c d : ℝ} (hv : Valid s c d) : 0 ≤ S s c d := by
  by_cases hn : Nondegenerate s c d
  · rw [S_eq_sSup hn]
    apply Real.sSup_nonneg
    rintro r ⟨x, hx, hxs, rfl⟩
    exact div_nonneg (D_nonneg (q_mem_Icc c d x hv.2.1 hv.2.2 hx) hn.2)
      (D_nonneg hx hn.1)
  · rw [S_eq_zero_of_not_nondegenerate hn]

theorem S_le_one {s c d : ℝ} (hv : Valid s c d) : S s c d ≤ 1 := by
  by_cases hn : Nondegenerate s c d
  · exact S_le_of_klCap hn (klCap_one hv hn)
  · rw [S_eq_zero_of_not_nondegenerate hn]
    exact zero_le_one

theorem S_mem_Icc {s c d : ℝ} (hv : Valid s c d) : S s c d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨S_nonneg hv, S_le_one hv⟩

theorem ratio_le_S {s c d x : ℝ} (hv : Valid s c d) (hn : Nondegenerate s c d)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxs : x ≠ s) :
    D (q c d x) (q c d s) / D x s ≤ S s c d :=
  ratio_le_S_of_bddAbove hn (klRatios_bddAbove hv hn) hx hxs

/-- The exact supremum coefficient is at most a cap iff every test input
satisfies its KL inequality. There is no assumed bound on the supremum. -/
theorem S_le_iff_klCap {lam s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) : S s c d ≤ lam ↔ KLCap lam s c d :=
  S_le_iff_klCap_of_bddAbove hn (klRatios_bddAbove hv hn)

theorem klCap_S {s c d : ℝ} (hv : Valid s c d) (hn : Nondegenerate s c d) :
    KLCap (S s c d) s c d :=
  (S_le_iff_klCap hv hn).1 le_rfl

/-- Independent inputs have zero coefficient, including deterministic inputs. -/
theorem S_eq_zero_of_independent {s c d : ℝ} (hi : Independent s c d) :
    S s c d = 0 := by
  rcases hi with hs | hs | hcd
  · subst s
    simp [S, Nondegenerate]
  · subst s
    simp [S, Nondegenerate]
  · by_cases hn : Nondegenerate s c d
    · have hk : k c d = 0 := by unfold k; linarith
      have hr : klRatios s c d = {0} := by
        ext r
        constructor
        · rintro ⟨x, hx, hxs, rfl⟩
          simp [q, hk]
        · intro hr
          have hr0 : r = 0 := hr
          subst r
          refine ⟨0, ⟨le_rfl, zero_le_one⟩, ne_of_lt hn.1.1, ?_⟩
          simp [q, hk]
      rw [S_eq_sSup hn, hr]
      simp
    · exact S_eq_zero_of_not_nondegenerate hn

/-- The universal KL inequality is exactly the lower-supporting tangent
condition. This part does not need a sign restriction on the cap. -/
theorem klCap_iff_supporting_tangent {lam s c d : ℝ}
    (hn : Nondegenerate s c d) :
    KLCap lam s c d ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, tangent lam s c d x ≤ entropyCurve lam c d x := by
  constructor
  · intro h x hx
    have hcap := h x hx
    have hgap := equation_4_1 lam s c d x hn.1 hn.2
    linarith
  · intro h x hx
    have hsupp := h x hx
    have hgap := equation_4_1 lam s c d x hn.1 hn.2
    linarith

/-- Section 4.1: the distribution-dependent contraction cap is equivalent
to the tangent being lower supporting on the entire probability interval. -/
theorem S_le_iff_supporting_tangent {lam s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) :
    S s c d ≤ lam ↔
      ∀ x ∈ Set.Icc (0 : ℝ) 1, tangent lam s c d x ≤ entropyCurve lam c d x :=
  (S_le_iff_klCap hv hn).trans (klCap_iff_supporting_tangent hn)

end Contraction

/-! ## The entropy of a two-cell probability row -/

@[expose] public noncomputable section BinaryMassEntropy

/-- The entropy of a two-cell row, without any full-support assumption. -/
theorem binary_mass_entropy {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * H (b / (a + b)) =
      Real.negMulLog a + Real.negMulLog b - Real.negMulLog (a + b) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, H]
  have h1 : (a + b) * (b / (a + b)) = b := by field_simp
  have h2 : (a + b) * (1 - b / (a + b)) = a := by field_simp; ring
  have e1 := Real.negMulLog_mul (a + b) (b / (a + b))
  have e2 := Real.negMulLog_mul (a + b) (1 - b / (a + b))
  rw [h1] at e1
  rw [h2] at e2
  rw [H, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  nlinarith

end BinaryMassEntropy

end BinaryPairBound
