module

public import BinaryPairBound.BinaryInformation
public import BinaryPairBound.ChannelGeometry
public import BinaryPairBound.MaximizerExistence
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of the exact KL coefficient

求出KL比值的对角线极限，并证明输入、信道一起变化时真实系数的连续性。

Read the sections below in order: they develop one mathematical goal in this file.
All theorem names and mathematical statements from the original development are retained.
-/

namespace BinaryPairBound

/-! ## The diagonal KL limit and attainment of the extended ratio

求出 KL 比值在测试输入趋近原输入时的极限，并用它补上比值的对角线取值。
-/

@[expose] public noncomputable section RatioContinuity

open Filter Set
open scoped Topology

lemma continuous_D_left (y : ℝ) : Continuous (fun x : ℝ => D x y) := by
  unfold D
  fun_prop

/-- Equation (4.2), as a two-sided punctured limit of the actual KL ratios. -/
theorem tendsto_klRatio_nhdsNE {s c d : ℝ} (hn : Nondegenerate s c d) :
    Tendsto (fun x => D (q c d x) (q c d s) / D x s)
      (nhdsWithin s {s}ᶜ) (nhds (rhoSquared c d s)) := by
  let f1 : ℝ → ℝ := fun x => k c d * (logOdds (q c d x) - logOdds (q c d s))
  let g1 : ℝ → ℝ := fun x => logOdds x - logOdds s
  let f2 : ℝ → ℝ := fun x => (k c d)^2 / (q c d x * (1 - q c d x))
  let g2 : ℝ → ℝ := fun x => 1 / (x * (1 - x))
  have hi : ∀ᶠ x in nhds s, x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hn.1.1 hn.1.2
  have ho : ∀ᶠ x in nhds s, q c d x ∈ Ioo (0 : ℝ) 1 :=
    (hasDerivAt_q c d s).continuousAt (Ioo_mem_nhds hn.2.1 hn.2.2)
  have hf12 : ∀ᶠ x in nhds s, HasDerivAt f1 (f2 x) x := by
    filter_upwards [ho] with x hx
    have h := (((hasDerivAt_logOdds hx).comp x (hasDerivAt_q c d x)).sub_const
      (logOdds (q c d s))).const_mul (k c d)
    convert! h using 1
    dsimp [f2]
    ring
  have hg12 : ∀ᶠ x in nhds s, HasDerivAt g1 (g2 x) x := by
    filter_upwards [hi] with x hx
    exact (hasDerivAt_logOdds hx).sub_const (logOdds s)
  have hg2ne : ∀ᶠ x in nhds s, g2 x ≠ 0 := by
    filter_upwards [hi] with x hx
    exact div_ne_zero one_ne_zero (mul_ne_zero (ne_of_gt hx.1) (ne_of_gt (sub_pos.mpr hx.2)))
  have hf1zero : Tendsto f1 (nhds s) (nhds 0) := by
    have h := (((hasDerivAt_logOdds hn.2).comp s (hasDerivAt_q c d s)).sub_const
      (logOdds (q c d s))).const_mul (k c d)
    simpa [f1] using h.continuousAt.tendsto
  have hg1zero : Tendsto g1 (nhds s) (nhds 0) := by
    have h := (hasDerivAt_logOdds hn.1).sub_const (logOdds s)
    simpa [g1] using h.continuousAt.tendsto
  have hquot2 : Tendsto (fun x => f2 x / g2 x) (nhds s) (nhds (rhoSquared c d s)) := by
    convert (continuousAt_rhoSquared hn.2).tendsto using 1
    funext x
    dsimp [f2, g2, rhoSquared]
    simp only [div_eq_mul_inv, inv_inv, one_mul]
    ring
  have hquot1 := HasDerivAt.lhopital_zero_nhds hf12 hg12 hg2ne hf1zero hg1zero hquot2
  have hf01 : ∀ᶠ x in nhdsWithin s {s}ᶜ,
      HasDerivAt (fun x => D (q c d x) (q c d s)) (f1 x) x := by
    filter_upwards [ho.filter_mono nhdsWithin_le_nhds] with x hx
    convert! (hasDerivAt_D_left hx hn.2).comp x (hasDerivAt_q c d x) using 1
    dsimp [f1]
    ring
  have hg01 : ∀ᶠ x in nhdsWithin s {s}ᶜ, HasDerivAt (fun x => D x s) (g1 x) x := by
    filter_upwards [hi.filter_mono nhdsWithin_le_nhds] with x hx
    exact hasDerivAt_D_left hx hn.1
  have hg1ne : ∀ᶠ x in nhdsWithin s {s}ᶜ, g1 x ≠ 0 := by
    filter_upwards [hi.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxs
    change logOdds x - logOdds s ≠ 0
    exact sub_ne_zero.mpr (fun heq => hxs (logOdds_strictMonoOn.injOn hx hn.1 heq))
  have hf0 : Tendsto (fun x => D (q c d x) (q c d s))
      (nhdsWithin s {s}ᶜ) (nhds 0) := by
    have h := (continuous_D_left (q c d s)).continuousAt.comp (hasDerivAt_q c d s).continuousAt
    convert! h.tendsto.mono_left
      (show nhdsWithin s {s}ᶜ ≤ nhds s from nhdsWithin_le_nhds) using 1
    simp only [Function.comp_apply, D_self]
  have hg0 : Tendsto (fun x => D x s) (nhdsWithin s {s}ᶜ) (nhds 0) := by
    have h : ContinuousAt (fun x => D x s) s := (continuous_D_left s).continuousAt
    simpa only [D_self] using
      h.tendsto.mono_left (show nhdsWithin s {s}ᶜ ≤ nhds s from nhdsWithin_le_nhds)
  exact HasDerivAt.lhopital_zero_nhdsNE hf01 hg01 hg1ne hf0 hg0 hquot1

/-- The KL ratio with its proved removable singularity filled in. -/
def extendedRatio (s c d x : ℝ) : ℝ :=
  if x = s then rhoSquared c d s else D (q c d x) (q c d s) / D x s

@[simp] theorem extendedRatio_self (s c d : ℝ) :
    extendedRatio s c d s = rhoSquared c d s := by simp [extendedRatio]

theorem extendedRatio_of_ne {s c d x : ℝ} (hxs : x ≠ s) :
    extendedRatio s c d x = D (q c d x) (q c d s) / D x s := by
  simp [extendedRatio, hxs]

theorem continuousAt_extendedRatio_self {s c d : ℝ} (hn : Nondegenerate s c d) :
    ContinuousAt (extendedRatio s c d) s := by
  rw [continuousAt_iff_punctured_nhds, extendedRatio_self]
  have heq : extendedRatio s c d =ᶠ[nhdsWithin s {s}ᶜ]
      (fun x => D (q c d x) (q c d s) / D x s) := by
    filter_upwards [self_mem_nhdsWithin] with x hxs
    exact extendedRatio_of_ne hxs
  exact (tendsto_congr' heq).2 (tendsto_klRatio_nhdsNE hn)

/-- For a fixed nondegenerate reference, the diagonal extension is continuous
at every probability input, including both endpoints. -/
theorem continuousAt_extendedRatio {s c d x : ℝ} (hn : Nondegenerate s c d)
    (hx : x ∈ Icc (0 : ℝ) 1) : ContinuousAt (extendedRatio s c d) x := by
  by_cases hxs : x = s
  · subst x
    exact continuousAt_extendedRatio_self hn
  · have hnum : ContinuousAt (fun x => D (q c d x) (q c d s)) x := by
      convert! (continuous_D_left (q c d s)).continuousAt.comp
        (hasDerivAt_q c d x).continuousAt using 1
    have hden : ContinuousAt (fun x => D x s) x := (continuous_D_left s).continuousAt
    apply (hnum.div hden (ne_of_gt (D_pos hx hn.1 hxs))).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hxs] with y hys
    exact extendedRatio_of_ne hys

theorem continuousOn_extendedRatio {s c d : ℝ} (hn : Nondegenerate s c d) :
    ContinuousOn (extendedRatio s c d) (Icc (0 : ℝ) 1) := by
  intro x hx
  exact (continuousAt_extendedRatio hn hx).continuousWithinAt

theorem extendedRatio_le_S {s c d x : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) (hx : x ∈ Icc (0 : ℝ) 1) :
    extendedRatio s c d x ≤ S s c d := by
  by_cases hxs : x = s
  · subst x
    rw [extendedRatio_self]
    exact rhoSquared_le_S hv hn
  · rw [extendedRatio_of_ne hxs]
    exact ratio_le_S hv hn hx hxs

/-- The supremum in (2.2) is an attained maximum after filling in the diagonal. -/
theorem exists_extendedRatio_eq_S {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) :
    ∃ x ∈ Icc (0 : ℝ) 1, extendedRatio s c d x = S s c d := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, le_rfl, zero_le_one⟩)
    (continuousOn_extendedRatio hn)
  refine ⟨x, hx, le_antisymm (extendedRatio_le_S hv hn hx) ?_⟩
  rw [S_eq_sSup hn]
  apply csSup_le (klRatios_nonempty hn.1)
  rintro r ⟨y, hy, hys, rfl⟩
  rw [← extendedRatio_of_ne (c := c) (d := d) hys]
  exact hmax hy

/-- Section 4.2: the channel-wide coefficient is attained at exactly the
distinguished input. Compactness rules out a strict but unattained supremum. -/
theorem S_eq_eta_iff {s c d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1) :
    S s c d = eta c d ↔ s = distinguishedInput c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  constructor
  · intro heq
    obtain ⟨x, hx, hmax⟩ := exists_extendedRatio_eq_S hv hn
    by_cases hxs : x = s
    · subst x
      rw [extendedRatio_self, heq] at hmax
      exact (rhoSquared_eq_eta_iff hc hd hcd hn.2).1 hmax
    · rw [extendedRatio_of_ne hxs, heq] at hmax
      exact False.elim ((ne_of_lt (ratio_lt_eta hs hc hd hcd hx hxs)) hmax)
  · intro heq
    subst s
    exact S_distinguishedInput_eq_eta hc hd hcd

theorem S_lt_eta_of_ne_distinguishedInput {s c d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hne : s ≠ distinguishedInput c d) : S s c d < eta c d :=
  lt_of_le_of_ne (S_le_eta ⟨hs.1.le, hs.2.le⟩ hc hd)
    (fun heq => hne ((S_eq_eta_iff hs hc hd hcd).1 heq))

/-- Away from the distinguished input, a distinct test input actually attains
the KL supremum. Endpoint exclusion is a separate contact-geometry result. -/
theorem exists_testInput_eq_S {s c d : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1) (hcd : c + d ≠ 1)
    (hne : s ≠ distinguishedInput c d) :
    ∃ x ∈ Icc (0 : ℝ) 1, x ≠ s ∧
      D (q c d x) (q c d s) / D x s = S s c d := by
  have hv : Valid s c d := ⟨⟨hs.1.le, hs.2.le⟩, ⟨hc.1.le, hc.2.le⟩, ⟨hd.1.le, hd.2.le⟩⟩
  have hn : Nondegenerate s c d := ⟨hs, q_mem_Ioo_of_channel hc hd hv.1⟩
  obtain ⟨x, hx, heq⟩ := exists_extendedRatio_eq_S hv hn
  have hxs : x ≠ s := by
    intro hxs
    subst x
    rw [extendedRatio_self] at heq
    exact (ne_of_lt (rhoSquared_lt_S hs hc hd hcd hne)) heq
  exact ⟨x, hx, hxs, (extendedRatio_of_ne hxs).symm.trans heq⟩

end RatioContinuity

/-! ## Continuity when input and channel vary together

证明输入和信道一起变化时，补全后的比值及非退化区域内的系数连续变化。
-/

@[expose] public noncomputable section JointRatioContinuity

open Filter Set
open scoped Topology

private lemma exists_zero_uIcc {f f' : ℝ → ℝ} {a b : ℝ} (hne : a ≠ b)
    (hc : ContinuousOn f (uIcc a b)) (heq : f a = f b)
    (hd : ∀ y ∈ uIcc a b, HasDerivAt f (f' y) y) :
    ∃ y ∈ uIcc a b, y ≠ a ∧ f' y = 0 := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨y, hy, hz⟩ := exists_hasDerivAt_eq_zero hab
      (by simpa [uIcc_of_le hab.le] using hc) heq
      (fun y hy => hd y (mem_uIcc_of_le hy.1.le hy.2.le))
    exact ⟨y, mem_uIcc_of_le hy.1.le hy.2.le, ne_of_gt hy.1, hz⟩
  · obtain ⟨y, hy, hz⟩ := exists_hasDerivAt_eq_zero hba
      (by simpa [uIcc_of_ge hba.le] using hc) heq.symm
      (fun y hy => hd y (mem_uIcc_of_ge hy.1.le hy.2.le))
    exact ⟨y, mem_uIcc_of_ge hy.1.le hy.2.le, ne_of_lt hy.2, hz⟩

/-- A twofold Rolle argument represents the KL ratio by the local squared
correlation at an intermediate input. This also includes the filled diagonal. -/
theorem exists_extendedRatio_eq_rhoSquared {s c d x : ℝ}
    (hi : uIcc s x ⊆ Ioo (0 : ℝ) 1)
    (ho : ∀ y ∈ uIcc s x, q c d y ∈ Ioo (0 : ℝ) 1) :
    ∃ y ∈ uIcc s x, extendedRatio s c d x = rhoSquared c d y := by
  by_cases hxs : x = s
  · subst x
    exact ⟨s, left_mem_uIcc, extendedRatio_self s c d⟩
  let r := extendedRatio s c d x
  let f := entropyCurve r c d
  let g : ℝ → ℝ := fun y => f y - (f s + deriv f s * (y - s))
  let g' : ℝ → ℝ := fun y => deriv f y - deriv f s
  let g'' : ℝ → ℝ := fun y => (r - rhoSquared c d y) / (y * (1 - y))
  have hs := hi left_mem_uIcc
  have hqs := ho s left_mem_uIcc
  have hx := hi right_mem_uIcc
  have hg : ∀ y ∈ uIcc s x, HasDerivAt g (g' y) y := by
    intro y hy
    have hf := (hasDerivAt_entropyCurve r y c d (hi hy) (ho y hy)).differentiableAt.hasDerivAt
    convert! hf.sub (((hasDerivAt_id y).sub_const s).const_mul (deriv f s) |>.const_add (f s)) using 1
    simp only [g', f, mul_one]
  have hg' : ∀ y ∈ uIcc s x, HasDerivAt g' (g'' y) y := by
    intro y hy
    exact (hasDerivAt_deriv_entropyCurve (lam := r) (hi hy) (ho y hy)).sub_const (deriv f s)
  have hgzero : g s = 0 := by simp [g]
  have hg'zero : g' s = 0 := by simp [g']
  have hgxeq : g x = 0 := by
    change entropyCurve r c d x - tangent r s c d x = 0
    rw [equation_4_1 r s c d x hs hqs]
    dsimp [r]
    rw [extendedRatio_of_ne hxs, div_mul_cancel₀ _ (ne_of_gt (D_pos ⟨hx.1.le, hx.2.le⟩ hs hxs))]
    exact sub_self _
  obtain ⟨v, hv, hvs, hvzero⟩ := exists_zero_uIcc (Ne.symm hxs)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt) (hgzero.trans hgxeq.symm) hg
  have hvsub : uIcc s v ⊆ uIcc s x := uIcc_subset_uIcc_left hv
  obtain ⟨y, hy, _, hyzero⟩ := exists_zero_uIcc hvs.symm
    (fun y hy => (hg' y (hvsub hy)).continuousAt.continuousWithinAt)
    (hg'zero.trans hvzero.symm) (fun y hy => hg' y (hvsub hy))
  refine ⟨y, hvsub hy, ?_⟩
  have hyi := hi (hvsub hy)
  have hden : y * (1 - y) ≠ 0 := mul_ne_zero (ne_of_gt hyi.1) (ne_of_gt (sub_pos.mpr hyi.2))
  exact sub_eq_zero.mp ((div_eq_zero_iff).mp hyzero |>.resolve_right hden)

lemma q_mem_uIcc {s c d x y : ℝ} (hy : y ∈ uIcc s x) :
    q c d y ∈ uIcc (q c d s) (q c d x) := by
  by_cases hk : 0 ≤ k c d
  · have hm : Monotone (q c d) := by
      intro a b hab
      change c + k c d * a ≤ c + k c d * b
      linarith [mul_le_mul_of_nonneg_left hab hk]
    exact hm.mapsTo_uIcc hy
  · have hm : Antitone (q c d) := by
      intro a b hab
      change c + k c d * b ≤ c + k c d * a
      linarith [mul_le_mul_of_nonpos_left hab (le_of_not_ge hk)]
    exact hm.mapsTo_uIcc hy

lemma continuousAt_q_comp {α : Type*} [TopologicalSpace α]
    {c d x : α → ℝ} {a : α}
    (hc : ContinuousAt c a) (hd : ContinuousAt d a) (hx : ContinuousAt x a) :
    ContinuousAt (fun t => q (c t) (d t) (x t)) a := by
  exact hc.add (((continuousAt_const.sub hc).sub hd).mul hx)

lemma tendsto_rhoSquared_comp {α : Type*} {l : Filter α}
    {c d x : α → ℝ} {c₀ d₀ x₀ : ℝ}
    (hc : Tendsto c l (nhds c₀)) (hd : Tendsto d l (nhds d₀))
    (hx : Tendsto x l (nhds x₀)) (hqx : q c₀ d₀ x₀ ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun t => rhoSquared (c t) (d t) (x t)) l (nhds (rhoSquared c₀ d₀ x₀)) := by
  have hk : Tendsto (fun t => k (c t) (d t)) l (nhds (k c₀ d₀)) :=
    (tendsto_const_nhds.sub hc).sub hd
  have hq := hc.add (hk.mul hx)
  exact (((hk.pow 2).mul hx).mul (tendsto_const_nhds.sub hx)).div
    (hq.mul (tendsto_const_nhds.sub hq))
    (mul_ne_zero (ne_of_gt hqx.1) (ne_of_gt (sub_pos.mpr hqx.2)))

/-- Joint continuity on the diagonal, allowing all three source/channel
parameters and the test input to vary simultaneously. -/
theorem continuousAt_extendedRatio_comp_self {α : Type*} [TopologicalSpace α]
    {s c d x : α → ℝ} {a : α}
    (hs : ContinuousAt s a) (hc : ContinuousAt c a) (hd : ContinuousAt d a)
    (hx : ContinuousAt x a) (hn : Nondegenerate (s a) (c a) (d a))
    (hdiag : x a = s a) :
    ContinuousAt (fun t => extendedRatio (s t) (c t) (d t) (x t)) a := by
  classical
  let P (t : α) := ∃ y ∈ uIcc (s t) (x t),
    extendedRatio (s t) (c t) (d t) (x t) = rhoSquared (c t) (d t) y
  let y (t : α) := if h : P t then h.choose else s t
  have hymem : ∀ t, y t ∈ uIcc (s t) (x t) := by
    intro t
    by_cases h : P t
    · simpa [y, h] using h.choose_spec.1
    · simp [y, h]
  have hy : Tendsto y (nhds a) (nhds (s a)) := by
    have hmin : Tendsto (fun t => min (s t) (x t)) (nhds a) (nhds (s a)) := by
      simpa [hdiag] using hs.tendsto.min hx.tendsto
    have hmax : Tendsto (fun t => max (s t) (x t)) (nhds a) (nhds (s a)) := by
      simpa [hdiag] using hs.tendsto.max hx.tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hmin hmax
      (fun t => (hymem t).1) (fun t => (hymem t).2)
  have hxa : x a ∈ Ioo (0 : ℝ) 1 := by simpa [hdiag] using hn.1
  have hei : ∀ᶠ t in nhds a, s t ∈ Ioo (0 : ℝ) 1 ∧ x t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [hs (Ioo_mem_nhds hn.1.1 hn.1.2), hx (Ioo_mem_nhds hxa.1 hxa.2)] with t ht ht'
    exact ⟨ht, ht'⟩
  have heo : ∀ᶠ t in nhds a,
      q (c t) (d t) (s t) ∈ Ioo (0 : ℝ) 1 ∧ q (c t) (d t) (x t) ∈ Ioo (0 : ℝ) 1 := by
    have hqx : q (c a) (d a) (x a) ∈ Ioo (0 : ℝ) 1 := by simpa [hdiag] using hn.2
    filter_upwards [(continuousAt_q_comp hc hd hs) (Ioo_mem_nhds hn.2.1 hn.2.2),
      (continuousAt_q_comp hc hd hx) (Ioo_mem_nhds hqx.1 hqx.2)] with t ht ht'
    exact ⟨ht, ht'⟩
  have heq : (fun t => extendedRatio (s t) (c t) (d t) (x t)) =ᶠ[nhds a]
      (fun t => rhoSquared (c t) (d t) (y t)) := by
    filter_upwards [hei, heo] with t hi ho
    have hp : P t := exists_extendedRatio_eq_rhoSquared
      (ordConnected_Ioo.uIcc_subset hi.1 hi.2)
      (fun z hz => ordConnected_Ioo.uIcc_subset ho.1 ho.2 (q_mem_uIcc hz))
    simpa only [y, dite_eq_left hp] using hp.choose_spec.2
  change Tendsto _ (nhds a) (nhds (extendedRatio (s a) (c a) (d a) (x a)))
  rw [hdiag, extendedRatio_self]
  exact (tendsto_congr' heq).2 (tendsto_rhoSquared_comp hc.tendsto hd.tendsto hy hn.2)

/-- Joint continuity of the extended ratio at every probability test input.
The source marginal and its channel image must be nondegenerate. -/
theorem continuousAt_extendedRatio_comp {α : Type*} [TopologicalSpace α]
    {s c d x : α → ℝ} {a : α}
    (hs : ContinuousAt s a) (hc : ContinuousAt c a) (hd : ContinuousAt d a)
    (hx : ContinuousAt x a) (hn : Nondegenerate (s a) (c a) (d a))
    (hxa : x a ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun t => extendedRatio (s t) (c t) (d t) (x t)) a := by
  by_cases hdiag : x a = s a
  · exact continuousAt_extendedRatio_comp_self hs hc hd hx hn hdiag
  · have hnum := continuousAt_D_comp (continuousAt_q_comp hc hd hx)
      (continuousAt_q_comp hc hd hs) hn.2
    have hden := continuousAt_D_comp hx hs hn.1
    apply (hnum.div hden (ne_of_gt (D_pos hxa hn.1 hdiag))).congr_of_eventuallyEq
    filter_upwards [(hx.sub hs).eventually (eventually_ne_nhds (sub_ne_zero.mpr hdiag))] with t ht
    exact extendedRatio_of_ne (sub_ne_zero.mp ht)

lemma S_eq_sSup_range_extendedRatio {s c d : ℝ} (hv : Valid s c d)
    (hn : Nondegenerate s c d) :
    S s c d = sSup (range (fun x : Icc (0 : ℝ) 1 => extendedRatio s c d x)) := by
  have hb : BddAbove (range (fun x : Icc (0 : ℝ) 1 => extendedRatio s c d x)) := by
    refine ⟨S s c d, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact extendedRatio_le_S hv hn x.property
  apply le_antisymm
  · obtain ⟨x, hx, heq⟩ := exists_extendedRatio_eq_S hv hn
    rw [← heq]
    exact le_csSup hb ⟨⟨x, hx⟩, rfl⟩
  · apply csSup_le (range_nonempty (fun x : Icc (0 : ℝ) 1 => extendedRatio s c d x))
    rintro _ ⟨x, rfl⟩
    exact extendedRatio_le_S hv hn x.property

/-- The KL coefficient is jointly continuous throughout the nondegenerate
part of the closed parameter cube, including channel-boundary points. -/
theorem continuousOn_parameterCoefficient :
    ContinuousOn parameterCoefficient
      {p : Parameters | Nondegenerate (parameterInput p) (parameterC p) (parameterD p)} := by
  let N := {p : Parameters // Nondegenerate (parameterInput p) (parameterC p) (parameterD p)}
  let f : N → Icc (0 : ℝ) 1 → ℝ := fun p x =>
    extendedRatio (parameterInput p) (parameterC p) (parameterD p) x
  have hf : Continuous (fun z : N × Icc (0 : ℝ) 1 => f z.1 z.2) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hproj : ContinuousAt (fun z : N × Icc (0 : ℝ) 1 => (z.1.val : Parameters)) z :=
      continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt
    exact continuousAt_extendedRatio_comp
      (continuous_parameterInput.continuousAt.comp hproj)
      (continuous_parameterC.continuousAt.comp hproj)
      (continuous_parameterD.continuousAt.comp hproj)
      (continuous_subtype_val.continuousAt.comp continuous_snd.continuousAt)
      z.1.property z.2.property
  let : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hsup : Continuous (fun p : N => sSup (range (f p))) := by
    simpa only [image_univ] using (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) 1))).continuous_sSup hf
  rw [continuousOn_iff_continuous_domRestrict]
  apply hsup.congr
  intro p
  exact (S_eq_sSup_range_extendedRatio (parameter_valid p) p.property).symm

theorem continuousAt_parameterCoefficient {p : Parameters}
    (hn : Nondegenerate (parameterInput p) (parameterC p) (parameterD p)) :
    ContinuousAt parameterCoefficient p :=
  continuousOn_parameterCoefficient.continuousAt (isOpen_parameterNondegenerate.mem_nhds hn)

/-- Continuity along any continuous family that stays in the parameter cube
near the point under consideration. -/
theorem continuousAt_S_comp {α : Type*} [TopologicalSpace α]
    {s c d : α → ℝ} {a : α}
    (hs : ContinuousAt s a) (hc : ContinuousAt c a) (hd : ContinuousAt d a)
    (hv : ∀ᶠ t in nhds a, Valid (s t) (c t) (d t))
    (hn : Nondegenerate (s a) (c a) (d a)) :
    ContinuousAt (fun t => S (s t) (c t) (d t)) a := by
  let T : Set α := {t | Valid (s t) (c t) (d t)}
  have ha : a ∈ T := mem_of_mem_nhds hv
  let p : T → Parameters := fun t =>
    (⟨s t, t.property.1⟩, ⟨c t, t.property.2.1⟩, ⟨d t, t.property.2.2⟩)
  have hp : ContinuousAt p ⟨a, ha⟩ := by
    have hval : ContinuousAt (fun t : T => (t : α)) ⟨a, ha⟩ := continuous_subtype_val.continuousAt
    exact ((hs.comp hval).codRestrict (fun t : T => t.property.1)).prodMk
      (((hc.comp hval).codRestrict (fun t : T => t.property.2.1)).prodMk
        ((hd.comp hval).codRestrict (fun t : T => t.property.2.2)))
  have h := (continuousAt_parameterCoefficient (p := p ⟨a, ha⟩) hn).comp hp
  have hw : ContinuousWithinAt (fun t => S (s t) (c t) (d t)) T a :=
    (continuousWithinAt_iff_continuousAt_domRestrict _ ha).2 h
  exact hw.continuousAt hv

end JointRatioContinuity

end BinaryPairBound
