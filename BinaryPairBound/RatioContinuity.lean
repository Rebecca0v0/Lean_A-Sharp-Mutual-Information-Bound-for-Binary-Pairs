module

public import BinaryPairBound.LocalCoefficient
public import BinaryPairBound.DivergenceCalculus
public import BinaryPairBound.ContactGeometry
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Topology.Order.Compact

/-!
# The removable diagonal singularity of the binary KL ratio

All limits here keep the reference input and channel fixed. The diagonal
value is proved by two applications of l'Hôpital's rule, rather than
introduced as an unverified continuity assumption.
-/

noncomputable section
@[expose] public section

open Filter Set
open scoped Topology

namespace BinaryPairBound

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

end BinaryPairBound
