module

public import BinaryPairBound.RatioContinuity
public import BinaryPairBound.Compactness

/-! # Joint continuity of the extended KL ratio -/

noncomputable section
@[expose] public section

open Filter Set
open scoped Topology

namespace BinaryPairBound

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

end BinaryPairBound
