module

public import BinaryPairBound.ContactJacobian
public import BinaryPairBound.InformationPerturbation
public import BinaryPairBound.ContactEndpoints
public import BinaryPairBound.ContactFeasibility
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Smooth contact equations and local contact families -/

noncomputable section
@[expose] public section

open scoped ContDiff

namespace BinaryPairBound

/-- The explicit derivative of the contact gap with respect to its test input. -/
def contactSlope (lam s qv kv r : ℝ) : ℝ :=
  kv * (logOdds (qv + kv * (r - s)) - logOdds qv) -
    lam * (logOdds r - logOdds s)

/-- The two contact equations, parameterized by `(s,q)` and solved for `(k,r)`. -/
def contactSystem (lam : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (contactGap lam p.1.1 p.1.2 p.2.1 p.2.2,
   contactSlope lam p.1.1 p.1.2 p.2.1 p.2.2)

lemma contactSlope_eq_deriv {lam s qv kv r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    contactSlope lam s qv kv r = deriv (fun z => contactGap lam s qv kv z) r :=
  (hasDerivAt_contactGap_r lam s qv kv r hs hr hq hqr).deriv.symm

private lemma contDiffAt_D_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hfI : f x ∈ Set.Ioo (0 : ℝ) 1) (hgI : g x ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ n (fun z => D (f z) (g z)) x := by
  simp only [D, H_eq]
  fun_prop (disch := first | exact ne_of_gt hfI.1 | exact ne_of_gt hgI.1 |
    exact ne_of_gt (sub_pos.mpr hfI.2) | exact ne_of_gt (sub_pos.mpr hgI.2))

private lemma contDiffAt_logOdds_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ n f x)
    (hfI : f x ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ n (fun z => logOdds (f z)) x := by
  unfold logOdds
  exact (hf.log (ne_of_gt hfI.1)).sub
    ((contDiffAt_const.sub hf).log (ne_of_gt (sub_pos.mpr hfI.2)))

/-- Both contact equations are smooth on the interior probability domain. -/
theorem contDiffAt_contactSystem {lam s qv kv r : ℝ} {n : ℕ∞ω}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ n (contactSystem lam) ((s, qv), (kv, r)) := by
  have hS : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1) ((s,qv),(kv,r)) := by fun_prop
  have hQ : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2) ((s,qv),(kv,r)) := by fun_prop
  have hK : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1) ((s,qv),(kv,r)) := by fun_prop
  have hR : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.2) ((s,qv),(kv,r)) := by fun_prop
  have hY := hQ.add (hK.mul (hR.sub hS))
  exact ((contDiffAt_D_comp hY hQ hqr hq).sub
    (contDiffAt_const.mul (contDiffAt_D_comp hR hS hr hs))).prodMk
    ((hK.mul ((contDiffAt_logOdds_comp hY hqr).sub (contDiffAt_logOdds_comp hQ hq))).sub
      (contDiffAt_const.mul ((contDiffAt_logOdds_comp hR hr).sub (contDiffAt_logOdds_comp hS hs))))

private lemma prod_linear_decomposition (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (z : ℝ × ℝ) :
    L z = z.1 • L (1, 0) + z.2 • L (0, 1) := by
  have hz : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
  conv_lhs => rw [hz]
  simp only [map_add, map_smul]

/-- An explicit inverse for a triangular two-dimensional derivative. -/
private theorem triangular_isInvertible (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hA : (L (1, 0)).1 ≠ 0) (hZ : (L (0, 1)).1 = 0)
    (hC : (L (0, 1)).2 ≠ 0) : L.IsInvertible := by
  let A := (L (1, 0)).1
  let B := (L (1, 0)).2
  let C := (L (0, 1)).2
  let inv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((1 / A) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((1 / C) • ContinuousLinearMap.snd ℝ ℝ ℝ -
        (B / (A * C)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hL (z : ℝ × ℝ) : L z = (A * z.1, B * z.1 + C * z.2) := by
    rw [prod_linear_decomposition]
    ext <;> simp [A, B, C, hZ] <;> ring
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := inv)
  · apply ContinuousLinearMap.ext
    intro z
    change L (inv z) = z
    rw [hL]
    ext <;> simp [inv, smul_eq_mul] <;>
      field_simp [show A ≠ 0 from hA, show C ≠ 0 from hC]
    all_goals ring
  · apply ContinuousLinearMap.ext
    intro z
    change inv (L z) = z
    rw [hL]
    ext <;> simp [inv, smul_eq_mul] <;>
      field_simp [show A ≠ 0 from hA, show C ≠ 0 from hC]
    all_goals ring

lemma deriv_contactSlope_r {lam s qv kv r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hq : qv ∈ Set.Ioo (0 : ℝ) 1)
    (hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun z => contactSlope lam s qv kv z) r =
      deriv (deriv (fun z => contactGap lam s qv kv z)) r := by
  have hY : ContinuousAt (fun z : ℝ => qv + kv * (z - s)) r := by fun_prop
  have heq : (fun z => contactSlope lam s qv kv z) =ᶠ[nhds r]
      deriv (fun z => contactGap lam s qv kv z) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2, hY (Ioo_mem_nhds hqr.1 hqr.2)] with z hz hqz
    exact contactSlope_eq_deriv hs hz hq hqz
  exact heq.deriv_eq

/-- The unknown-coordinate derivative of the genuine two contact equations
is invertible. Its diagonal signs follow from supporting-contact geometry. -/
theorem contactSystem_partial_isInvertible {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    (fderiv ℝ (contactSystem lam) ((s, q c d s), (k c d, r)) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)).IsInvertible := by
  let qv := q c d s
  let kv := k c d
  have hq : qv ∈ Set.Ioo (0 : ℝ) 1 := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr : qv + kv * (r - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    have heq : qv + kv * (r - s) = q c d r := by dsimp [qv, kv, q]; ring
    rw [heq]
    exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hcdiff : ContDiffAt ℝ 1 (contactSystem lam) ((s,qv),(kv,r)) :=
    contDiffAt_contactSystem hs hr hq hqr
  have hf := (hcdiff.differentiableAt (by norm_num)).hasFDerivAt
  let L := fderiv ℝ (contactSystem lam) ((s,qv),(kv,r)) ∘L
    ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)
  have hkcurve : HasDerivAt (fun z : ℝ => ((s,qv),(z,r))) ((0,0),(1,0)) kv :=
    (hasDerivAt_const kv (s,qv)).prodMk ((hasDerivAt_id kv).prodMk (hasDerivAt_const kv r))
  have hrcurve : HasDerivAt (fun z : ℝ => ((s,qv),(kv,z))) ((0,0),(0,1)) r :=
    (hasDerivAt_const r (s,qv)).prodMk ((hasDerivAt_const r kv).prodMk (hasDerivAt_id r))
  have hfk : HasDerivAt (fun z => contactGap lam s qv z r) (L (1,0)).1 kv := by
    exact hf.fst.comp_hasDerivAt kv hkcurve
  have hfr : HasDerivAt (fun z => contactGap lam s qv kv z) (L (0,1)).1 r := by
    exact hf.fst.comp_hasDerivAt r hrcurve
  have hgr : HasDerivAt (fun z => contactSlope lam s qv kv z) (L (0,1)).2 r := by
    exact hf.snd.comp_hasDerivAt r hrcurve
  apply triangular_isInvertible L
  · rw [← hfk.deriv]
    exact ne_of_gt (contactGap_deriv_k_pos lam s qv kv r hq hqr
      (by dsimp [kv, k]; linarith) hsr)
  · rw [← hfr.deriv]
    exact contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact
  · rw [← hgr.deriv, deriv_contactSlope_r hs hr hq hqr]
    exact ne_of_lt (contactGap_deriv2_r_neg_of_contact hs hr hc hd (ne_of_lt hcd) hlam
      (ne_of_gt hsr) hcap hcontact)

/-- The implicit function theorem constructs a genuine local smooth family
of contacts with both marginals free. Invertibility is proved from the contact
hypotheses, not assumed. Feasibility follows separately from the open outer-
contact conditions. -/
theorem exists_smooth_contact_family {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    ∃ f : (ℝ × ℝ) → (ℝ × ℝ),
      ContDiffAt ℝ 1 f (s, q c d s) ∧
      f (s, q c d s) = (k c d, r) ∧
      ∀ᶠ p in nhds (s, q c d s),
        contactGap lam p.1 p.2 (f p).1 (f p).2 = 0 ∧
        contactSlope lam p.1 p.2 (f p).1 (f p).2 = 0 := by
  have hq := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr : q c d s + k c d * (r - s) ∈ Set.Ioo (0 : ℝ) 1 := by
    have heq : q c d s + k c d * (r - s) = q c d r := by unfold q; ring
    rw [heq]
    exact q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hcdiff : ContDiffAt ℝ 1 (contactSystem lam) ((s,q c d s),(k c d,r)) :=
    contDiffAt_contactSystem hs hr hq hqr
  have hi := contactSystem_partial_isInvertible hs hr hc hd hcd hlam hsr hcap hcontact
  let f := hcdiff.implicitFunction (by norm_num) hi
  refine ⟨f, hcdiff.contDiffAt_implicitFunction (by norm_num) hi,
    hcdiff.implicitFunction_apply_self (by norm_num) hi, ?_⟩
  have hbase : contactSystem lam ((s,q c d s),(k c d,r)) = (0,0) := by
    apply Prod.ext
    · change contactGap lam s (q c d s) (k c d) r = 0
      rw [contactGap_eq_tangent_sub ⟨hs,hq⟩, hcontact, sub_self]
    · change contactSlope lam s (q c d s) (k c d) r = 0
      rw [contactSlope_eq_deriv hs hr hq hqr]
      exact contactGap_deriv_r_eq_zero_of_contact hs hr hc hd hcap hcontact
  have he := hcdiff.eventually_apply_implicitFunction (by norm_num) hi
  filter_upwards [he] with p hp
  rw [hbase] at hp
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The smooth family remains globally feasible and exactly saturates the cap.
This follows from the proved local-to-global supporting-contact theorem. -/
theorem exists_feasible_contact_family {lam s c d r : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hd : d ∈ Set.Ioo (0 : ℝ) 1)
    (hcd : c + d < 1) (hlam : lam < eta c d) (hsr : s < r)
    (hcap : KLCap lam s c d)
    (hcontact : entropyCurve lam c d r = tangent lam s c d r) :
    ∃ f : (ℝ × ℝ) → (ℝ × ℝ),
      ContDiffAt ℝ 1 f (s, q c d s) ∧ f (s, q c d s) = (k c d, r) ∧
      ∀ᶠ p in nhds (s, q c d s),
        contactGap lam p.1 p.2 (f p).1 (f p).2 = 0 ∧
        contactSlope lam p.1 p.2 (f p).1 (f p).2 = 0 ∧
        Valid p.1 (p.2 - (f p).1 * p.1) (1 - p.2 - (f p).1 * (1 - p.1)) ∧
        S p.1 (p.2 - (f p).1 * p.1) (1 - p.2 - (f p).1 * (1 - p.1)) = lam := by
  obtain ⟨f, hf, hbase, heq⟩ := exists_smooth_contact_family hs hr hc hd hcd hlam hsr hcap hcontact
  refine ⟨f, hf, hbase, ?_⟩
  let C : (ℝ × ℝ) → ℝ := fun p => p.2 - (f p).1 * p.1
  let E : (ℝ × ℝ) → ℝ := fun p => 1 - p.2 - (f p).1 * (1 - p.1)
  have hC0 : C (s,q c d s) = c := by dsimp [C]; rw [hbase]; unfold q; ring
  have hE0 : E (s,q c d s) = d := by dsimp [E]; rw [hbase]; unfold q k; ring
  have hR0 : (f (s,q c d s)).2 = r := congrArg Prod.snd hbase
  have hfc := hf.continuousAt
  have hC : ContinuousAt C (s,q c d s) := by dsimp [C]; fun_prop
  have hE : ContinuousAt E (s,q c d s) := by dsimp [E]; fun_prop
  have hS0 : S s c d = lam :=
    S_eq_of_supporting_contact hs ⟨hr.1.le, hr.2.le⟩ hc hd (ne_of_gt hsr) hcap hcontact
  have hq := q_mem_Ioo_of_channel hc hd ⟨hs.1.le, hs.2.le⟩
  have hqr := q_mem_Ioo_of_channel hc hd ⟨hr.1.le, hr.2.le⟩
  have hlam0 : 0 < lam := by
    have hpos := (rhoSquared_pos hc hd (ne_of_lt hcd) hs).trans_le
      (rhoSquared_le_S ⟨⟨hs.1.le,hs.2.le⟩,⟨hc.1.le,hc.2.le⟩,⟨hd.1.le,hd.2.le⟩⟩ ⟨hs,hq⟩)
    rwa [hS0] at hpos
  obtain ⟨a, ha, b, hb, haroot, hbroot, _⟩ := rhoSquared_two_roots hc hd (ne_of_lt hcd) ⟨hlam0,hlam⟩
  have hpos := supporting_contacts_straddle_roots hs hr hc hd (ne_of_lt hcd)
    ha hb haroot hbroot hsr hcap hcontact
  have hsu : s < distinguishedInput c d := hpos.1.trans ha.2
  have hrv : distinguishedInput c d < r := hb.1.trans hpos.2
  have hrhos : rhoSquared c d s < lam :=
    rhoSquared_lt_of_left hc hd (ne_of_lt hcd) ha haroot ⟨hs.1.le,hpos.1⟩
  have hrhor : rhoSquared c d r < lam :=
    rhoSquared_lt_of_right hc hd (ne_of_lt hcd) hb hbroot ⟨hpos.2,hr.2.le⟩
  have hecont : ContinuousAt (fun p => eta (C p) (E p)) (s,q c d s) := by
    unfold eta
    fun_prop
  have hden : Real.sqrt (C (s,q c d s) * (1-C (s,q c d s))) +
      Real.sqrt (E (s,q c d s) * (1-E (s,q c d s))) ≠ 0 := by
    rw [hC0,hE0]
    exact ne_of_gt (add_pos (Real.sqrt_pos.mpr (mul_pos hc.1 (sub_pos.mpr hc.2)))
      (Real.sqrt_pos.mpr (mul_pos hd.1 (sub_pos.mpr hd.2))))
  have hdcont : ContinuousAt (fun p => distinguishedInput (C p) (E p)) (s,q c d s) := by
    unfold distinguishedInput
    fun_prop (disch := exact hden)
  have hrscont : ContinuousAt (fun p => rhoSquared (C p) (E p) p.1) (s,q c d s) := by
    unfold rhoSquared
    apply ContinuousAt.div
    · unfold k; fun_prop
    · unfold q k; fun_prop
    · rw [hC0,hE0]
      exact mul_ne_zero (ne_of_gt hq.1) (ne_of_gt (sub_pos.mpr hq.2))
  have hrrcont : ContinuousAt (fun p => rhoSquared (C p) (E p) (f p).2) (s,q c d s) := by
    unfold rhoSquared
    apply ContinuousAt.div
    · unfold k; fun_prop
    · unfold q k; fun_prop
    · rw [hC0,hE0,hR0]
      exact mul_ne_zero (ne_of_gt hqr.1) (ne_of_gt (sub_pos.mpr hqr.2))
  have hsEv : ∀ᶠ p : ℝ × ℝ in nhds (s,q c d s), p.1 ∈ Set.Ioo (0 : ℝ) 1 :=
    continuousAt_fst (Ioo_mem_nhds hs.1 hs.2)
  have hrEv : ∀ᶠ p in nhds (s,q c d s), (f p).2 ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hfc.snd
    simpa only [hR0] using Ioo_mem_nhds hr.1 hr.2
  have hcEv : ∀ᶠ p in nhds (s,q c d s), C p ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hC
    simpa only [hC0] using Ioo_mem_nhds hc.1 hc.2
  have hdEv : ∀ᶠ p in nhds (s,q c d s), E p ∈ Set.Ioo (0 : ℝ) 1 := by
    apply hE
    simpa only [hE0] using Ioo_mem_nhds hd.1 hd.2
  have hcdEv : ∀ᶠ p in nhds (s,q c d s), C p + E p < 1 := by
    exact (hC.add hE).eventually_lt continuousAt_const
      (by simpa only [Pi.add_apply,hC0,hE0] using hcd)
  have hetaEv : ∀ᶠ p in nhds (s,q c d s), lam < eta (C p) (E p) := by
    exact continuousAt_const.eventually_lt hecont
      (by simpa only [hC0,hE0] using hlam)
  have hs0Ev : ∀ᶠ p in nhds (s,q c d s), p.1 < distinguishedInput (C p) (E p) :=
    continuousAt_fst.eventually_lt hdcont (by simpa only [hC0,hE0] using hsu)
  have hr0Ev : ∀ᶠ p in nhds (s,q c d s), distinguishedInput (C p) (E p) < (f p).2 :=
    hdcont.eventually_lt hfc.snd (by simpa only [hC0,hE0,hR0] using hrv)
  have hrsEv : ∀ᶠ p in nhds (s,q c d s), rhoSquared (C p) (E p) p.1 < lam := by
    exact hrscont.eventually_lt continuousAt_const
      (by simpa only [hC0,hE0] using hrhos)
  have hrrEv : ∀ᶠ p in nhds (s,q c d s), rhoSquared (C p) (E p) (f p).2 < lam := by
    exact hrrcont.eventually_lt continuousAt_const
      (by simpa only [hC0,hE0,hR0] using hrhor)
  filter_upwards [heq,hsEv,hrEv,hcEv,hdEv,hcdEv,hetaEv,hs0Ev,hr0Ev,hrsEv,hrrEv] with
    p hp hsp hrp hcp hdp hcdp hetap hs0p hr0p hrsp hrrp
  have hkid : k (C p) (E p) = (f p).1 := by dsimp [C,E,k]; ring
  have hqid : q (C p) (E p) p.1 = p.2 := by rw [q,hkid]; dsimp [C]; ring
  have hn : Nondegenerate p.1 (C p) (E p) :=
    ⟨hsp,q_mem_Ioo_of_channel hcp hdp ⟨hsp.1.le,hsp.2.le⟩⟩
  have hcontactp : entropyCurve lam (C p) (E p) (f p).2 = tangent lam p.1 (C p) (E p) (f p).2 := by
    have h := contactGap_eq_tangent_sub (lam := lam) hn (f p).2
    rw [hqid,hkid,hp.1] at h
    linarith
  have hderivp : deriv (entropyCurve lam (C p) (E p)) (f p).2 =
      deriv (entropyCurve lam (C p) (E p)) p.1 := by
    rw [deriv_entropyCurve lam _ _ _ hrp (q_mem_Ioo_of_channel hcp hdp ⟨hrp.1.le,hrp.2.le⟩),
      deriv_entropyCurve lam _ _ _ hsp hn.2]
    have h := hp.2
    unfold contactSlope logOdds at h
    have heq : q (C p) (E p) (f p).2 = p.2 + (f p).1 * ((f p).2 - p.1) := by
      rw [q,hkid]; dsimp [C]; ring
    rw [heq,hqid,hkid]
    linarith
  have hcapP := klCap_of_outer_contact_equations hcp hdp (ne_of_lt hcdp) ⟨hlam0,hetap⟩
    ⟨hsp.1,hs0p⟩ ⟨hr0p,hrp.2⟩ hrsp hrrp hcontactp hderivp
  refine ⟨hp.1,hp.2,⟨⟨hsp.1.le,hsp.2.le⟩,⟨hcp.1.le,hcp.2.le⟩,⟨hdp.1.le,hdp.2.le⟩⟩,?_⟩
  exact S_eq_of_supporting_contact hsp ⟨hrp.1.le,hrp.2.le⟩ hcp hdp
    (ne_of_gt (hs0p.trans hr0p)) hcapP hcontactp

end BinaryPairBound
