module

public import BinaryPairBound.Contraction
public import BinaryPairBound.Symmetry
public import Mathlib.Topology.Order.Compact

/-!
# Existence of a cap-constrained maximizer

We prove closedness of cap sublevel sets directly from the universal KL
inequality. Only continuity of each fixed-test-input inequality is needed;
global continuity of the coefficient at deterministic marginals is not claimed.
-/

noncomputable section
@[expose] public section

namespace BinaryPairBound

abbrev Parameters := Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1

def parameterInput (p : Parameters) : ℝ := p.1
def parameterC (p : Parameters) : ℝ := p.2.1
def parameterD (p : Parameters) : ℝ := p.2.2
def parameterOutput (p : Parameters) (x : ℝ) : ℝ := q (parameterC p) (parameterD p) x
def parameterInformation (p : Parameters) : ℝ := J (parameterInput p) (parameterC p) (parameterD p)
def parameterCoefficient (p : Parameters) : ℝ := S (parameterInput p) (parameterC p) (parameterD p)

theorem parameter_valid (p : Parameters) :
    Valid (parameterInput p) (parameterC p) (parameterD p) :=
  ⟨p.1.property, p.2.1.property, p.2.2.property⟩

lemma continuous_parameterInput : Continuous parameterInput :=
  continuous_subtype_val.comp continuous_fst

lemma continuous_parameterC : Continuous parameterC :=
  continuous_subtype_val.comp (continuous_fst.comp continuous_snd)

lemma continuous_parameterD : Continuous parameterD :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_snd)

lemma continuous_parameterOutput {f : Parameters → ℝ} (hf : Continuous f) :
    Continuous (fun p => parameterOutput p (f p)) := by
  unfold parameterOutput q k
  exact continuous_parameterC.add
    (((continuous_const.sub continuous_parameterC).sub continuous_parameterD).mul hf)

theorem continuous_parameterInformation : Continuous parameterInformation := by
  unfold parameterInformation J
  exact ((Real.binEntropy_continuous.comp (continuous_parameterOutput continuous_parameterInput)).sub
    ((continuous_const.sub continuous_parameterInput).mul
      (Real.binEntropy_continuous.comp continuous_parameterC))).sub
    (continuous_parameterInput.mul (Real.binEntropy_continuous.comp continuous_parameterD))

lemma continuousAt_D_comp {α : Type*} [TopologicalSpace α] {f g : α → ℝ} {a : α}
    (hf : ContinuousAt f a) (hg : ContinuousAt g a) (ha : g a ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (fun t => D (f t) (g t)) a := by
  unfold D
  exact (((Real.binEntropy_continuous.continuousAt.comp hf).neg).sub
    (hf.mul (hg.log (ne_of_gt ha.1)))).sub
    ((continuousAt_const.sub hf).mul
      ((continuousAt_const.sub hg).log (ne_of_gt (sub_pos.mpr ha.2))))

lemma isOpen_parameterNondegenerate :
    IsOpen {p : Parameters | Nondegenerate (parameterInput p) (parameterC p) (parameterD p)} := by
  exact (continuous_parameterInput.isOpen_preimage _ isOpen_Ioo).inter
    ((continuous_parameterOutput continuous_parameterInput).isOpen_preimage _ isOpen_Ioo)

/-- Lower semicontinuity in the form needed for compact optimization. -/
theorem isOpen_coefficient_gt {lam : ℝ} (hlam : 0 ≤ lam) :
    IsOpen {p : Parameters | lam < parameterCoefficient p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hn : Nondegenerate (parameterInput p) (parameterC p) (parameterD p) := by
    by_contra hn
    have hzero := S_eq_zero_of_not_nondegenerate hn
    change lam < S (parameterInput p) (parameterC p) (parameterD p) at hp
    rw [hzero] at hp
    linarith
  have hfail : ¬KLCap lam (parameterInput p) (parameterC p) (parameterD p) := by
    intro h
    exact (not_le_of_gt hp) ((S_le_iff_klCap (parameter_valid p) hn).mpr h)
  simp only [KLCap, not_forall] at hfail
  obtain ⟨x, hx, hstrict⟩ := hfail
  have hlt : lam * D x (parameterInput p) <
      D (parameterOutput p x) (parameterOutput p (parameterInput p)) := lt_of_not_ge hstrict
  have hc1 := (continuousAt_D_comp (f := fun _ : Parameters => x) continuousAt_const
    continuous_parameterInput.continuousAt hn.1).const_mul lam
  have hc2 := continuousAt_D_comp (f := fun z : Parameters => parameterOutput z x)
    (continuous_parameterOutput (f := fun _ => x) continuous_const).continuousAt
    (continuous_parameterOutput continuous_parameterInput).continuousAt hn.2
  have hevent := (hc2.sub hc1).eventually (lt_mem_nhds (sub_pos.mpr hlt))
  have hnevent : ∀ᶠ z in nhds p,
      Nondegenerate (parameterInput z) (parameterC z) (parameterD z) :=
    isOpen_parameterNondegenerate.mem_nhds hn
  exact (hnevent.and hevent).mono fun z hz => by
    apply lt_of_not_ge
    intro hle
    have hcap := (S_le_iff_klCap (parameter_valid z) hz.1).mp hle x hx
    have hzpos := hz.2
    change 0 < D (q (parameterC z) (parameterD z) x)
      (q (parameterC z) (parameterD z) (parameterInput z)) -
      lam * D x (parameterInput z) at hzpos
    linarith

theorem isClosed_coefficient_le {lam : ℝ} (hlam : 0 ≤ lam) :
    IsClosed {p : Parameters | parameterCoefficient p ≤ lam} := by
  simpa only [Set.compl_ofPred, not_lt] using (isOpen_coefficient_gt hlam).isClosed_compl

theorem exists_cap_maximizer {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ s c d : ℝ, Valid s c d ∧ S s c d ≤ lam ∧
      ∀ s' c' d' : ℝ, Valid s' c' d' → S s' c' d' ≤ lam → J s' c' d' ≤ J s c d := by
  let : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hcompact := (isClosed_coefficient_le hlam).isCompact
  have hne : ({p : Parameters | parameterCoefficient p ≤ lam}).Nonempty := by
    refine ⟨(⟨0, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩), ?_⟩
    change S 0 0 0 ≤ lam
    simpa only [S_eq_zero_of_independent (s := 0) (c := 0) (d := 0) (Or.inl rfl)] using hlam
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hne continuous_parameterInformation.continuousOn
  refine ⟨parameterInput p, parameterC p, parameterD p, parameter_valid p, hp, ?_⟩
  intro s c d hv hS
  exact hmax (show (⟨s, hv.1⟩, ⟨c, hv.2.1⟩, ⟨d, hv.2.2⟩) ∈
    {p : Parameters | parameterCoefficient p ≤ lam} from hS)

/-- The maximizer can be chosen in the positive-slope half of the channel cube. -/
theorem exists_normalized_cap_maximizer {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ s c d : ℝ, Valid s c d ∧ c + d ≤ 1 ∧ S s c d ≤ lam ∧
      ∀ s' c' d' : ℝ, Valid s' c' d' → S s' c' d' ≤ lam → J s' c' d' ≤ J s c d := by
  obtain ⟨s, c, d, hv, hS, hmax⟩ := exists_cap_maximizer hlam
  by_cases hcd : c + d ≤ 1
  · exact ⟨s, c, d, hv, hcd, hS, hmax⟩
  · refine ⟨s, 1 - c, 1 - d, valid_output_flip hv, by linarith, ?_, ?_⟩
    · simpa only [S_output_flip] using hS
    · intro s' c' d' hv' hS'
      simpa only [J_output_flip] using hmax s' c' d' hv' hS'

end BinaryPairBound
