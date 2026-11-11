module

public import BinaryPairBound.FiniteEntropyConvex
public import BinaryPairBound.FiniteContraction

noncomputable section
@[expose] public section

open scoped BigOperators

namespace BinaryPairBound.FiniteInfo

universe u

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[ext] theorem Law.ext {p q : Law α} (h : p.mass = q.mass) : p = q := by
  cases p; cases q; cases h; rfl

def Law.prod (p : Law α) (q : Law β) : Law (α × β) where
  mass a := p.mass a.1 * q.mass a.2
  nonneg a := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.total, q.total]

def Channel.prod (K : Channel α β) (L : Channel γ δ) : Channel (α × γ) (β × δ) where
  prob a b := K.prob a.1 b.1 * L.prob a.2 b.2
  nonneg a b := mul_nonneg (K.nonneg _ _) (L.nonneg _ _)
  total a := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, K.total, L.total]

/-- The entropy chain identity for a product reference law. -/
theorem entropy_prod (p : Law α) (q : Law β) (f : α × β → ℝ) :
    entropy (p.prod q).mass f =
      (∑ a, p.mass a * entropy q.mass (fun b => f (a,b))) +
      entropy p.mass (fun a => ∑ b, q.mass b * f (a,b)) := by
  unfold entropy Law.prod
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_sub_distrib,
    mul_sub]
  simp only [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
  ring

/-- The output law of independent channels is the product of output laws. -/
theorem out_prod (p : Law α) (q : Law γ) (K : Channel α β) (L : Channel γ δ) :
    out (p.prod q) (K.prod L) = (out p K).prod (out q L) := by
  ext z
  simp only [out, Law.prod, Channel.prod, Fintype.sum_prod_type]
  simp_rw [show ∀ a c, p.mass a * q.mass c * (K.prob a z.1 * L.prob c z.2) =
    (p.mass a * K.prob a z.1) * (q.mass c * L.prob c z.2) by intros; ring]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Applying independent channels is successive posterior averaging. -/
theorem transfer_prod (p : Law α) (q : Law γ) (K : Channel α β) (L : Channel γ δ)
    (f : α × γ → ℝ) (b : β) (d : δ) :
    transfer (p.prod q) (K.prod L) f (b,d) =
      transfer q L (fun c => transfer p K (fun a => f (a,c)) b) d := by
  unfold transfer
  rw [out_prod]
  simp only [Law.prod, Channel.prod, Fintype.sum_prod_type, div_eq_mul_inv,
    mul_inv_rev, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Posterior averaging commutes with a finite weighted average. -/
theorem transfer_sum (p : Law α) (K : Channel α β) (w : γ → ℝ)
    (f : α × γ → ℝ) (b : β) :
    transfer p K (fun a => ∑ c, w c * f (a,c)) b =
      ∑ c, w c * transfer p K (fun a => f (a,c)) b := by
  simp only [transfer, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Conditional entropy cannot increase under posterior mixing in the other coordinate. -/
theorem sum_entropy_transfer_le (p : Law α) (q : Law γ) (K : Channel α β)
    {f : α × γ → ℝ} (hf : ∀ z, 0 ≤ f z) :
    (∑ b, (out p K).mass b * entropy q.mass
      (fun c => transfer p K (fun a => f (a,c)) b)) ≤
      ∑ a, p.mass a * entropy q.mass (fun c => f (a,c)) := by
  have hbnd (b : β) :
      (out p K).mass b * entropy q.mass (fun c => transfer p K (fun a => f (a,c)) b) ≤
        ∑ a, p.mass a * K.prob a b * entropy q.mass (fun c => f (a,c)) := by
    by_cases hb : (out p K).mass b = 0
    · simp [hb, joint_zero_of_out_zero p K hb]
    have hmix := entropy_mix_le q
      (fun a => p.mass a * K.prob a b / (out p K).mass b)
      (fun a => div_nonneg (mul_nonneg (p.nonneg a) (K.nonneg a b)) ((out p K).nonneg b))
      (fun a c => f (a,c)) (fun a c => hf (a,c))
    have hfun : (fun c => ∑ a, p.mass a * K.prob a b / (out p K).mass b * f (a,c)) =
        (fun c => transfer p K (fun a => f (a,c)) b) := by
      funext c
      simp only [transfer, div_eq_mul_inv, mul_right_comm _ _ (f _), Finset.sum_mul]
    rw [hfun] at hmix
    have hmul := mul_le_mul_of_nonneg_left hmix ((out p K).nonneg b)
    convert hmul using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  calc
    _ ≤ ∑ b, ∑ a, p.mass a * K.prob a b * entropy q.mass (fun c => f (a,c)) :=
      Finset.sum_le_sum fun b _ => hbnd b
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul, ← Finset.mul_sum, K.total, mul_one]

/-- Distribution-dependent KL caps tensorize for independent finite channels. -/
theorem Contracts.prod {p : Law α} {q : Law γ} {K : Channel α β} {L : Channel γ δ}
    {lam : ℝ} (hK : Contracts p K lam) (hL : Contracts q L lam) (hlam : 0 ≤ lam) :
    Contracts (p.prod q) (K.prod L) lam := by
  intro f hf
  have ht : transfer (p.prod q) (K.prod L) f =
      (fun z => transfer q L (fun c => transfer p K (fun a => f (a,c)) z.1) z.2) := by
    funext z
    exact transfer_prod p q K L f z.1 z.2
  rw [ht, out_prod, entropy_prod, entropy_prod]
  simp_rw [sum_out_mul_transfer]
  have hfun : (fun b => ∑ c, q.mass c * transfer p K (fun a => f (a,c)) b) =
      transfer p K (fun a => ∑ c, q.mass c * f (a,c)) := by
    funext b
    exact (transfer_sum p K q.mass f b).symm
  rw [hfun]
  have hfirst := Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
    mul_le_mul_of_nonneg_left
      (hL (fun c => transfer p K (fun a => f (a,c)) b)
        (fun c => transfer_nonneg p K (fun a => hf (a,c)) b)) ((out p K).nonneg b))
  have hsecond := hK (fun a => ∑ c, q.mass c * f (a,c))
    (fun a => Finset.sum_nonneg (fun c _ => mul_nonneg (q.nonneg c) (hf (a,c))))
  have hmix := mul_le_mul_of_nonneg_left (sum_entropy_transfer_le p q K hf) hlam
  calc
    _ ≤ (∑ b, (out p K).mass b * (lam * entropy q.mass
        (fun c => transfer p K (fun a => f (a,c)) b))) +
        lam * entropy p.mass (fun a => ∑ c, q.mass c * f (a,c)) := add_le_add hfirst hsecond
    _ = lam * (∑ b, (out p K).mass b * entropy q.mass
        (fun c => transfer p K (fun a => f (a,c)) b)) +
        lam * entropy p.mass (fun a => ∑ c, q.mass c * f (a,c)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ lam * (∑ a, p.mass a * entropy q.mass (fun c => f (a,c))) +
        lam * entropy p.mass (fun a => ∑ c, q.mass c * f (a,c)) := add_le_add hmix le_rfl
    _ = _ := by ring

/-- A constant density has zero homogeneous entropy. -/
theorem entropy_const (p : Law α) (c : ℝ) : entropy p.mass (fun _ => c) = 0 := by
  simp only [entropy, ← Finset.sum_mul, p.total, one_mul, sub_self]

/-- The conditional entropy of a constant remains zero after processing. -/
theorem entropy_transfer_const (p : Law α) (K : Channel α β) {c : ℝ} (hc : 0 ≤ c) :
    entropy (out p K).mass (transfer p K (fun _ => c)) = 0 := by
  apply le_antisymm
  · simpa only [entropy_const] using entropy_transfer_le p K (fun _ => hc)
  · exact entropy_nonneg _ (transfer_nonneg p K (fun _ => hc))

/-- A cap for an independent product implies the cap for its first coordinate. -/
theorem Contracts.of_prod_left {p : Law α} {q : Law γ} {K : Channel α β} {L : Channel γ δ}
    {lam : ℝ} (h : Contracts (p.prod q) (K.prod L) lam) : Contracts p K lam := by
  intro f hf
  have hh := h (fun z => f z.1) (fun z => hf z.1)
  have ht : transfer (p.prod q) (K.prod L) (fun z => f z.1) =
      (fun z => transfer q L (fun _ => transfer p K f z.1) z.2) := by
    funext z
    exact transfer_prod p q K L (fun z => f z.1) z.1 z.2
  rw [ht, out_prod, entropy_prod, entropy_prod] at hh
  simp only [entropy_const, mul_zero, Finset.sum_const_zero, zero_add] at hh
  simp_rw [sum_out_mul_transfer, ← Finset.sum_mul, q.total, one_mul] at hh
  have he : (fun b => entropy (out q L).mass (transfer q L (fun _ => transfer p K f b))) =
      fun _ => 0 := by
    funext b
    exact entropy_transfer_const q L (transfer_nonneg p K hf b)
  simp_rw [show ∀ b, entropy (out q L).mass (transfer q L (fun _ => transfer p K f b)) = 0
    from congrFun he] at hh
  simpa only [mul_zero, Finset.sum_const_zero, zero_add] using hh

/-- A finite sequence of observations, represented by nested products. -/
def Sample (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × Sample α n

@[reducible] instance sampleFintype (α : Type*) [Fintype α] : (n : ℕ) → Fintype (Sample α n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd α (Sample α n) _ (sampleFintype α n)

/-- The law of independent identically distributed observations. -/
def Law.power (p : Law α) : (n : ℕ) → Law (Sample α n)
  | 0 => { mass := fun _ => 1, nonneg := fun _ => zero_le_one, total := by change (∑ _ : PUnit, (1 : ℝ)) = 1; simp }
  | n + 1 => p.prod (p.power n)

/-- Independent application of one channel to each observation. -/
def Channel.power (K : Channel α β) : (n : ℕ) → Channel (Sample α n) (Sample β n)
  | 0 => { prob := fun _ _ => 1, nonneg := fun _ _ => zero_le_one,
           total := fun _ => by change (∑ _ : PUnit, (1 : ℝ)) = 1; simp }
  | n + 1 => K.prod (K.power n)

/-- Tensorization for any finite number of independent observations, including zero. -/
theorem Contracts.power {p : Law α} {K : Channel α β} {lam : ℝ}
    (h : Contracts p K lam) (hlam : 0 ≤ lam) (n : ℕ) :
    Contracts (p.power n) (K.power n) lam := by
  induction n with
  | zero =>
    intro f _
    let : Subsingleton (Sample α 0) := inferInstanceAs (Subsingleton PUnit)
    let : Subsingleton (Sample β 0) := inferInstanceAs (Subsingleton PUnit)
    have hp : (p.power 0).mass PUnit.unit = 1 := rfl
    have hq : (out (p.power 0) (K.power 0)).mass PUnit.unit = 1 := by
      change (∑ _ : PUnit, (1 : ℝ) * 1) = 1
      simp
    have sumA (g : Sample α 0 → ℝ) : ∑ a, g a = g PUnit.unit :=
      Fintype.sum_subsingleton g PUnit.unit
    have sumB (g : Sample β 0 → ℝ) : ∑ b, g b = g PUnit.unit :=
      Fintype.sum_subsingleton g PUnit.unit
    unfold entropy
    rw [sumB, sumB, sumA, sumA]
    rw [hp, hq]
    simp
  | succ n ih => exact h.prod ih hlam

/-- A concrete conversion of the nested-product representation to ordinary indexed vectors. -/
def Sample.toVector : (n : ℕ) → Sample α n → (Fin n → α)
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, x => Fin.cons x.1 (Sample.toVector n x.2)

def Sample.ofVector : (n : ℕ) → (Fin n → α) → Sample α n
  | 0, _ => PUnit.unit
  | n + 1, x => (x 0, Sample.ofVector n (fun i => x i.succ))

omit [Fintype α] in
theorem Sample.ofVector_toVector (n : ℕ) (x : Sample α n) :
    Sample.ofVector n (Sample.toVector n x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    simp only [Sample.ofVector, Sample.toVector, Fin.cons_zero, Fin.cons_succ]
    rw [ih]
    rfl

omit [Fintype α] in
theorem Sample.toVector_ofVector (n : ℕ) (x : Fin n → α) :
    Sample.toVector n (Sample.ofVector n x) = x := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Sample.ofVector, Sample.toVector, Fin.cons_succ]
      exact congrFun (ih (fun j => x j.succ)) j

/-- The representation has precisely the observations indexed by `Fin n`. -/
def Sample.equivVector (n : ℕ) : Sample α n ≃ (Fin n → α) where
  toFun := Sample.toVector n
  invFun := Sample.ofVector n
  left_inv := Sample.ofVector_toVector n
  right_inv := Sample.toVector_ofVector n

/-- Atom probabilities of an IID source are the product of the one-coordinate masses. -/
theorem Law.power_mass (p : Law α) (n : ℕ) (x : Sample α n) :
    (p.power n).mass x = ∏ i : Fin n, p.mass (Sample.toVector n x i) := by
  induction n with
  | zero => simp [Law.power]
  | succ n ih =>
    change p.mass x.1 * (p.power n).mass x.2 = _
    rw [Fin.prod_univ_succ, ih]
    rfl

omit [Fintype α] in
/-- Independent channel probabilities factor coordinate by coordinate. -/
theorem Channel.power_prob (K : Channel α β) (n : ℕ)
    (x : Sample α n) (y : Sample β n) :
    (K.power n).prob x y = ∏ i : Fin n,
      K.prob (Sample.toVector n x i) (Sample.toVector n y i) := by
  induction n with
  | zero => simp [Channel.power]
  | succ n ih =>
    change K.prob x.1 y.1 * (K.power n).prob x.2 y.2 = _
    rw [Fin.prod_univ_succ, ih]
    rfl

/-- The exact contraction coefficient never grows under independent repetition. -/
theorem coefficient_power_le (p : Law α) (K : Channel α β) (n : ℕ) :
    coefficient (p.power n) (K.power n) ≤ coefficient p K :=
  (coefficient_le_iff (coefficient_nonneg p K)).mpr
    ((contracts_coefficient p K).power (coefficient_nonneg p K) n)

/-- Exact tensorization for any positive number of IID observations. -/
theorem coefficient_power_succ (p : Law α) (K : Channel α β) (n : ℕ) :
    coefficient (p.power (n + 1)) (K.power (n + 1)) = coefficient p K := by
  apply le_antisymm (coefficient_power_le p K (n + 1))
  apply (coefficient_le_iff (coefficient_nonneg (p.power (n + 1)) (K.power (n + 1)))).mpr
  exact (contracts_coefficient (p.power (n + 1)) (K.power (n + 1))).of_prod_left

end BinaryPairBound.FiniteInfo
