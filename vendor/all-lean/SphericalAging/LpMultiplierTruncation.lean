module

public import SphericalAging.LpMomentBounds
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Uniformly bounded multipliers that vanish in L² act continuously on each
fixed L² vector. The measure need not have finite mass. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.LpMultiplierTruncation
variable {α E U V ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup U] [NormedAddCommGroup V]
  {μ : Measure α}

@[expose] def tail (W : α → E) (n : ℕ) (x : α) : ℝ := max 0 (‖W x‖-(n:ℝ))

lemma tail_nonnegative (W : α → E) (n : ℕ) (x : α) : 0≤tail W n x := le_max_left _ _
lemma tail_le (W : α → E) (n : ℕ) (x : α) : tail W n x≤‖W x‖ :=
  max_le (norm_nonneg _) (sub_le_self _ (Nat.cast_nonneg _))

lemma tail_memLp {W : α → E} (hW : MemLp W 2 μ) (n : ℕ) : MemLp (tail W n) 2 μ := by
  have hh : AEStronglyMeasurable (tail W n) μ :=
    ((continuous_const.max (continuous_id.sub continuous_const)).comp_aestronglyMeasurable hW.aestronglyMeasurable.norm)
  apply hW.norm.of_le hh
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tail_nonnegative W n x),abs_of_nonneg (norm_nonneg _)] using tail_le W n x)

theorem tail_lpNorm_tendsto {W : α → E} (hW : MemLp W 2 μ) :
    Tendsto (fun n => lpNorm (tail W n) 2 μ) atTop (𝓝 0) := by
  have hdom : Integrable (fun x => ‖W x‖^2) μ := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have hi : Tendsto (fun n => ∫ x,(tail W n x)^2 ∂μ) atTop (𝓝 (0:ℝ)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (l:=(atTop : Filter ℕ)) (μ:=μ)
      (bound:=fun x => ‖W x‖^2) (F:=fun n x => (tail W n x)^2) (f:=fun _ => (0:ℝ))
      (Eventually.of_forall (fun n => ((tail_memLp hW n).aestronglyMeasurable.pow 2)))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (tail_nonnegative W n x) (tail_le W n x) 2))) hdom ?_
    · simpa only [integral_zero] using hh
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖W x‖)] with n hn
        simp only [tail,max_eq_left (sub_nonpos.mpr hn),zero_pow (by decide : (2:ℕ)≠0)])
  have he (n : ℕ) : lpNorm (tail W n) 2 μ=Real.sqrt (∫x,(tail W n x)^2 ∂μ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞)≠0) (by finiteness)
      (tail_memLp hW n).aestronglyMeasurable,Real.sqrt_eq_rpow]
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only; rw [Real.norm_eq_abs,sq_abs])
  simpa only [he,Real.sqrt_zero] using hi.sqrt

lemma lpNorm_norm {f : α → U} (hf : MemLp f 2 μ) :
    lpNorm (fun x => ‖f x‖) 2 μ=lpNorm f 2 μ := by
  simpa only [toReal_eLpNorm] using congrArg ENNReal.toReal (eLpNorm_norm f hf.aestronglyMeasurable (p:=2))

lemma lpNorm_const_mul (c : ℝ) (f : α → ℝ) :
    lpNorm (fun x => c*f x) 2 μ=|c| * lpNorm f 2 μ := by
  change lpNorm (c • f) 2 μ=|c| * lpNorm f 2 μ
  rw [lpNorm_const_smul]
  simp only [coe_nnnorm,Real.norm_eq_abs]

theorem quantitative_bound {W : α → E} {f : α → U} {g : α → V}
    (hW : MemLp W 2 μ) (hf : MemLp f 2 μ) (hg : AEStronglyMeasurable g μ)
    {L K : ℝ} (hL : 0≤L) (hK : 0≤K)
    (hsmall : ∀ᵐ x ∂μ,‖g x‖≤L*‖f x‖*‖W x‖)
    (hbounded : ∀ᵐ x ∂μ,‖g x‖≤K*‖W x‖) (n : ℕ) :
    MemLp g 2 μ ∧ lpNorm g 2 μ≤2*L*(n:ℝ)*lpNorm f 2 μ+2*K*lpNorm (tail W n) 2 μ := by
  have hG : MemLp g 2 μ := by
    apply (hW.norm.const_mul K).of_le hg
    filter_upwards [hbounded] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hK (norm_nonneg _))] using hx
  let B : α → ℝ := fun x => (2*L*(n:ℝ))*‖f x‖+(2*K)*tail W n x
  have hB : MemLp B 2 μ := (hf.norm.const_mul (2*L*n)).add ((tail_memLp hW n).const_mul (2*K))
  have hb : ∀ᵐ x ∂μ,‖g x‖≤B x := by
    filter_upwards [hsmall,hbounded] with x hs hk
    dsimp only [B]
    by_cases hw : ‖W x‖≤2*(n:ℝ)
    · have hh := hs.trans (mul_le_mul_of_nonneg_left hw (mul_nonneg hL (norm_nonneg _)))
      nlinarith [mul_nonneg hK (tail_nonnegative W n x)]
    · have hw' : (n:ℝ)≤‖W x‖ := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
      rw [tail,max_eq_right (sub_nonneg.mpr hw')]
      have hnn := Nat.cast_nonneg (α:=ℝ) n
      have hl := mul_nonneg hL (norm_nonneg (f x))
      nlinarith
  have hnorm : lpNorm g 2 μ≤lpNorm B 2 μ := by
    have he := eLpNorm_mono_ae_real (p:=2) hg hb
    simpa only [toReal_eLpNorm] using (ENNReal.toReal_le_toReal hG.eLpNorm_ne_top hB.eLpNorm_ne_top).mpr he
  refine ⟨hG,hnorm.trans ?_⟩
  have hh := lpNorm_add_le (hf.norm.const_mul (2*L*n)) (by norm_num : (1:ℝ≥0∞)≤2)
    (g:=fun x => (2*K)*tail W n x)
  change lpNorm ((fun x => (2*L*(n:ℝ))*‖f x‖)+(fun x => (2*K)*tail W n x)) 2 μ≤_
  simpa only [lpNorm_const_mul,abs_of_nonneg (by positivity : 0≤2*L*(n:ℝ)),
    abs_of_nonneg (by positivity : 0≤2*K),lpNorm_norm hf] using hh

theorem lpNorm_two_tendsto_zero {W : α → E} (hW : MemLp W 2 μ)
    {l : Filter ι} {f : ι → α → U} {g : ι → α → V} {L K : ℝ}
    (hL : 0≤L) (hK : 0≤K) (hf : ∀ᶠ i in l,MemLp (f i) 2 μ)
    (hg : ∀ᶠ i in l,AEStronglyMeasurable (g i) μ)
    (hsmall : ∀ᶠ i in l,∀ᵐ x ∂μ,‖g i x‖≤L*‖f i x‖*‖W x‖)
    (hbounded : ∀ᶠ i in l,∀ᵐ x ∂μ,‖g i x‖≤K*‖W x‖)
    (hzero : Tendsto (fun i => lpNorm (f i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => lpNorm (g i) 2 μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htail := (tail_lpNorm_tendsto hW).const_mul (2*K)
  simp only [mul_zero] at htail
  obtain ⟨n,hn⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))).exists
  have hnear := (hzero.const_mul (2*L*(n:ℝ))).eventually
    (gt_mem_nhds (by simpa only [mul_zero] using (show (0:ℝ)<ε/2 by positivity)))
  filter_upwards [hf,hg,hsmall,hbounded,hnear] with i hf hg hs hb hnear
  have hh := (quantitative_bound hW hf hg hL hK hs hb n).2
  rw [Real.dist_eq,sub_zero,abs_of_nonneg lpNorm_nonneg]
  linarith

end SphericalAging.LpMultiplierTruncation
