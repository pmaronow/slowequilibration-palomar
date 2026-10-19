module
public import FRSB.ParisiMeasureTopology
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Deterministic nondegeneracy of a martingale second-moment kernel.
Pairing a vanishing time integral with each martingale time gives this kernel;
its derivative detects the tail integral of the coefficient. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace FRSB

/-- Differentiating the `f(min(s,t))` covariance kernel requires no regularity
of the bounded time coefficient beyond measurability. -/
theorem hasDerivAt_momentKernel (a f : ℝ → ℝ)
    (ha : Measurable a) (hab : ∀ s, ‖a s‖ ≤ 1)
    (K : ℝ≥0) (hf : LipschitzWith K f)
    (t d : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hfd : HasDerivAt f d t) :
    HasDerivAt (fun r => ∫ s in (0 : ℝ)..1, a s * f (min s r))
      (d * ∫ s in t..1, a s) t := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsFiniteMeasure τ := by
    dsimp [τ]
    exact isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  let F : ℝ → ℝ → ℝ := fun r s => a s * f (min s r)
  let D : ℝ → ℝ := fun s => if t < s then a s * d else 0
  have hFm (r : ℝ) : AEStronglyMeasurable (F r) τ := by
    dsimp only [F]
    exact (ha.mul (hf.continuous.measurable.comp (measurable_id.min measurable_const))).aestronglyMeasurable
  have hFi : Integrable (F t) τ := by
    apply (integrable_const (‖f 0‖ + (K : ℝ))).mono' (hFm t)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    change ‖a s * f (min s t)‖ ≤ _
    have hm : min s t ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min hs.1.le ht.1.le, (min_le_left _ _).trans hs.2⟩
    have hnorm : ‖min s t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hm.1]
      exact hm.2
    have hff := hf.norm_sub_le (min s t) 0
    simp only [sub_zero] at hff
    have hv : ‖f (min s t)‖ ≤ ‖f 0‖ + (K : ℝ) := by
      have htri := norm_sub_le (f (min s t) - f 0) (-f 0)
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
      have hb := mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
      linarith
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hab s) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hv)
  have hDm : AEStronglyMeasurable D τ := by
    dsimp only [D]
    exact (ha.mul measurable_const).ite (isOpen_lt continuous_const continuous_id).measurableSet
      measurable_const |>.aestronglyMeasurable
  have hFL (s : ℝ) : LipschitzWith K (fun r => F r s) := by
    have hmin : LipschitzWith 1 (fun r : ℝ => min s r) := by
      exact LipschitzWith.const_min LipschitzWith.id s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (a s * f (min s x)) (a s * f (min s y)) ≤ _
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    have hh := (hf.comp hmin).norm_sub_le x y
    simp only [mul_one] at hh
    have hle := mul_le_mul_of_nonneg_left hh (norm_nonneg (a s))
    exact hle.trans (by
      rw [dist_eq_norm]
      exact (mul_le_mul_of_nonneg_right (hab s)
        (mul_nonneg K.coe_nonneg (norm_nonneg _))).trans_eq (one_mul _))
  have hdiff : ∀ᵐ s ∂τ, HasDerivAt (fun r => F r s) (D s) t := by
    filter_upwards [((volume : Measure ℝ).ae_ne t).filter_mono (ae_mono Measure.restrict_le_self)] with s hst
    rcases lt_or_gt_of_ne hst with hst | hts
    · have he : (fun r => F r s) =ᶠ[𝓝 t] (fun _ => a s * f s) := by
        filter_upwards [lt_mem_nhds hst] with r hr
        simp only [F, min_eq_left hr.le]
      simpa only [D, not_lt.mpr hst.le, ite_false] using
        (hasDerivAt_const t (a s * f s)).congr_of_eventuallyEq he
    · have he : (fun r => F r s) =ᶠ[𝓝 t] (fun r => a s * f r) := by
        filter_upwards [gt_mem_nhds hts] with r hr
        simp only [F, min_eq_right hr.le]
      simpa only [D, hts, ite_true] using (hfd.const_mul (a s)).congr_of_eventuallyEq he
  have hd := (hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := τ) (F := F) (F' := D) (bound := fun _ => (K : ℝ))
    (s := univ) (x₀ := t) (by simp)
    (Eventually.of_forall hFm) hFi hDm
    (Eventually.of_forall fun s => by
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using (hFL s).lipschitzOnWith)
    (integrable_const (K : ℝ)) hdiff).2
  have hDI : (∫ s, D s ∂τ) = d * ∫ s in t..1, a s := by
    have hset : Ioi t ∩ Ioc (0 : ℝ) 1 = Ioc t 1 := by
      ext s
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · intro hs
        exact ⟨hs.1, hs.2.2⟩
      · intro hs
        exact ⟨hs.1, ht.1.trans hs.1, hs.2⟩
    have he : D = (Ioi t).indicator (fun s => a s * d) := by
      funext s
      simp [D, Set.indicator]
    rw [he, integral_indicator measurableSet_Ioi]
    dsimp only [τ]
    rw [Measure.restrict_restrict measurableSet_Ioi, hset,
      ← intervalIntegral.integral_of_le ht.2.le, intervalIntegral.integral_mul_const, mul_comm]
  rw [hDI] at hd
  simpa only [F, τ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hd

/-- A strictly increasing covariance kernel detects every tail integral. -/
theorem tailIntegral_eq_zero_of_momentKernel_zero (a f g : ℝ → ℝ)
    (ha : Measurable a) (hab : ∀ s, ‖a s‖ ≤ 1)
    (K : ℝ≥0) (hf : LipschitzWith K f)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Ioo (0 : ℝ) 1, g t ≠ 0)
    (hz : ∀ t ∈ Ioo (0 : ℝ) 1, (∫ s in (0 : ℝ)..1, a s * f (min s t)) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) 1, (∫ s in t..1, a s) = 0 := by
  intro t ht
  have hder := hasDerivAt_momentKernel a f ha hab K hf t (g t) ht (hd t ht)
  have hzero : HasDerivAt (fun r => ∫ s in (0 : ℝ)..1, a s * f (min s r)) 0 t := by
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact hz r hr
  exact (mul_eq_zero.mp (hder.unique hzero)).resolve_left (hg t ht)

end FRSB
