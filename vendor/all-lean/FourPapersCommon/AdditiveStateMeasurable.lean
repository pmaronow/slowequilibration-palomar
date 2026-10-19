module
public import FourPapersCommon.AdditiveState

@[expose] public section

/-! Continuous dependence and measurable causal evaluation of the genuine additive state. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal Nat
namespace FourPapersCommon
open Paper

theorem additiveNoiseDrift_noise_dist_le (d : AdditiveDriftData) {T : ℝ} (hT : 0 ≤ T)
    (w z : C(Icc (0 : ℝ) T,ℝ)) (s y : ℝ) :
    dist (additiveNoiseDrift d (parisiNoiseExtension hT w) s y)
      (additiveNoiseDrift d (parisiNoiseExtension hT z) s y) ≤
      (d.radius : ℝ)*(d.gradientLip : ℝ)*dist w z := by
  have hn := ContinuousMap.dist_apply_le_dist (f := w) (g := z) (projIcc 0 T hT s)
  have hl := (d.gradient_lipschitz s).dist_le_mul
    (y+parisiNoiseExtension hT w s) (y+parisiNoiseExtension hT z s)
  rw [dist_add_left] at hl
  unfold additiveNoiseDrift
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have hh : ‖d.gradient s (y+parisiNoiseExtension hT w s)-
      d.gradient s (y+parisiNoiseExtension hT z s)‖ ≤ (d.gradientLip : ℝ)*dist w z := by
    rw [← dist_eq_norm]
    exact hl.trans (mul_le_mul_of_nonneg_left hn d.gradientLip.2)
  exact (mul_le_mul (d.coefficient_bound s) hh (norm_nonneg _) d.radius.2).trans_eq (by ring)

/-- The actual state depends Lipschitz continuously on its noise path. -/
theorem exists_lipschitzWith_additiveStatePath (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ≥0, LipschitzWith C (additiveStatePath d h T hT) := by
  let K := d.radius*d.gradientLip
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hden : 0 < 1 - ((K : ℝ) * T) ^ n / n ! := sub_pos.mpr hn
  let A := IntegralPicard.sensitivity K T n / (1 - ((K : ℝ) * T) ^ n / n !) * ((d.radius : ℝ)*(d.gradientLip : ℝ)) + 1
  have hA : 0 ≤ A := by
    exact add_nonneg (mul_nonneg (div_nonneg (IntegralPicard.sensitivity_nonneg hT n) hden.le)
      (mul_nonneg d.radius.2 d.gradientLip.2)) zero_le_one
  refine ⟨⟨A, hA⟩, LipschitzWith.of_dist_le_mul fun w z => ?_⟩
  let hfW := isBoundedMeasurableDrift_additiveNoiseDrift d
    (parisiNoiseExtension hT w) (continuous_parisiNoiseExtension hT w)
  let hfZ := isBoundedMeasurableDrift_additiveNoiseDrift d
    (parisiNoiseExtension hT z) (continuous_parisiNoiseExtension hT z)
  have hδ : 0 ≤ (d.radius : ℝ)*(d.gradientLip : ℝ) * dist w z := by positivity
  have hb := IntegralPicard.solution_drift_dist_le (h := h) hT hfW hfZ _ hδ
    (additiveNoiseDrift_noise_dist_le d hT w z) n hn
  change dist _ _ ≤ A * dist w z
  apply (ContinuousMap.dist_le (mul_nonneg hA dist_nonneg)).mpr
  intro t
  change dist ((IntegralPicard.solution (h := h) hT hfW) t + w t)
    ((IntegralPicard.solution (h := h) hT hfZ) t + z t) ≤ A * dist w z
  have heval : dist ((IntegralPicard.solution (h := h) hT hfW) t)
      ((IntegralPicard.solution (h := h) hT hfZ) t) ≤ dist
      (IntegralPicard.solution (h := h) hT hfW) (IntegralPicard.solution (h := h) hT hfZ) :=
    ContinuousMap.dist_apply_le_dist (f := ODE.FunSpace.toContinuousMap _) (g := ODE.FunSpace.toContinuousMap _) t
  have hnoise : dist (w t) (z t) ≤ 1 * dist w z := by
    simpa only [one_mul] using ContinuousMap.dist_apply_le_dist (f := w) (g := z) t
  calc
    _ ≤ dist ((IntegralPicard.solution (h := h) hT hfW) t)
        ((IntegralPicard.solution (h := h) hT hfZ) t) + dist (w t) (z t) := dist_add_add_le _ _ _ _
    _ ≤ IntegralPicard.sensitivity K T n / (1 - ((K : ℝ) * T) ^ n / n !) *
        ((d.radius : ℝ)*(d.gradientLip : ℝ) * dist w z) + 1 * dist w z := add_le_add (heval.trans hb) hnoise
    _ = A * dist w z := by dsimp only [A]; ring

theorem continuous_additiveStatePath (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) :
    Continuous (additiveStatePath d h T hT) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_additiveStatePath d h T hT
  exact hC.continuous

theorem measurable_additiveStatePath (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) :
    Measurable (additiveStatePath d h T hT) :=
  (continuous_additiveStatePath d h T hT).measurable



/-- State evaluation computed measurably from just the noise history. -/
def additiveEndpointFromPast (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (w : C(Icc (0 : ℝ) (t : ℝ), ℝ)) : ℝ :=
  additiveStatePath d h T hT (parisiPastExtensionPath t w) t

theorem measurable_additiveEndpointFromPast (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) :
    Measurable (additiveEndpointFromPast d h T hT t) :=
  ((ContinuousMap.measurable_eval t).comp
    (measurable_additiveStatePath d h T hT)).comp
      (lipschitzWith_parisiPastExtensionPath t).continuous.measurable

/-- The actual state evaluation factors exactly through past noise. -/
theorem additiveStatePath_eval_eq_fromPast (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (w : C(Icc (0 : ℝ) T, ℝ)) :
    additiveStatePath d h T hT w t =
      additiveEndpointFromPast d h T hT t (parisiNoisePast t w) := by
  let W := parisiNoiseExtension hT w
  let z := parisiPastExtensionPath t (parisiNoisePast t w)
  let Z := parisiNoiseExtension hT z
  have hW : Continuous W := continuous_parisiNoiseExtension hT w
  have hZ : Continuous Z := continuous_parisiNoiseExtension hT z
  have hnoise : EqOn W Z (Icc (0 : ℝ) (t : ℝ)) := by
    intro s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.property.2⟩
    dsimp [W, Z, z, parisiNoiseExtension, parisiPastExtensionPath, parisiNoisePast]
    simp only [projIcc_of_mem hT hsT]
    change w ⟨s, hsT⟩ = w ⟨(projIcc (0 : ℝ) (t : ℝ) t.property.1 s : ℝ), _⟩
    simp only [projIcc_of_mem t.property.1 hs]
  change additiveStatePath d h T hT w t =
    additiveStatePath d h T hT z t
  simp only [additiveStatePath_apply]
  exact additiveStateReal_causal d h T hT t.property W Z hW hZ hnoise
    ⟨t.property.1, le_rfl⟩

theorem measurable_additiveState_eval_of_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) (W : Ω → C(Icc (0 : ℝ) T, ℝ))
    (hW : Measurable (fun ω => parisiNoisePast t (W ω))) :
    Measurable (fun ω => additiveStatePath d h T hT (W ω) t) := by
  simp_rw [additiveStatePath_eval_eq_fromPast]
  exact (measurable_additiveEndpointFromPast d h T hT t).comp hW


end FourPapersCommon
