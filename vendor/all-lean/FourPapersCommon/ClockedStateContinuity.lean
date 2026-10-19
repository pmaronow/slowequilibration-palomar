module
public import FourPapersCommon.ClockedMoments
public import FourPapersCommon.L2IntegralBounds

@[expose] public section

/-! Actual L² time continuity of the constructed clocked diffusion. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem norm_integratedDrift_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℝ≥0 → Ω → ℝ) (hm : Measurable (Function.uncurry μ))
    (D : ℝ≥0) (hD : ∀ s ω, ‖μ s ω‖ ≤ D) (s t : ℝ≥0) (ω : Ω) :
    ‖integratedDrift μ s ω-integratedDrift μ t ω‖ ≤ D*|(s : ℝ)-(t : ℝ)| := by
  let f : ℝ → ℝ := fun r => μ r.toNNReal ω
  have hi (r : ℝ) : IntervalIntegrable f volume 0 r :=
    (intervalIntegrable_const (c := (D : ℝ))).mono_fun'
      (hm.comp (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable
      (.of_forall fun r => hD r.toNNReal ω)
  have he (r : ℝ≥0) : integratedDrift μ r ω = ∫ x in 0..(r : ℝ), f x := by
    rw [integratedDrift,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le r.coe_nonneg]
  rw [he s,he t,intervalIntegral.integral_interval_sub_left (hi s) (hi t)]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hD r.toNNReal ω)

theorem clockedItoState_increment_square_le (d : AdditiveDriftData) (c : NonnegativeRate)
    (h T : ℝ) (hT : 0 ≤ T) (s t : ℝ≥0) :
    (∫ ω,(clockedItoState d c h T hT s ω-clockedItoState d c h T hT t ω)^2 ∂canonicalBrownianMeasure) ≤
      2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2+2*dist (rateClock c s) (rateClock c t) := by
  let μ := clockedItoDrift d c h T hT
  let X := clockedItoState d c h T hT
  let W := timeChangedBrownian (rateClock c)
  have hiX := ((memLp_clockedItoState d c h T hT s).sub (memLp_clockedItoState d c h T hT t)).integrable_sq
  have hiW := integrable_timeChangedBrownian_increment_square (rateClock c) (rateClock c) s t
  have hpoint (ω : BrownianSample) : (X s ω-X t ω)^2 ≤
      2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2+2*(W s ω-W t ω)^2 := by
    have hn := norm_integratedDrift_sub_le μ (measurable_clockedItoDrift d c h T hT)
      d.radius (norm_clockedItoDrift_le d c h T hT) s t ω
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg d.radius.2 (abs_nonneg _))).mpr hn
    simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hsq
    have he : X s ω-X t ω = (integratedDrift μ s ω-integratedDrift μ t ω)+(W s ω-W t ω) := by
      dsimp [X,μ,W]
      rw [clockedItoState_decomposition d c h T hT s ω,
        clockedItoState_decomposition d c h T hT t ω]
      ring
    rw [he]
    calc
      _ ≤ 2*(integratedDrift μ s ω-integratedDrift μ t ω)^2+2*(W s ω-W t ω)^2 := by
        nlinarith only [sq_nonneg ((integratedDrift μ s ω-integratedDrift μ t ω)-(W s ω-W t ω))]
      _ ≤ _ := by
        have hm2 : 2*(integratedDrift μ s ω-integratedDrift μ t ω)^2 ≤
            2*((d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2) :=
          mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)
        calc
          _ ≤ 2*((d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2)+2*(W s ω-W t ω)^2 :=
            add_le_add hm2 le_rfl
          _ = _ := by ring
  have hmono := integral_mono hiX
    ((integrable_const (2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2)).add (hiW.const_mul 2)) hpoint
  change (∫ ω,(X s ω-X t ω)^2 ∂canonicalBrownianMeasure) ≤
    (∫ ω,2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2+2*(W s ω-W t ω)^2 ∂canonicalBrownianMeasure) at hmono
  rw [integral_add (f := fun _ => 2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2)
    (g := fun ω => 2*(W s ω-W t ω)^2) (integrable_const _) (hiW.const_mul 2),
    integral_const,integral_const_mul] at hmono
  simp only [MeasureTheory.probReal_univ,one_smul] at hmono
  rw [timeChangedBrownian_increment_square] at hmono
  exact hmono

def clockedStateLp (d : AdditiveDriftData) (c : NonnegativeRate)
    (h T : ℝ) (hT : 0 ≤ T) (t : ℝ≥0) : Lp ℝ 2 canonicalBrownianMeasure :=
  (memLp_clockedItoState d c h T hT t).toLp (clockedItoState d c h T hT t)

theorem norm_sq_clockedStateLp_sub_le (d : AdditiveDriftData) (c : NonnegativeRate)
    (h T : ℝ) (hT : 0 ≤ T) (s t : ℝ≥0) :
    ‖clockedStateLp d c h T hT s-clockedStateLp d c h T hT t‖^2 ≤
      2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2+2*dist (rateClock c s) (rateClock c t) := by
  unfold clockedStateLp
  rw [norm_sq_sub_toLp]
  exact clockedItoState_increment_square_le d c h T hT s t

theorem continuous_clockedStateLp (d : AdditiveDriftData) (c : NonnegativeRate)
    (h T : ℝ) (hT : 0 ≤ T) : Continuous (clockedStateLp d c h T hT) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun s => ‖clockedStateLp d c h T hT s-clockedStateLp d c h T hT t‖^2)
      (𝓝 t) (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
      (norm_sq_clockedStateLp_sub_le d c h T hT · t)
    have hcts : Continuous (fun s : ℝ≥0 => 2*(d.radius : ℝ)^2*((s : ℝ)-(t : ℝ))^2+
        2*dist (rateClock c s) (rateClock c t)) := by
      exact ((continuous_const.mul ((NNReal.continuous_coe.sub continuous_const).pow 2)).add
        (continuous_const.mul ((continuous_rateClock c).dist continuous_const)))
    simpa using (hcts.continuousAt (x := t)).tendsto
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun s => Real.sqrt (‖clockedStateLp d c h T hT s-clockedStateLp d c h T hT t‖^2))
    (𝓝 t) (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

end FourPapersCommon
