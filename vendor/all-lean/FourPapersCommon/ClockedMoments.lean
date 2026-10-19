module
public import FourPapersCommon.ClockedAdditiveState

@[expose] public section

/-! Actual square-integrable state and exact Brownian clock-increment moments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
open Paper

theorem norm_integratedDrift_le_of_bound {Ω : Type*} {μ : ℝ≥0 → Ω → ℝ}
    (D : ℝ≥0) (hD : ∀ s ω, ‖μ s ω‖ ≤ D) (T : ℝ≥0) (ω : Ω) :
    ‖integratedDrift μ T ω‖ ≤ D*(T : ℝ) := by
  rw [integratedDrift,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le T.coe_nonneg]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (T : ℝ)) (C := (D : ℝ)) (f := fun s => μ s.toNNReal ω)
    (fun s _ => hD s.toNNReal ω)
  simpa only [sub_zero,abs_of_nonneg T.coe_nonneg] using hn

theorem memLp_clockedItoState (d : AdditiveDriftData) (c : NonnegativeRate)
    (h T : ℝ) (hT : 0 ≤ T) (t : ℝ≥0) :
    MemLp (clockedItoState d c h T hT t) 2 canonicalBrownianMeasure := by
  have hi : MemLp (integratedDrift (clockedItoDrift d c h T hT) t) 2 canonicalBrownianMeasure :=
    .of_bound (stronglyMeasurable_integratedDrift (measurable_clockedItoDrift d c h T hT) t).aestronglyMeasurable
      ((d.radius : ℝ)*(t : ℝ)) (.of_forall fun ω =>
        norm_integratedDrift_le_of_bound d.radius (norm_clockedItoDrift_le d c h T hT) t ω)
  have he : clockedItoState d c h T hT t = fun ω => h+
      integratedDrift (clockedItoDrift d c h T hT) t ω+timeChangedBrownian (rateClock c) t ω := by
    funext ω
    rw [clockedItoState_decomposition,clockedItoState_zero]
  rw [he]
  exact ((memLp_const h).add hi).add (memLp_timeChangedBrownian _ t)

theorem centeredGaussian_square_integral (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  change Var[id;gaussianReal 0 v] = (v : ℝ) at hv
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  simp only [id_eq,integral_id_gaussianReal] at hv
  simpa only [sub_zero] using hv

theorem timeChangedBrownian_increment_square (A D : ℝ≥0 → ℝ≥0) (s t : ℝ≥0) :
    (∫ ω, (timeChangedBrownian A s ω-timeChangedBrownian D t ω)^2 ∂canonicalBrownianMeasure) =
      dist (A s) (D t) := by
  have hl := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_sub (A s) (D t)
  have he := hl.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)
  rw [centeredGaussian_square_integral] at he
  calc
    _ = ∫ ω, ((fun x : ℝ => x^2) ∘ (canonicalBrownian (A s)-canonicalBrownian (D t))) ω
        ∂canonicalBrownianMeasure := integral_congr_ae (.of_forall fun ω => rfl)
    _ = (nndist ((A s : ℝ≥0) : ℝ) ((D t : ℝ≥0) : ℝ) : ℝ) := he
    _ = dist (A s) (D t) := by rw [← dist_nndist,NNReal.dist_eq,Real.dist_eq]

theorem integrable_timeChangedBrownian_increment_square (A D : ℝ≥0 → ℝ≥0) (s t : ℝ≥0) :
    Integrable (fun ω => (timeChangedBrownian A s ω-timeChangedBrownian D t ω)^2) canonicalBrownianMeasure :=
  ((memLp_timeChangedBrownian A s).sub (memLp_timeChangedBrownian D t)).integrable_sq

theorem rateBrownian_increment_square_le (c d : NonnegativeRate) {T δ : ℝ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ‖c.rate s.toNNReal-d.rate s.toNNReal‖ ≤ δ)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) :
    (∫ ω, (timeChangedBrownian (rateClock c) t ω-timeChangedBrownian (rateClock d) t ω)^2
      ∂canonicalBrownianMeasure) ≤ δ*T := by
  rw [timeChangedBrownian_increment_square]
  exact rateClock_dist_le_of_rate_bound c d hT hδ hb t ht

end FourPapersCommon
