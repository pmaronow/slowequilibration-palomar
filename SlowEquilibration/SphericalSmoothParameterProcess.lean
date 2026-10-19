-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothParameterCoefficients
public import SlowEquilibration.SphericalDisorderPathKernel

/-! Genuine joint parameter/initial-state Brownian representatives for any
actual finite-dimensional jointly C1 spherical gradient family. -/
@[expose] public section
namespace SlowEquilibration.SphericalSmoothParameter
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open SphericalModel SphericalDynamics SphericalC1Dynamics SphericalRotationCovariance
open SphericalAging HardSphereDynamics
open scoped Topology NNReal ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
variable {N : ℕ} {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [FiniteDimensional ℝ Θ] [MeasurableSpace Θ] [BorelSpace Θ]

omit [MeasurableSpace Θ] [BorelSpace Θ] in
theorem localizedFixedCondition (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g) (m : ℕ) :
    ∀ θ,∃ K : ℝ≥0,∀ i,LipschitzWith K (localizedDrift β g m θ i) :=
  fun θ=>⟨(localizedDrift_state_lipschitz β g hg m).choose,
    (localizedDrift_state_lipschitz β g hg m).choose_spec θ⟩

omit [MeasurableSpace Θ] [BorelSpace Θ] in
theorem localizedStateCondition (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g) (m : ℕ) :
    ∀ A : ℝ≥0,∃ K : ℝ≥0,∀ θ,‖θ‖ ≤ A → ∀ i,LipschitzWith K (localizedDrift β g m θ i) :=
  fun _=>⟨(localizedDrift_state_lipschitz β g hg m).choose,
    fun θ _ => (localizedDrift_state_lipschitz β g hg m).choose_spec θ⟩

@[irreducible] def localizedProcess (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g) (m : ℕ) :
    (Θ×Vector N) → ℝ≥0 → VectorBrownian.Space N → Vector N :=
  ParameterFamily.globalRepresentative (NullAugmentation.driver (VectorBrownian.driver N))
    (localizedDrift β g m) (localizedFixedCondition β g hg m) (localizedStateCondition β g hg m)
    (localizedDrift_parameter_lipschitz β g hg m)
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec

theorem localizedProcess_measurable (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) :
    Measurable (fun z : ((Θ×Vector N)×ℝ≥0)×VectorBrownian.Space N=>
      localizedProcess β g hg m z.1.1 z.1.2 z.2) := by
  unfold localizedProcess
  exact ParameterFamily.globalRepresentative_measurable _ _ _ _ _ _

omit [MeasurableSpace Θ] [BorelSpace Θ] in
theorem localizedGlobalProcess_ae_actual (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) (θ : Θ) (hθ : ‖θ‖ ≤ (m:ℝ)+1) (x : Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N,∀ t,
      GlobalSDE.process (NullAugmentation.driver (VectorBrownian.driver N))
        ((localizedFixedCondition β g hg m θ).choose_spec)
        (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x t ω =
      SphericalC1Dynamics.process β (fun y=>g (θ,y))
        (hg.comp (contDiff_const.prodMk contDiff_id)) x t ω := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := GlobalSDE.process D ((localizedFixedCondition β g hg m θ).choose_spec)
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x
  let Y := SphericalC1Dynamics.process β (fun y=>g (θ,y))
    (hg.comp (contDiff_const.prodMk contDiff_id)) x
  have hEq := localizedDrift_eq β g m θ hθ
  have hXY (l : ℕ) : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,t ≤ GlobalSDE.integerHorizon l → X t ω=Y t ω := by
    apply cutoffSolution_unique D β (fun y=>g (θ,y))
      (hg.comp (contDiff_const.prodMk contDiff_id)) x _ X Y
    · simpa only [X,hEq] using GlobalSDE.process_strongSolution D
        ((localizedFixedCondition β g hg m θ).choose_spec)
        (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x (GlobalSDE.integerHorizon l)
    · exact GlobalSDE.process_strongSolution D _ _ x _
  filter_upwards [ae_all_iff.mpr hXY] with ω hω
  intro t
  exact hω (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

theorem localizedProcess_ae_actual (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (m : ℕ) (θ : Θ) (hθ : ‖θ‖ ≤ (m:ℝ)+1) (x : Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N,∀ t,localizedProcess β g hg m (θ,x) t ω =
      SphericalC1Dynamics.process β (fun y=>g (θ,y))
        (hg.comp (contDiff_const.prodMk contDiff_id)) x t ω := by
  unfold localizedProcess ParameterFamily.globalRepresentative
  have hh := (ParameterFamily.exists_joint_global_process
    (NullAugmentation.driver (VectorBrownian.driver N)) (localizedDrift β g m)
    (localizedFixedCondition β g hg m) (localizedStateCondition β g hg m)
    (localizedDrift_parameter_lipschitz β g hg m)
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec).choose_spec.2 (θ,x)
  filter_upwards [hh,localizedGlobalProcess_ae_actual β g hg m θ hθ x] with ω he ha
  intro t
  exact (he t).trans (ha t)

@[irreducible] def jointProcess (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g)
    (q : Θ×Vector N) (t : ℝ≥0) (ω : VectorBrownian.Space N) : Vector N :=
  localizedProcess β g hg (parameterIndex q.1) q t ω

theorem jointProcess_measurable (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g) :
    Measurable (fun z : ((Θ×Vector N)×ℝ≥0)×VectorBrownian.Space N=>
      jointProcess β g hg z.1.1 z.1.2 z.2) := by
  unfold jointProcess
  have hm : Measurable (fun z : ℕ×(((Θ×Vector N)×ℝ≥0)×VectorBrownian.Space N)=>
      localizedProcess β g hg z.1 z.2.1.1 z.2.1.2 z.2.2) :=
    measurable_from_prod_countable_right (fun m=>localizedProcess_measurable β g hg m)
  exact hm.comp (((Nat.measurable_ceil.comp measurable_norm).comp measurable_fst.fst.fst).prodMk measurable_id)

theorem jointProcess_ae_actual (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g)
    (q : Θ×Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N,∀ t,jointProcess β g hg q t ω =
      SphericalC1Dynamics.process β (fun y=>g (q.1,y))
        (hg.comp (contDiff_const.prodMk contDiff_id)) q.2 t ω :=
  by
    unfold jointProcess
    exact localizedProcess_ae_actual β g hg (parameterIndex q.1) q.1 (parameterIndex_bound q.1) q.2

@[irreducible] def jointContinuousPath (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g) (T : ℝ≥0)
    (z : (Θ×Vector N)×VectorBrownian.Space N) : ContinuousPath N T :=
  (ContinuousFieldLaw.denseEvaluation_measurableEmbedding (K:=PathTime T) (V:=Vector N)).invFun
    (fun n=>jointProcess β g hg z.1 (denseSeq (PathTime T) n).1 z.2)

theorem jointContinuousPath_measurable (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) :
    Measurable (jointContinuousPath β g hg T) := by
  unfold jointContinuousPath
  apply (ContinuousFieldLaw.denseEvaluation_measurableEmbedding (K:=PathTime T) (V:=Vector N)).measurable_invFun.comp
  apply Measurable.of_eval
  intro n
  exact (jointProcess_measurable β g hg).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem jointContinuousPath_ae_actual (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (q : Θ×Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N,∀ t : PathTime T,
      jointContinuousPath β g hg T (q,ω) t=
        SphericalC1Dynamics.process β (fun y=>g (q.1,y))
          (hg.comp (contDiff_const.prodMk contDiff_id)) q.2 t.1 ω := by
  filter_upwards [jointProcess_ae_actual β g hg q,
    SphericalC1Dynamics.process_continuous β (fun y=>g (q.1,y))
      (hg.comp (contDiff_const.prodMk contDiff_id)) q.2] with ω he hc
  let p : ContinuousPath N T := ⟨fun t=>SphericalC1Dynamics.process β (fun y=>g (q.1,y))
    (hg.comp (contDiff_const.prodMk contDiff_id)) q.2 t.1 ω,hc.comp continuous_subtype_val⟩
  have hd : (fun n=>jointProcess β g hg q (denseSeq (PathTime T) n).1 ω)=ContinuousFieldLaw.denseEvaluation p := by
    funext n
    exact he _
  have hp : jointContinuousPath β g hg T (q,ω)=p := by
    unfold jointContinuousPath
    rw [hd]
    exact (ContinuousFieldLaw.denseEvaluation_measurableEmbedding (K:=PathTime T) (V:=Vector N)).leftInverse_invFun p
  intro t
  rw [hp]
  rfl

end
end SlowEquilibration.SphericalSmoothParameter
