-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacGenerator

/-! The literal Feynman--Kac weight on the manuscript's original mixed
tensor diffusion, and its true infinitesimal physical C² generator. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalRotationCovariance SphericalReversibility SphericalReversibility.Ito
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- The previously constructed joint Picard representative of the
original physical process, with the original Wiener probability law. -/
def sourceProcess (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) : ℝ≥0 → VectorBrownian.Space N → Vector N :=
  jointMixedProcess μ β (J,x)

theorem sourceProcess_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) : Measurable (Function.uncurry (sourceProcess μ J β x)) := by
  exact (jointMixedProcess_measurable μ β).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

theorem sourceProcess_ae_actual (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, sourceProcess μ J β x t ω = mixedProcess μ J β x t ω :=
  jointMixedProcess_ae_actual μ β (J,x)

theorem sourceProcess_ae_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) :
    ∀ᵐ ω ∂VectorBrownian.law N, Continuous (fun t => sourceProcess μ J β x t ω) := by
  filter_upwards [sourceProcess_ae_actual μ J β x,mixedProcess_continuous μ J β x]
    with ω he hc
  exact hc.congr (fun t => (he t).symm)

theorem sourceProcess_zero (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) : sourceProcess μ J β x 0 =ᵐ[VectorBrownian.law N] fun _ => x := by
  filter_upwards [sourceProcess_ae_actual μ J β x,mixedProcess_zero μ J β x] with ω he h0
  exact (he 0).trans h0

theorem sourceProcess_onSphere (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, OnSphere (sourceProcess μ J β x t ω) := by
  filter_upwards [sourceProcess_ae_actual μ J β x,mixedProcess_onSphere hN μ J β x hx]
    with ω he hs
  intro t
  rw [he t]
  exact hs t

/-- Killing is integrated along the actual physical trajectories, rather
than introduced as an operator with a supplied identification. -/
def sourceKilledExpectation (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (κ : Vector N → ℝ) (t : ℝ≥0) (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  killedExpectation (VectorBrownian.law N) κ (sourceProcess μ J β x) t f

theorem sourceKilledExpectation_eq_actual (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (κ : Vector N → ℝ) (t : ℝ≥0) (f : Vector N → ℝ) (x : Vector N) :
    sourceKilledExpectation μ J β κ t f x =
      ∫ ω, survival κ (mixedProcess μ J β x) t ω * f (mixedProcess μ J β x t ω)
        ∂VectorBrownian.law N := by
  apply integral_congr_ae
  filter_upwards [sourceProcess_ae_actual μ J β x] with ω he
  have ho : occupation κ (sourceProcess μ J β x) t ω =
      occupation κ (mixedProcess μ J β x) t ω := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrArg κ (he s.toNNReal)
  simp only [survival,ho,he t]

theorem sourceKilledExpectation_generator_zero (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) (hx : OnSphere x)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ y, 0 ≤ κ y)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ y, ‖κ y‖ ≤ K)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun r : ℝ => sourceKilledExpectation μ J β κ r.toNNReal f x)
      (coefficientGenerator β (mixedGradient μ J) f x - κ x * f x) (Ici 0) 0 := by
  obtain ⟨C0,hC0⟩ := (physicalSphere_compact N).exists_bound_of_continuousOn hf.continuous.continuousOn
  let C : ℝ := max C0 0
  have hC : ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, ‖f (sourceProcess μ J β x t ω)‖ ≤ C := by
    filter_upwards [sourceProcess_onSphere hN μ J β x hx] with ω hs
    intro t
    exact (hC0 _ (hs t)).trans (le_max_left _ _)
  have he (t : ℝ≥0) : (∫ ω, f (sourceProcess μ J β x t ω) ∂VectorBrownian.law N) =
      SphericalC1Dynamics.expectation β (mixedGradient μ J)
        ((mixedGradient_contDiff μ J).of_le (by simp)) t f x := by
    rw [SphericalC1Dynamics.expectation_eq_mixed hN μ J β x hx,mixedExpectation_eq_actual]
    apply integral_congr_ae
    exact (sourceProcess_ae_actual μ J β x).mono (fun _ h => congrArg f (h t))
  have hd := SphericalC1Dynamics.expectation_hasDerivWithinAt_zero hN β
    (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) x hx hf
  have hd' : HasDerivWithinAt
      (fun r : ℝ => ∫ ω, f (sourceProcess μ J β x r.toNNReal ω) ∂VectorBrownian.law N)
      (coefficientGenerator β (mixedGradient μ J) f x) (Ici 0) 0 :=
    hd.congr_of_eventuallyEq (.of_forall (fun r => he r.toNNReal))
      (by simpa only [Real.toNNReal_zero] using he 0)
  exact killedExpectation_hasDerivWithinAt_zero (VectorBrownian.law N) κ hκ hκ0 K hK0 hK
    (sourceProcess μ J β x) (sourceProcess_measurable μ J β x)
    (sourceProcess_ae_continuous μ J β x) x (sourceProcess_zero μ J β x)
    f hf.continuous C (le_max_right _ _) hC _ hd'

end SlowEquilibration.ConditionedEntrance.FeynmanKac
