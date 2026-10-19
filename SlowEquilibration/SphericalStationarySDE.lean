-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPhysicalSpectral

@[expose] public section

/-! Literal Brownian-product realization of the physical stationary pair
law. The joint sample is the proved jointly measurable Picard solution
family, which agrees with the actual mixed SDE on every initial-state slice. -/

noncomputable section
namespace SlowEquilibration.SphericalStationarySDE

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalDynamics SphericalReversibility SphericalPhysicalSpectral
open SphericalAging SphericalAging.HardSphereDynamics
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

/-- The literal joint Picard sample on independent initial-state/Brownian
inputs; no transition-law realization is assumed. -/
def sample (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (t : ℝ≥0) (q : Vector N × VectorBrownian.Space N) : Vector N :=
  FixedCoefficients.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec q.1 t q.2

theorem sample_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : Measurable (sample μ J β t) :=
  FixedCoefficients.terminal_measurable _ _ _ t

/-- The joint sample is the actual mixed physical SDE, simultaneously for
all times on each initial-state slice. -/
theorem sample_ae_actual (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) :
    ∀ᵐ omega ∂VectorBrownian.law N, ∀ t,
      sample μ J β t (x,omega) = mixedProcess μ J β x t omega :=
  FixedCoefficients.jointProcess_ae _ _ _ x

/-- The conditional law of the actual joint Brownian sample is the literal
physical transition kernel, proved by the kernel's construction. -/
theorem sample_conditional_law (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (x : Vector N) :
    (VectorBrownian.law N).map (fun omega => sample μ J β t (x,omega)) =
      mixedTransitionKernel μ J β t x := by
  change (VectorBrownian.law N).map (fun omega => sample μ J β t (x,omega)) =
    ((Kernel.id ×ₖ Kernel.const (Vector N) (VectorBrownian.law N)).map (sample μ J β t)) x
  rw [Kernel.map_apply _ (sample_measurable μ J β t), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (sample_measurable μ J β t) measurable_prodMk_left]
  rfl

/-- The genuine stationary pair law is the law of the actual measurable
SDE sample with independent actual Gibbs initial state and Brownian path. -/
theorem twoTimeLaw_eq_brownian_product (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    ((mixtureGibbsLaw μ β J).prod (VectorBrownian.law N)).map
      (fun q => (q.1, sample μ J β t q)) = twoTimeLaw μ J β t := by
  have := mixtureGibbsLaw_probability hN μ β J
  have hm : Measurable (fun q : Vector N × VectorBrownian.Space N =>
      (q.1, sample μ J β t q)) := measurable_fst.prodMk (sample_measurable μ J β t)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  change _ = ((mixtureGibbsLaw μ β J) ⊗ₘ mixedTransitionKernel μ J β t) s
  rw [Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  rw [← sample_conditional_law μ J β t x]
  have hmx : Measurable (fun omega => sample μ J β t (x,omega)) :=
    (sample_measurable μ J β t).comp measurable_prodMk_left
  rw [Measure.map_apply hmx (measurable_prodMk_left hs)]
  rfl

end SlowEquilibration.SphericalStationarySDE
