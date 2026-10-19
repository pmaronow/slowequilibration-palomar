-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRotatedVectorIto
public import SphericalAging.BrownianDriverPullback

/-! Pullback of actual predictable coefficients along a measure-preserving
filtered Brownian sample map. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalAging.FilteredItoPullback SphericalAging.BrownianDriverPullback
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {N : ℕ} {Ω Ω' : Type*}
  [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'}
  {φ : Ω' → Ω}

theorem coefficientTimeCut_pullback_memLp
    (hφ : MeasurePreserving φ Q P)
    (X : ℝ≥0 → Ω → State N) (g : State N → ℝ) (t : ℝ≥0)
    (hmem : MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => g (X s ω)) t) 2 (nonnegativeLebesgueMeasure.prod P)) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => g (X s (φ ω))) t) 2 (nonnegativeLebesgueMeasure.prod Q) := by
  change MemLp ((FourPapersCommon.continuousAdaptedTimeCut
    (fun s ω => g (X s ω)) t) ∘ timeMap φ) 2
      (nonnegativeLebesgueMeasure.prod Q)
  exact hmem.comp_measurePreserving (timeMap_measurePreserving hφ)

theorem coefficientPredictableActual_pullback
    (hφ : MeasurePreserving φ Q P)
    (hF : ∀ t, @Measurable Ω' Ω (G t) (F t) φ)
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (g : State N → ℝ) (hg : Continuous g) (t : ℝ≥0)
    (hmem : MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => g (X s ω)) t) 2 (nonnegativeLebesgueMeasure.prod P)) :
    let Y : ℝ≥0 → Ω' → State N := fun s ω => X s (φ ω)
    let hYa : StronglyAdapted G Y := fun s => (hXa s).comp_measurable (hF s)
    let hYc : ∀ᵐ ω ∂Q,Continuous (fun s => Y s ω) := hφ.quasiMeasurePreserving.ae hXc
    let hmemY := coefficientTimeCut_pullback_memLp hφ X g t hmem
    coefficientPredictableActual hYa hYc hg t hmemY =
      predictablePullback hφ hF (coefficientPredictableActual hXa hXc hg t hmem) := by
  dsimp only
  apply Subtype.ext
  apply Lp.ext
  have hX := (timeMap_measurePreserving hφ).quasiMeasurePreserving.ae
    hmem.coeFn_toLp
  filter_upwards [(coefficientTimeCut_pullback_memLp hφ X g t hmem).coeFn_toLp,
    predictablePullback_coe hφ hF (coefficientPredictableActual hXa hXc hg t hmem),
    hX] with z hY hR hX
  exact hY.trans (hX.symm.trans hR.symm)

end SlowEquilibration.SphericalRotationCovariance
