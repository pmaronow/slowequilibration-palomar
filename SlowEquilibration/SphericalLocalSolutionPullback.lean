-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalStrongSolutionPullback

/-! A local strong solution of an actual matrix-driven SDE transports
along a measure-preserving filtered map of Brownian sample spaces. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalAging.FilteredItoPullback
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {N : ℕ} {Ω Ω' : Type*}
  [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΩ'}
  {φ : Ω' → Ω}

theorem localStrongSolution_pullback
    (hφ : MeasurePreserving φ Q P)
    (hF : ∀ t, @Measurable Ω' Ω (G t) (F t) φ)
    (D : BrownianDriver N P F) (E : BrownianDriver N Q G)
    (hB : ∀ i t, E.coordinate i t =ᵐ[Q]
      fun ω => D.coordinate i t (φ ω))
    (b : Fin N → State N → ℝ)
    (sigma : Fin N → Fin N → State N → ℝ)
    (hsigma : ∀ i j, Continuous (sigma i j))
    (x : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsLocalStrongSolutionOn b sigma hsigma D x X T) :
    IsLocalStrongSolutionOn b sigma hsigma E x
      (fun s ω => X s (φ ω)) T := by
  rcases hsol with ⟨hXa,hXc,hbmem,hsigmamem,heq⟩
  let Y : ℝ≥0 → Ω' → State N := fun s ω => X s (φ ω)
  let hYa : StronglyAdapted G Y := fun s =>
    (hXa s).comp_measurable (hF s)
  let hYc : ∀ᵐ ω ∂Q, Continuous (fun s => Y s ω) :=
    hφ.quasiMeasurePreserving.ae hXc
  let hsigmamemY : ∀ i j (t : ℝ≥0), t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => sigma i j (Y s ω)) t) 2
      (nonnegativeLebesgueMeasure.prod Q) :=
    fun i j t ht => coefficientTimeCut_pullback_memLp hφ X (sigma i j) t
      (hsigmamem i j t ht)
  refine ⟨hYa,hYc,
    (fun i => coefficientTimeCut_pullback_memLp hφ X (b i) T (hbmem i)),
    hsigmamemY,?_⟩
  intro t ht i
  have hcoeff (j : Fin N) :
      coefficientPredictableActual hYa hYc (hsigma i j) t
        (hsigmamemY i j t ht) =
      predictablePullback hφ hF
        (coefficientPredictableActual hXa hXc (hsigma i j) t
          (hsigmamem i j t ht)) :=
    coefficientPredictableActual_pullback hφ hF X hXa hXc
      (sigma i j) (hsigma i j) t (hsigmamem i j t ht)
  have hnoise :
      driverItoMap E (fun j => coefficientPredictableActual hYa hYc
        (hsigma i j) t (hsigmamemY i j t ht)) =
      randomPullback hφ (driverItoMap D
        (fun j => coefficientPredictableActual hXa hXc
          (hsigma i j) t (hsigmamem i j t ht))) := by
    simp only [hcoeff, SphericalAging.CutoffSphere.driverItoMap_eq_vectorIto]
    exact vectorIto_predictablePullback hφ hF D E hB _
  filter_upwards [hφ.quasiMeasurePreserving.ae (heq t ht i),
    randomPullback_coe hφ (driverItoMap D
      (fun j => coefficientPredictableActual hXa hXc
        (hsigma i j) t (hsigmamem i j t ht)))] with ω he hI
  rw [hnoise,hI]
  exact he

end SlowEquilibration.SphericalRotationCovariance
