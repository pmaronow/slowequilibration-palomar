-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRotatedCoefficientAlgebra

/-! Transport of the literal spherical matrix Itô term when both the
physical state and every independent Brownian coordinate are rotated. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalAging.VectorIto
open SphericalAging.CutoffSphere
open SphericalModel
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem physicalNoiseIto_rotated
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (D E : BrownianDriver N P F)
    (hB : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => ∑ i : Fin N, (U (basisVector i)) j * D.coordinate i t ω)
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (t : ℝ≥0)
    (hnX : ∀ a i, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => (noiseColumn (X s ω) i) a) t) 2
      (nonnegativeLebesgueMeasure.prod P))
    (hnY : ∀ k j, MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => (noiseColumn (U (X s ω)) j) k) t) 2
      (nonnegativeLebesgueMeasure.prod P))
    (k : Fin N) :
    let Y : ℝ≥0 → Ω → State N := fun s ω => U (X s ω)
    let hYa : StronglyAdapted F Y := fun s => U.continuous.comp_stronglyMeasurable (hXa s)
    let hYc : ∀ᵐ ω ∂P, Continuous (fun s => Y s ω) :=
      hXc.mono (fun _ hc => U.continuous.comp hc)
    driverItoMap E (fun j => coefficientPredictableActual hYa hYc
      (physical_noise_continuous k j) t (hnY k j)) =
      ∑ a : Fin N, (U (basisVector a)) k •
        driverItoMap D (fun i => coefficientPredictableActual hXa hXc
          (physical_noise_continuous a i) t (hnX a i)) := by
  dsimp only
  rw [SphericalAging.CutoffSphere.driverItoMap_eq_vectorIto]
  simp only [SphericalAging.CutoffSphere.driverItoMap_eq_vectorIto]
  rw [vectorIto_mixed D E (fun j i => (U (basisVector i)) j) hB]
  have hrow (i : Fin N) :
      (∑ j : Fin N, (U (basisVector i)) j •
        coefficientPredictableActual
          (fun s => U.continuous.comp_stronglyMeasurable (hXa s))
          (hXc.mono (fun _ hc => U.continuous.comp hc))
          (physical_noise_continuous k j) t (hnY k j)) =
      ∑ a : Fin N, (U (basisVector a)) k •
        coefficientPredictableActual hXa hXc
          (physical_noise_continuous a i) t (hnX a i) := by
    let Y : ℝ≥0 → Ω → State N := fun s ω => U (X s ω)
    let hYa : StronglyAdapted F Y :=
      fun s => U.continuous.comp_stronglyMeasurable (hXa s)
    let hYc : ∀ᵐ ω ∂P, Continuous (fun s => Y s ω) :=
      hXc.mono (fun _ hc => U.continuous.comp hc)
    let GY : State N → ℝ := fun v =>
      ∑ j : Fin N, (U (basisVector i)) j * (noiseColumn v j) k
    let GX : State N → ℝ := fun v =>
      ∑ a : Fin N, (U (basisVector a)) k * (noiseColumn v i) a
    have hGY : Continuous GY := by
      apply continuous_finsetSum
      intro j _
      exact continuous_const.mul (physical_noise_continuous k j)
    have hGX : Continuous GX := by
      apply continuous_finsetSum
      intro a _
      exact continuous_const.mul (physical_noise_continuous a i)
    have hGYeq (v : State N) :
        GY v = ∑ j : Fin N, (U (basisVector i)) j * (noiseColumn v j) k := rfl
    have hGXeq (v : State N) :
        GX v = ∑ a : Fin N, (U (basisVector a)) k * (noiseColumn v i) a := rfl
    have hGrel (v : State N) : GY (U v) = GX v :=
      (noiseColumn_rotated_double_sum U v i k).symm
    let hmGY := coefficientTimeCut_finsetLinear_memLp Y
      (fun j v => (noiseColumn v j) k) GY
      (fun j => (U (basisVector i)) j) hGYeq t (hnY k)
    let hmGX := coefficientTimeCut_finsetLinear_memLp X
      (fun a v => (noiseColumn v i) a) GX
      (fun a => (U (basisVector a)) k) hGXeq t (fun a => hnX a i)
    have hleft :
        coefficientPredictableActual hYa hYc hGY t hmGY =
        ∑ j : Fin N, (U (basisVector i)) j •
          coefficientPredictableActual hYa hYc
            (physical_noise_continuous k j) t (hnY k j) :=
      coefficientPredictableActual_finsetLinear Y hYa hYc
        (fun j v => (noiseColumn v j) k) GY
        (fun j => physical_noise_continuous k j) hGY
        (fun j => (U (basisVector i)) j) hGYeq t (hnY k)
    have hright :
        coefficientPredictableActual hXa hXc hGX t hmGX =
        ∑ a : Fin N, (U (basisVector a)) k •
          coefficientPredictableActual hXa hXc
            (physical_noise_continuous a i) t (hnX a i) :=
      coefficientPredictableActual_finsetLinear X hXa hXc
        (fun a v => (noiseColumn v i) a) GX
        (fun a => physical_noise_continuous a i) hGX
        (fun a => (U (basisVector a)) k) hGXeq t (fun a => hnX a i)
    calc
      _ = coefficientPredictableActual hYa hYc hGY t hmGY := hleft.symm
      _ = coefficientPredictableActual hXa hXc hGX t hmGX := by
        apply Subtype.ext
        apply Lp.ext
        filter_upwards [hmGY.coeFn_toLp,hmGX.coeFn_toLp] with z hy hx
        change (coefficientPredictableActual hYa hYc hGY t hmGY : TimeProcessL2 P) z = _ at hy
        change (coefficientPredictableActual hXa hXc hGX t hmGX : TimeProcessL2 P) z = _ at hx
        rw [hy,hx]
        change FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => GY (U (X s ω))) t z =
          FourPapersCommon.continuousAdaptedTimeCut
            (fun s ω => GX (X s ω)) t z
        simp only [FourPapersCommon.continuousAdaptedTimeCut,hGrel]
      _ = _ := hright
  simp only [hrow]
  simp only [vectorIto,map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

end SlowEquilibration.SphericalRotationCovariance
