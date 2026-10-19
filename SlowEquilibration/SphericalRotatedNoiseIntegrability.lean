-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRotatedPhysicalSolution

/-! The rotated physical noise is square integrable on every finite time
horizon for a sphere-valued adapted continuous path. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open Set MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalModel
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem boundedCoefficient_timeCut_memLp
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (g : State N → ℝ) (hg : Continuous g)
    (K T : ℝ≥0)
    (hbound : ∀ᵐ ω ∂P, ∀ s, s ≤ T → ‖g (X s ω)‖ ≤ K) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => g (X s ω)) T) 2
      (nonnegativeLebesgueMeasure.prod P) := by
  have hsm := FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
    (fun s ω => g (X s ω))
    (fun s => hg.comp_stronglyMeasurable (hXa s))
    (hXc.mono (fun ω hc => hg.comp hc)) T
  have hconst := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (K : ℝ)
    (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))
  apply hconst.mono' (hsm.mono (predictable_le_prod F))
  have hcommon := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hbound
  filter_upwards [hcommon] with z hz
  by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show z ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from
      ⟨ht, mem_univ _⟩)]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true]
    exact hz z.1 ht.2
  · rw [indicator_of_notMem (show z ∉ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from
      fun h => ht h.1)]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,norm_zero]
    exact le_rfl

theorem sphere_rotatedNoise_timeCut_memLp (hN : N ≠ 0)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ s, OnSphere (X s ω))
    (k j : Fin N) (T : ℝ≥0) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => (noiseColumn (U (X s ω)) j) k) T) 2
      (nonnegativeLebesgueMeasure.prod P) := by
  let Y : ℝ≥0 → Ω → State N := fun s ω => U (X s ω)
  let hYa : StronglyAdapted F Y :=
    fun s => U.continuous.comp_stronglyMeasurable (hXa s)
  let hYc : ∀ᵐ ω ∂P, Continuous (fun s => Y s ω) :=
    hXc.mono (fun _ hc => U.continuous.comp hc)
  have hbound : ∀ᵐ ω ∂P, ∀ s, s ≤ T →
      ‖(noiseColumn (Y s ω) j) k‖ ≤ Real.sqrt 2 := by
    filter_upwards [hSphere] with ω hω
    intro s _
    exact (PiLp.norm_apply_le _ k).trans
      (noiseColumn_norm_le_onSphere hN _ (onSphere_map U (hω s)) j)
  exact boundedCoefficient_timeCut_memLp Y hYa hYc
    (fun v => (noiseColumn v j) k)
    (SphericalAging.CutoffSphere.physical_noise_continuous k j)
    ⟨Real.sqrt 2,Real.sqrt_nonneg 2⟩ T hbound

end SlowEquilibration.SphericalRotationCovariance
