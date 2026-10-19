-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRotatedNoiseIto

/-! Orthogonal covariance of the actual physical spherical strong-solution
equation under a simultaneously rotated vector Brownian driver. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open SphericalAging.CutoffSphere SphericalAging.VectorIto
open SphericalModel SphericalForm
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem physicalSolution_rotated
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (D E : BrownianDriver N P F)
    (hB : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => ∑ i : Fin N, (U (basisVector i)) j * D.coordinate i t ω)
    (β : ℝ) (g g' : State N → State N)
    (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ v, g' (U v) = U (g v))
    (x : State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsLocalStrongSolutionOn
      (fun a v => (drift β g v) a)
      (fun a i v => (noiseColumn v i) a) physical_noise_continuous
      D x X T)
    (hnY : ∀ k j t, t ≤ T → MemLp
      (FourPapersCommon.continuousAdaptedTimeCut
        (fun s ω => (noiseColumn (U (X s ω)) j) k) t) 2
      (nonnegativeLebesgueMeasure.prod P)) :
    IsLocalStrongSolutionOn
      (fun k v => (drift β g' v) k)
      (fun k j v => (noiseColumn v j) k) physical_noise_continuous
      E (U x) (fun s ω => U (X s ω)) T := by
  rcases hsol with ⟨hXa,hXc,hbmem,hsigmamem,heq⟩
  let Y : ℝ≥0 → Ω → State N := fun s ω => U (X s ω)
  let hYa : StronglyAdapted F Y :=
    fun s => U.continuous.comp_stronglyMeasurable (hXa s)
  let hYc : ∀ᵐ ω ∂P, Continuous (fun s => Y s ω) :=
    hXc.mono (fun _ hc => U.continuous.comp hc)
  have hdrift (v : State N) : drift β g' (U v) = U (drift β g v) := by
    simp only [drift,hgrad,← projection_map,map_sub,map_smul]
  have hpoint (k : Fin N) (v : State N) :
      (drift β g' (U v)) k =
      ∑ a : Fin N, (U (basisVector a)) k * (drift β g v) a := by
    rw [hdrift,rotated_coordinate_sum]
  let hbmemY (k : Fin N) :=
    coefficientTimeCut_finsetLinear_memLp X
      (fun a v => (drift β g v) a)
      (fun v => (drift β g' (U v)) k)
      (fun a => (U (basisVector a)) k) (hpoint k) T hbmem
  refine ⟨hYa,hYc,hbmemY,hnY,?_⟩
  intro t ht k
  have hIto := physicalNoiseIto_rotated U D E hB X hXa hXc t
    (fun a i => hsigmamem a i t ht) (fun a j => hnY a j t ht) k
  let V (a : Fin N) : RandomL2 P := driverItoMap D
    (fun i => coefficientPredictableActual hXa hXc
      (physical_noise_continuous a i) t (hsigmamem a i t ht))
  have hweighted :
      ((∑ a : Fin N, (U (basisVector a)) k • V a : RandomL2 P) : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ a : Fin N, (U (basisVector a)) k * (V a : Ω → ℝ) ω := by
    have hsmul : ∀ᵐ ω ∂P, ∀ a : Fin N,
        (((U (basisVector a)) k • V a : RandomL2 P) : Ω → ℝ) ω =
          (U (basisVector a)) k * (V a : Ω → ℝ) ω := by
      apply ae_all_iff.mpr
      intro a
      filter_upwards [Lp.coeFn_smul ((U (basisVector a)) k) (V a)] with ω hω
      simpa only [Pi.smul_apply,smul_eq_mul] using hω
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun a : Fin N => (U (basisVector a)) k • V a),hsmul] with ω hs hsmul
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun a _ => hsmul a)
  have hall : ∀ᵐ ω ∂P, ∀ a : Fin N,
      (X t ω) a = x a +
        (∫ s in (0 : ℝ)..(t : ℝ), (drift β g (X s.toNNReal ω)) a) +
        (V a : Ω → ℝ) ω :=
    ae_all_iff.mpr (fun a => heq t ht a)
  have hbc (a : Fin N) : Continuous (fun v : State N => (drift β g v) a) :=
    (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) a).comp
      (SphericalC1Dynamics.contDiff_drift β g hg).continuous
  filter_upwards [hall,hweighted,hXc] with ω hall hweighted hc
  have hInt :
      (∫ s in (0 : ℝ)..(t : ℝ), (drift β g' (Y s.toNNReal ω)) k) =
        ∑ a : Fin N, (U (basisVector a)) k *
          (∫ s in (0 : ℝ)..(t : ℝ), (drift β g (X s.toNNReal ω)) a) := by
    simp_rw [show ∀ s : ℝ,
      (drift β g' (Y s.toNNReal ω)) k =
        ∑ a : Fin N, (U (basisVector a)) k *
          (drift β g (X s.toNNReal ω)) a from fun s => hpoint k (X s.toNNReal ω)]
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro a _
      exact (((hbc a).comp (hc.comp continuous_real_toNNReal)).intervalIntegrable
        (0 : ℝ) (t : ℝ)).const_mul _
  have hItoAt := congrArg (fun Z : RandomL2 P => (Z : Ω → ℝ) ω) hIto
  change (Y t ω) k = (U x) k +
    (∫ s in (0 : ℝ)..(t : ℝ), (drift β g' (Y s.toNNReal ω)) k) +
    (driverItoMap E (fun j => coefficientPredictableActual hYa hYc
      (physical_noise_continuous k j) t (hnY k j t ht)) : Ω → ℝ) ω
  rw [rotated_coordinate_sum U (X t ω) k,
    rotated_coordinate_sum U x k,hInt,hItoAt,hweighted]
  calc
    (∑ a : Fin N, (U (basisVector a)) k * (X t ω) a) =
        ∑ a : Fin N, (U (basisVector a)) k *
          (x a +
            (∫ s in (0 : ℝ)..(t : ℝ), (drift β g (X s.toNNReal ω)) a) +
            (V a : Ω → ℝ) ω) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hall a]
    _ = (∑ a : Fin N, (U (basisVector a)) k * x a) +
        (∑ a : Fin N, (U (basisVector a)) k *
          (∫ s in (0 : ℝ)..(t : ℝ), (drift β g (X s.toNNReal ω)) a)) +
        (∑ a : Fin N, (U (basisVector a)) k * (V a : Ω → ℝ) ω) := by
          simp only [mul_add,Finset.sum_add_distrib]

end SlowEquilibration.SphericalRotationCovariance
