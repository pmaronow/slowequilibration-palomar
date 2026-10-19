-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteCubeFubini
public import SlowEquilibration.SphericalPowerGG
public import SlowEquilibration.SphericalPerturbationCoordinateSlice
public import SlowEquilibration.GaussianPositiveParameterBudget
public import SlowEquilibration.GaussianGGParameterFamily

/-! The actual finite positive-parameter cube and its true tensor-Gibbs
power discrepancies. Coordinate slices, measurability and support are
proved from the genuine joint Gaussian Gibbs kernel. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianReplicaCalculus GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationDeviation GaussianPerturbationIntegrated
open GaussianGGEnsemble
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal product of the ordinary uniform laws on [1/2,1]. -/
def positiveCubeLaw (K : ℕ) : Measure (Fin K → ℝ) :=
  Measure.pi (fun _ => positiveParameterLaw)

instance positiveCubeLaw_probability (K : ℕ) : IsProbabilityMeasure (positiveCubeLaw K) := by
  unfold positiveCubeLaw
  infer_instance

 theorem positiveCubeLaw_support (K : ℕ) :
    ∀ᵐ x ∂positiveCubeLaw K, ∀p, x p∈Icc (1/2:ℝ) 1 := by
  apply ae_all_iff.mpr
  intro p
  exact ((measurePreserving_eval (fun _ : Fin K => positiveParameterLaw) p).hasLaw.ae_iff
    (measurableSet_setOfPred.mp measurableSet_Icc)).mpr positiveParameterLaw_support

 theorem positiveCubeLaw_abs_le_two (K : ℕ) :
    ∀ᵐ x ∂positiveCubeLaw K, ∀p, |x p|≤2 := (positiveCubeLaw_support K).mono fun x hx p => by
  have h := hx p
  rw [abs_of_nonneg (by linarith [h.1] : 0≤x p)]
  linarith [h.2]

 theorem update_one_abs_le_two {K : ℕ} (x : Fin K → ℝ) (hx : ∀p,|x p|≤2) (p : Fin K) :
    ∀j, |Function.update x p 1 j|≤2 := by
  intro j
  by_cases h : j=p
  · subst j
    rw [Function.update_self]
    norm_num
  · rw [Function.update_of_ne h]
    exact hx j

/-- The actual joint kernel slice equals the selected scalar-parameter
Gibbs kernel, including its true ambient unit-spin transport. -/
theorem ambient_kernel_coordinate_slice {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v)
    (x : Fin K → ℝ) (hx : ∀p,|x p|≤2) (p : Fin K) (t : ℝ) :
    (ambientParameterizedGibbsKernel ν v).sectR (Function.update x p t)=
      (gibbsKernel ν (parameterLinear (unitLinear (coefficients v (Function.update x p 1)))
        (degreeLabel p) t)).map Subtype.val := by
  let L := unitLinear (N := N) (coefficients v (Function.update x p 1))
  let Lx := parameterLinear L (degreeLabel p) t
  have hL : Measurable L := unitLinear_measurable _
  have hLx : Measurable Lx := parameterLinear_measurable L hL (degreeLabel p) t
  have hB : ∀ᵐ z ∂ν,‖Lx z‖≤(1+|t|)*(2*v) :=
    .of_forall (parameterLinear_pointwise_bound L (degreeLabel p) (by positivity)
      (unitLinear_norm_bound hv _ (update_one_abs_le_two x hx p)) t)
  apply Kernel.ext
  intro w
  rw [Kernel.sectR_apply,ambientParameterizedGibbsKernel,
    Kernel.map_apply _ measurable_subtype_coe,parameterizedGibbsKernel_active_slice ν hv,
    Kernel.map_apply _ measurable_subtype_coe,gibbsKernel_apply ν Lx hLx (by positivity) hB]

/-- The genuine model's tested-power error at an original full coefficient
vector, with Gaussian averaging at that vector. -/
def cubePowerDefect {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v ε : ℝ) (m q : ℕ) (x : Fin K → ℝ) : ℝ :=
  powerDefect (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((ambientParameterizedGibbsKernel ν v).sectR x) ε m q

def cubeMeanPowerDefect {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v ε : ℝ) (m q : ℕ) : ℝ := ∫x,cubePowerDefect ν v ε m q x ∂positiveCubeLaw K

 theorem cubePowerDefect_measurable {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v)
    (ε : ℝ) (m q : ℕ) : Measurable (cubePowerDefect (K := K) ν v ε m q) := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  exact powerDefect_measurable _ _ _ _ _

 theorem cubePowerDefect_nonneg {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v ε : ℝ) (m q : ℕ) (x : Fin K → ℝ) : 0≤cubePowerDefect ν v ε m q x :=
  powerDefect_nonneg _ _ _ _ _

/-- True ambient unit-spin support bounds every actual power-GG
error by two, even outside the positive coefficient cube. -/
theorem cubePowerDefect_le_two {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v)
    (ε : ℝ) (m q : ℕ) (x : Fin K → ℝ) : cubePowerDefect ν v ε m q x≤2 := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  apply powerDefect_le_two
  exact .of_forall fun w => (ambientParameterizedGibbsKernel_unit_support ν v (x,w)).mono
    (fun z hz => hz.le)

 theorem cubePowerDefect_integrable {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v)
    (ε : ℝ) (m q : ℕ) : Integrable (cubePowerDefect (K := K) ν v ε m q) (positiveCubeLaw K) := by
  apply Integrable.of_bound (cubePowerDefect_measurable ν hv ε m q).aestronglyMeasurable 2
  exact .of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (cubePowerDefect_nonneg _ _ _ _ _ _)]
    exact cubePowerDefect_le_two ν hv ε m q x

/-- Actual coordinate-slice power error; its covariance and diagonal are
proved by the tensor model, and its Gibbs kernel is identified internally. -/
theorem cubePowerDefect_coordinate_le {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀p,|x p|≤2) (p : Fin K) (t : ℝ) (ht : 0<t)
    (ε : ℝ) (m : ℕ) :
    cubePowerDefect ν v ε m (p.val+1) (Function.update x p t)≤
      totalDeviation ν (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) t/
        (((m:ℝ)+1)*t*(v^2*(1/4:ℝ)^(p.val+1))) := by
  rw [cubePowerDefect,ambient_kernel_coordinate_slice ν hv.le x hx p t]
  exact ambient_powerDefect_error_le ν hv (Function.update x p 1) (update_one_abs_le_two x hx p)
    p (Function.update_self p 1 x) t ht ε m

end SlowEquilibration.SphericalPositivePerturbation
