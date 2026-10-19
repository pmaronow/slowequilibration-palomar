-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGKernelIdentity
public import SlowEquilibration.SphericalSelectedPerturbationKernel

/-! The genuine tensor perturbation gives every required positive-degree
power-GG test, on arbitrary ordinary unit-sphere spin probabilities.
Its covariance, constant diagonal and actual ambient IID law are proved
internally. Error normalization is n*t*v²4^(-degree). -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianReplicaCalculus GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationDeviation GaussianPerturbationIntegrated
open GaussianGGEnsemble GaussianGGStarRecursion
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal normalized overlap on the actual unit-sphere state space. -/
def unitOverlap {N : ℕ} (z y : UnitSpin N) : ℝ := inner ℝ z.val y.val

 theorem coefficient_sq_of_one {K : ℕ} (v : ℝ) (x : Fin K → ℝ) (p : Fin K) (hp : x p=1) :
    (coefficients v x p)^2=v^2*(1/4:ℝ)^(p.val+1) := by
  unfold coefficients
  rw [hp,mul_one,mul_pow,← pow_mul,pow_mul',show (1/2:ℝ)^2=1/4 by norm_num]

/-- Actual selected tensor covariance supplies the raw power-GG bound,
including arbitrary measurable hard-star tests. -/
theorem unit_powerGG_error_le {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀p,|x p|≤2) (p : Fin K) (hp : x p=1)
    (t : ℝ) (ht : 0<t) (m : ℕ)
    (f : (Fin (m+1) → UnitSpin N) → ℝ) (hf : Measurable f) (hfb : ∀σ,|f σ|≤1) :
    |powerGG ν (parameterLinear (unitLinear (coefficients v x)) (degreeLabel p) t)
      unitOverlap m (p.val+1) f|≤
      (meanThermalDeviation ν (unitLinear (coefficients v x)) (degreeLabel p) t+
        energyFluctuation ν (unitLinear (coefficients v x)) (degreeLabel p) t)/
        (((m:ℝ)+1)*t*(v^2*(1/4:ℝ)^(p.val+1))) := by
  have ha : 0<(coefficients v x p)^2 := by rw [coefficient_sq_of_one v x p hp];positivity
  have hcov (z y : UnitSpin N) := unit_selectedKernel (coefficients v x) p z y
  have hdiag (z : UnitSpin N) : unitOverlap z z=1 := by
    rw [unitOverlap,real_inner_self_eq_norm_sq,z.property];norm_num
  have hbase := powerGG_le_selected_deviation ν (unitLinear (coefficients v x))
    (unitLinear_measurable _) (by positivity : 0≤2*v)
    (unitLinear_norm_bound hv.le x hx) (degreeLabel p) unitOverlap (p.val+1)
    ((coefficients v x p)^2) t ha ht hcov hdiag m f hf hfb
  rw [coefficient_sq_of_one v x p hp] at hbase
  exact hbase

/-- Direct ambient hard-star power-GG error for the true Gaussian Gibbs
kernel, ready for the finite ordinary-measure positivity consumer. -/
theorem ambient_powerDefect_error_le {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀p,|x p|≤2) (p : Fin K) (hp : x p=1)
    (t : ℝ) (ht : 0<t) (ε : ℝ) (m : ℕ) :
    powerDefect (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((gibbsKernel ν (parameterLinear (unitLinear (coefficients v x)) (degreeLabel p) t)).map Subtype.val)
      ε m (p.val+1)≤
      (meanThermalDeviation ν (unitLinear (coefficients v x)) (degreeLabel p) t+
        energyFluctuation ν (unitLinear (coefficients v x)) (degreeLabel p) t)/
        (((m:ℝ)+1)*t*(v^2*(1/4:ℝ)^(p.val+1))) := by
  let L := unitLinear (N := N) (coefficients v x)
  let Lx := parameterLinear L (degreeLabel p) t
  have hL : Measurable L := unitLinear_measurable _
  have hLx : Measurable Lx := parameterLinear_measurable L hL (degreeLabel p) t
  have hb : ∀ᵐ z ∂ν,‖Lx z‖≤(1+|t|)*(2*v) :=
    .of_forall (parameterLinear_pointwise_bound L (degreeLabel p) (by positivity)
      (unitLinear_norm_bound hv.le x hx) t)
  let f : (Fin (m+1) → UnitSpin N) → ℝ := fun σ =>
    starObservable ε m (GaussianReplicaKernel.mapReplicas Subtype.val (m+1) σ)
  have hf : Measurable f := (starObservable_measurable ε m).comp
    (GaussianReplicaKernel.mapReplicas_measurable measurable_subtype_coe (m+1))
  have hfb (σ) : |f σ|≤1 := by
    have hmem := starObservable_mem ε m (GaussianReplicaKernel.mapReplicas Subtype.val (m+1) σ)
    change |starObservable ε m (GaussianReplicaKernel.mapReplicas Subtype.val (m+1) σ)|≤1
    rw [abs_of_nonneg hmem.1]
    exact hmem.2
  have hbase := unit_powerGG_error_le ν hv x hx p hp t ht m f hf hfb
  have hid := powerGG_abs_eq_powerDefect ν Lx hLx (by positivity) hb
    (Subtype.val : UnitSpin N → Vector N) measurable_subtype_coe (fun z => z.property.le) ε m (p.val+1)
  change |powerGG ν Lx (fun z y : UnitSpin N => inner ℝ z.val y.val) m (p.val+1) f|=_ at hid
  change |powerGG ν Lx (fun z y : UnitSpin N => inner ℝ z.val y.val) m (p.val+1) f|≤_ at hbase
  rw [hid] at hbase
  exact hbase

end SlowEquilibration.SphericalPositivePerturbation

namespace SlowEquilibration.GaussianGGEnsemble
open MeasureTheory ProbabilityTheory Set GaussianGGIndicatorTransfer

/-- The constant overlap test has exact zero error; no degree-zero
Gaussian perturbation is necessary. -/
theorem powerDefect_zero {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (ε : ℝ) (m : ℕ) : powerDefect d G ε m 0=0 := by
  unfold powerDefect
  simp only [pow_zero]
  rw [discrepancy_one,abs_zero]

end SlowEquilibration.GaussianGGEnsemble
