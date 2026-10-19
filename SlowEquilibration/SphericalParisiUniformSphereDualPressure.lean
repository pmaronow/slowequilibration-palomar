-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiFiniteMixtureDualPressure
public import SlowEquilibration.SphericalParisiSphereNetMaximum
public import SphericalAging.SphereSurfaceIdentification

/-! Transport the actual uniform physical sphere law through the unit-sphere
parameterization and identify the two ordered Gaussian tensor partition
functions. This supplies the missing reference-law step for the all-parity
one-step dual upper. It does not supply the Parisi lower bound. -/
@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalParisiUniformSphereDualPressure

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel PureTensorJetBounds FiniteTensorMixtureMaximum
open SphericalParisiFiniteMixtureGroundBridge
open SphericalParisiFiniteMixtureDualPressure
open SphericalParisiLabeledOriginalEndpoint
open SphericalParisiSphereNet
open SphericalAging.SphereSurfaceIdentification
open GaussianSpinInterpolation
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Euclidean surface law on the unit sphere. -/
def unitSphereProbability (N : ℕ) : Measure (UnitSphere N) :=
  ((unitSurface N) univ)⁻¹ • unitSurface N

/-- Physical radius-sqrt(N) embedding. -/
def physicalAxis {N : ℕ} (u : UnitSphere N) : Vector N :=
  Real.sqrt (N : ℝ) • (u : Vector N)

theorem physicalAxis_measurable (N : ℕ) :
    Measurable (physicalAxis (N := N)) := by
  unfold physicalAxis
  fun_prop

/-- The pushforward is precisely the manuscript's normalized Gaussian
sphere law. The surface normalization is inherited from its proven polar
coordinate disintegration. -/
theorem unitSphereProbability_physical_map {N : ℕ} (hN : 1 ≤ N) :
    (unitSphereProbability N).map (physicalAxis (N := N)) = sphereLaw N := by
  change (((unitSurface N) univ)⁻¹ • unitSurface N).map
    (fun θ => Real.sqrt N • θ.1) = SphericalAging.SphereInitialLaw.sphereLaw N
  exact (sphereLaw_eq_normalizedSurface hN).symm

theorem unitSphereProbability_isProbability {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (unitSphereProbability N) := by
  have hm := congrArg (fun ν : Measure (Vector N) => ν univ)
    (unitSphereProbability_physical_map hN)
  rw [Measure.map_apply (physicalAxis_measurable N) MeasurableSet.univ] at hm
  simp only [preimage_univ, measure_univ] at hm
  constructor
  exact hm

/-- The exact physical Hamiltonian at sqrt(N) times a unit vector equals
the true ordered-Gaussian feature field, sample by sample. -/
theorem tensor_spin_field_eq_physical {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (u : UnitSphere N)
    (g : EuclideanDisorder N μ.maxDegree) :
    inner ℝ (feature (tensorDegree μ) (tensorCoefficient μ) u.val) g =
      field (mixtureCoefficients μ) (unpackDisorder g) (physicalAxis u) := by
  have hd : ∀ p, 1 ≤ tensorDegree μ p := by
    intro p
    have hp := tensorDegree_ge_two μ p
    omega
  rw [original_field_eq_sum_scaledHamiltonians hN
    (tensorDegree μ) (tensorCoefficient μ) hd]
  rfl

/-- Exact log partition transport before averaging over the original
Gaussian coordinates. -/
theorem tensor_spin_logPartition_eq_physical {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (g : EuclideanDisorder N μ.maxDegree) :
    logPartition (unitSphereProbability N)
      (spinLinear (tensorDegree μ) (tensorCoefficient μ) β) g =
      Real.log (partition N β (field (mixtureCoefficients μ) (unpackDisorder g))) := by
  unfold GaussianSpinInterpolation.logPartition
  apply congrArg Real.log
  unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight partition
  simp only [one_mul]
  rw [← unitSphereProbability_physical_map hN]
  have hExp : StronglyMeasurable (fun x : Vector N =>
      Real.exp (β * field (mixtureCoefficients μ) (unpackDisorder g) x)) := by
    exact (Real.continuous_exp.comp
      ((field_contDiff (mixtureCoefficients μ) (unpackDisorder g)).continuous.const_mul β)).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable (physicalAxis_measurable N) hExp]
  apply integral_congr_ae
  exact .of_forall fun u => by
    simp only [spinLinear, innerSL_apply_apply,
      real_inner_smul_left, tensor_spin_field_eq_physical (by omega) μ u g]

/-- The actual tensor-feature pressure against normalized surface measure
is exactly N times the canonical quenched pressure of the original finite
mixture. -/
theorem uniform_originalSpinPressure_eq_quenchedPressure {N : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    originalSpinPressure (unitSphereProbability N)
      (tensorDegree μ) (tensorCoefficient μ) β / (N : ℝ) =
      quenchedPressure N μ β := by
  rw [originalSpinPressure]
  change (∫ g : EuclideanDisorder N μ.maxDegree,
    logPartition (unitSphereProbability N)
      (spinLinear (tensorDegree μ) (tensorCoefficient μ) β) g
      ∂SYK.standardGaussianMeasureOnEuclidean
        (SphericalModel.Coordinate N μ.maxDegree)) / (N : ℝ) = _
  rw [integral_congr_ae (.of_forall
    (tensor_spin_logPartition_eq_physical hN μ β))]
  have he := gaussianMeanLogPartition_eq_quenchedPressure hN μ β
  convert he using 1
  unfold GaussianSpinInterpolation.averagedLogPartition
  congr 1
  apply integral_congr_ae
  exact .of_forall fun g => by
    unfold GaussianSpinInterpolation.logPartition
    simp only [gaussianMoment_eq_partition]

/-- A genuine uniform-sphere all-parity physical pressure upper for each
positive one-step dual trial. The full CS infimum/equality in source 3.14
still requires the arbitrary-order upper and the physical lower bound. -/
theorem eventual_quenchedPressure_div_beta_le_sourceDual
    (μ : FiniteMixture)
    {α β κ q ε : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ - α * (μ.xi1 1 - μ.xi1 q))
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      quenchedPressure N μ β / β ≤ sourceDual μ α q κ + ε := by
  have hν : ∀ N, 0 < N → IsProbabilityMeasure (unitSphereProbability N) :=
    fun N hN => unitSphereProbability_isProbability (by omega)
  have H := eventual_tensor_pressure_le_sourceDual μ unitSphereProbability
    hν hα hαβ hq hq1 hmargin hε
  filter_upwards [H, eventually_ge_atTop (1 : ℕ)] with N hupper hN
  rw [← uniform_originalSpinPressure_eq_quenchedPressure hN μ β]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hβ : 0 < β := hα.trans_le hαβ
  convert hupper using 1
  field_simp [hNr, hβ.ne']

end SlowEquilibration.SphericalParisiUniformSphereDualPressure
