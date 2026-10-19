-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import SlowEquilibration.SphericalRayleighComparison

@[expose] public section

/-! # Exact Gibbs normalization of the actual weighted source law -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open scoped Topology ContDiff ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- The literal dimension-scaled source potential after reweighting. -/
def weightedPotential (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x u : Vector N) : ℝ :=
  β*H u-2*(N:ℝ)*h (overlap x u)

lemma weightedPotential_continuous (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    {h : ℝ → ℝ} (hh : Continuous h) (x : Vector N) : Continuous (weightedPotential β H h x) := by
  have hR : Continuous (fun u : Vector N => overlap x u) := by unfold overlap; fun_prop
  exact (continuous_const.mul hH).sub (continuous_const.mul (hh.comp hR))

lemma weightedPotential_exp (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x u : Vector N) :
    Real.exp (weightedPotential β H h x u)=Real.exp (β*H u)*(psi h x u)^2 := by
  rw [weightedPotential,psi_sq,← Real.exp_add]
  congr 1
  ring

/-- Actual overlap denominator equals the ratio of two true spherical
partitions. No normalization is assumed for the weighted Gibbs law. -/
theorem denominator_eq_partition_ratio (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (h : ℝ → ℝ) (x : Vector N) :
    denominator β H h x=partition N 1 (weightedPotential β H h x)/partition N β H := by
  rw [denominator,integral_gibbsLaw_eq_unnormalized hN β hH]
  congr 1
  unfold unnormalizedSphereIntegral partition
  apply integral_congr_ae
  exact .of_forall fun u => by
    change Real.exp (β*H u)*(psi h x u)^2=Real.exp (1*weightedPotential β H h x u)
    rw [one_mul,weightedPotential_exp]

/-- The actual overlap-weighted Gibbs law is exactly the actual Gibbs law
of the full weighted potential, on the same physical sphere. -/
theorem weightedLaw_eq_gibbsLaw (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    weightedLaw β H h x=gibbsLaw N 1 (weightedPotential β H h x) := by
  have hρ : Measurable (fun u => ENNReal.ofReal (gibbsDensity N β H u)) :=
    (gibbsDensity_continuous β hH).measurable.ennreal_ofReal
  have hw : Measurable (fun u => ENNReal.ofReal (weightedDensity β H h x u)) :=
    (weightedDensity_continuous β H hh x).measurable.ennreal_ofReal
  rw [weightedLaw,gibbsLaw,← withDensity_mul _ hρ hw]
  congr 1
  funext u
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (gibbsDensity_pos hN β hH u).le]
  congr 1
  rw [gibbsDensity,weightedDensity,denominator_eq_partition_ratio hN β hH h x]
  change Real.exp (β*H u)/partition N β H*((psi h x u)^2/
    (partition N 1 (weightedPotential β H h x)/partition N β H))=
    Real.exp (1*weightedPotential β H h x u)/partition N 1 (weightedPotential β H h x)
  rw [one_mul,weightedPotential_exp]
  field_simp [(partition_pos hN β hH).ne']

end
end SlowEquilibration.SphericalBarycenter
