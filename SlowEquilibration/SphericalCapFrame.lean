-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCapCutoff
public import SlowEquilibration.SphericalFrameCount

/-! The literal continuum cap frame on the actual spherical Gibbs space.
Its measurable mass and energy are ordinary integrals of the constructed
smooth cutoff. No spectral frame or overlap identities are assumed. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalCapFrame

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalPhysicalSpectral SphericalDynamics SphericalReversibility
open SphericalLaplaceIdentification SphericalCapCutoff
open SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal ENNReal

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

def familyGraph (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β q₁ q₂ : ℝ) (u : Vector N) :
    sphericalSobolevGraph hN β (potential μ J) (potential_continuous μ J) :=
  C1ToGraph hN β (potential μ J) (potential_continuous μ J)
    (capTrial q₁ q₂ u) ((capTrial_contDiff q₁ q₂ u).of_le (by simp))

def squareMass (β : ℝ) (H : Vector N → ℝ) (q₁ q₂ : ℝ) (u : Vector N) : ℝ :=
  ∫ x, (capTrial q₁ q₂ u x)^2 ∂gibbsLaw N β H

lemma familyGraph_mass (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β q₁ q₂ : ℝ) (u : Vector N) :
    ‖formValue hN μ J β (familyGraph hN μ J β q₁ q₂ u)‖^2 =
      squareMass β (potential μ J) q₁ q₂ u := by
  change ‖gibbsToL2 hN β (potential μ J) (potential_continuous μ J)
    (capTrial q₁ q₂ u) (capTrial_contDiff q₁ q₂ u).continuous‖^2 = _
  rw [← real_inner_self_eq_norm_sq, gibbsToL2_inner]
  unfold squareMass
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp [squareMass]; ring)

lemma familyGraph_energy (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β q₁ q₂ : ℝ) (u : Vector N) :
    sphericalCompletedDirichlet hN β (potential μ J) (potential_continuous μ J)
      (familyGraph hN μ J β q₁ q₂ u) (familyGraph hN μ J β q₁ q₂ u) =
      dirichletEnergy N β (potential μ J) (capTrial q₁ q₂ u) :=
  sphericalCompletedDirichlet_C1_energy hN β _ _ _ _

lemma squareMass_measurable (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (q₁ q₂ : ℝ) :
    Measurable (squareMass β H q₁ q₂) := by
  let _ := gibbsLaw_probability hN β hH
  have hc : Continuous (fun z : Vector N × Vector N => (capTrial q₁ q₂ z.1 z.2)^2) := by
    have h := (capTrial_joint_contDiff (N := N) q₁ q₂).continuous
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right' (ν := gibbsLaw N β H) |>.measurable

lemma squareMass_nonneg (β : ℝ) (H : Vector N → ℝ) (q₁ q₂ : ℝ) (u : Vector N) :
    0 ≤ squareMass β H q₁ q₂ u := integral_nonneg (fun x => sq_nonneg _)

lemma squareMass_le_one (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    (q₁ q₂ : ℝ) (u : Vector N) : squareMass β H q₁ q₂ u ≤ 1 := by
  let _ := gibbsLaw_probability hN β hH
  have hc : Continuous (fun x => (capTrial q₁ q₂ u x)^2) := by
    have h := (capTrial_contDiff q₁ q₂ u).continuous
    fun_prop
  have hi := integrable_gibbs_of_continuous hN β hH hc
  have hm := integral_mono_ae hi (integrable_const (1 : ℝ)) (ae_of_all _ (fun x => by
    have h0 := cutoff_nonneg q₁ q₂ (overlap x u)
    have h1 := cutoff_le_one q₁ q₂ (overlap x u)
    change (cutoff q₁ q₂ (overlap x u))^2 ≤ 1
    nlinarith))
  change (∫ x, (capTrial q₁ q₂ u x)^2 ∂gibbsLaw N β H) ≤ 1
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hm

lemma squareMass_integrable (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    (q₁ q₂ : ℝ) (ν : Measure (Vector N)) [IsFiniteMeasure ν] :
    Integrable (squareMass β H q₁ q₂) ν := by
  apply Integrable.of_bound (squareMass_measurable hN β hH q₁ q₂).aestronglyMeasurable 1
  exact ae_of_all _ (fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (squareMass_nonneg β H q₁ q₂ u)]
    exact squareMass_le_one hN β hH q₁ q₂ u)

lemma capTrial_energy_measurable (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (q₁ q₂ : ℝ) :
    Measurable (fun u => dirichletEnergy N β H (capTrial q₁ q₂ u)) := by
  let _ := gibbsLaw_probability hN β hH
  have hd : Continuous (deriv (cutoff q₁ q₂)) :=
    (cutoff_contDiff q₁ q₂).continuous_deriv (by simp)
  have hc : Continuous (fun z : Vector N × Vector N =>
      ‖(deriv (cutoff q₁ q₂) (overlap z.2 z.1) / (N : ℝ)) • tangentProjection z.2 z.1‖^2) := by
    simp only [tangentProjection_apply, projection]
    unfold overlap
    fun_prop
  have heq : (fun u => dirichletEnergy N β H (capTrial q₁ q₂ u)) =
      (fun u => ∫ x,
        ‖(deriv (cutoff q₁ q₂) (overlap x u) / (N : ℝ)) • tangentProjection x u‖^2 ∂gibbsLaw N β H) := by
    funext u
    rw [dirichletEnergy_eq_integral_norm_sq]
    congr 1
    funext x
    rw [capTrial_surfaceGradient hN]
  rw [heq]
  exact hc.stronglyMeasurable.integral_prod_right' (ν := gibbsLaw N β H) |>.measurable

lemma capTrial_energy_integrable (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {q₁ q₂ : ℝ} (hq : q₁ < q₂)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν] (hν : ∀ᵐ u ∂ν, OnSphere u) :
    Integrable (fun u => dirichletEnergy N β H (capTrial q₁ q₂ u)) ν := by
  let _ := gibbsLaw_probability hN β hH
  apply Integrable.of_bound (capTrial_energy_measurable hN β hH q₁ q₂).aestronglyMeasurable
    (collarCoefficient N q₁ q₂)
  filter_upwards [hν] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (dirichletEnergy_nonneg N β H _)]
  exact (capTrial_energy_le_collar hN β hH hq u hu).trans (by
    have hm := measureReal_le_one (μ := gibbsLaw N β H) (s := collar u q₁ q₂)
    have hK : 0 ≤ collarCoefficient N q₁ q₂ := by dsimp [collarCoefficient]; positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hK)

end SlowEquilibration.SphericalCapFrame
