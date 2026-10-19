-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGeneratorDomainForm
public import SlowEquilibration.ConditionedEntranceKilledPerturbation

/-! The full spherical form equation for literal bounded perturbations.
This bridge uses the proved spherical generator-domain identity. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem boundedPerturbation_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E)
    (h : A.domain) (θ : ℝ) (f w : E)
    (hr : θ • (h : E)+boundedPerturbation A V h=f) :
    inner ℝ (A h) w+inner ℝ (V h) w+θ*inner ℝ (h : E) w=inner ℝ f w := by
  have hp := congrArg (fun z : E => inner ℝ z w) hr
  rw [boundedPerturbation_apply,inner_add_left,inner_add_left,real_inner_smul_left] at hp
  linarith

/-- Every solution of the literal perturbed operator equation has the
actual completed spherical form identity against every Sobolev test. -/
theorem sphericalGenerator_boundedPerturbation_form {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (V : Lp ℝ 2 (gibbsLaw N β H) →L[ℝ] Lp ℝ 2 (gibbsLaw N β H))
    (h : (sphericalGenerator hN β H hH).domain) (θ : ℝ)
    (f : Lp ℝ 2 (gibbsLaw N β H))
    (hr : θ • (h : Lp ℝ 2 (gibbsLaw N β H))+
      boundedPerturbation (sphericalGenerator hN β H hH) V h=f) :
    ∃ u : sphericalSobolevGraph hN β H hH,
      sphericalEnergyL2Map hN β H hH u=h.val ∧
      ∀ v : sphericalSobolevGraph hN β H hH,
        sphericalCompletedDirichlet hN β H hH u v+
          inner ℝ (V h) (sphericalEnergyL2Map hN β H hH v)+
          θ*inner ℝ h.val (sphericalEnergyL2Map hN β H hH v)=
          inner ℝ f (sphericalEnergyL2Map hN β H hH v) := by
  obtain ⟨u,hu,hform⟩ := sphericalGenerator_domain_form hN β H hH h
  refine ⟨u,hu,?_⟩
  intro v
  rw [hform v]
  exact boundedPerturbation_pairing _ V h θ f _ hr

end SlowEquilibration.SphericalForm
