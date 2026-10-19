-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOperator

/-! Actual generator-domain elements belong to the completed spherical
Gibbs gradient graph and satisfy its full-domain weak form identity. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

theorem sphericalGenerator_domain_form {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (U : (sphericalGenerator hN β H hH).domain) :
    ∃ u : sphericalSobolevGraph hN β H hH,
      sphericalEnergyL2Map hN β H hH u=U.val ∧
      ∀ v : sphericalSobolevGraph hN β H hH,
        sphericalCompletedDirichlet hN β H hH u v=
          inner ℝ (sphericalGenerator hN β H hH U) (sphericalEnergyL2Map hN β H hH v) := by
  obtain ⟨f,hf⟩ := U.property
  have hU : U=(⟨sphericalL2Resolvent hN β H hH f,⟨f,rfl⟩⟩ :
      (sphericalGenerator hN β H hH).domain) := Subtype.ext hf.symm
  refine ⟨sphericalWeakSolution hN β H hH f,hf,?_⟩
  intro v
  rw [hU]
  exact sphericalGenerator_resolvent_form hN β H hH f v

end SlowEquilibration.SphericalForm
