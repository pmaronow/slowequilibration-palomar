-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeakResolvent

/-! Literal integrals of the actual completed normalized rotation gradients. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def completedGradientPairing (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (u v : sphericalSobolevGraph hN β H hH) (x : Vector N) : ℝ :=
  ∑ ij : Fin N × Fin N,u.val.snd ij x*v.val.snd ij x

theorem completedGradientPairing_integrable (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (u v : sphericalSobolevGraph hN β H hH) :
    Integrable (completedGradientPairing hN β H hH u v) (gibbsLaw N β H) := by
  apply integrable_finsetSum
  intro ij _
  have hi := L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij) (v.val.snd ij)
  simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using hi

theorem sphericalCompletedDirichlet_integral (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (u v : sphericalSobolevGraph hN β H hH) :
    sphericalCompletedDirichlet hN β H hH u v=
      ∫ x,completedGradientPairing hN β H hH u v x ∂gibbsLaw N β H := by
  change inner ℝ u.val.snd v.val.snd=_
  rw [PiLp.inner_apply]
  simp only [completedGradientPairing]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ij _
    rw [L2.inner_def]
    apply integral_congr_ae
    exact .of_forall (fun _ => by simp only [RCLike.inner_apply,conj_trivial,mul_comm])
  · intro ij _
    have hi := L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij) (v.val.snd ij)
    simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using hi

end SlowEquilibration.SphericalForm
