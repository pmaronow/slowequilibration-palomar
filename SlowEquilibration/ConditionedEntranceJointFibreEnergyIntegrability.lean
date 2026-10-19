-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceBoundedCrossEnergy
public import SlowEquilibration.SphericalWeightedCrossAbsorption

/-! Literal finite-dimensional energy densities of completed spherical
Sobolev graphs are Bochner integrable. These are the fibre inputs needed
for the source Gibbs kernel and global tilted-law disintegration. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem spherical_weighted_gradient_density_integrable
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H)
    (u F : sphericalSobolevGraph hN β H hH)
    (CF : ℝ≥0)
    (hF : ∀ᵐ x ∂gibbsLaw N β H, ‖F.val.fst x‖ ≤ CF) :
    Integrable (fun x => F.val.fst x *
      (∑ ij : Fin N × Fin N, (u.val.snd ij x)^2))
      (gibbsLaw N β H) := by
  have hi (ij : Fin N × Fin N) :
      Integrable (fun x => F.val.fst x * (u.val.snd ij x)^2)
        (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (u.val.snd ij)
      (multiplication (gibbsLaw N β H) F.val.fst
        (Lp.aestronglyMeasurable F.val.fst) CF hF (u.val.snd ij))).congr
    filter_upwards [multiplication_ae (gibbsLaw N β H) F.val.fst
      (Lp.aestronglyMeasurable F.val.fst) CF hF (u.val.snd ij)] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring
  have hs : Integrable (fun x =>
      ∑ ij : Fin N × Fin N, F.val.fst x * (u.val.snd ij x)^2)
      (gibbsLaw N β H) :=
    integrable_finsetSum Finset.univ (fun ij _ => hi ij)
  convert hs using 1
  ext x
  rw [Finset.mul_sum]

theorem spherical_fisher_density_integrable
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H)
    (F : sphericalSobolevGraph hN β H hH)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β H, 1 ≤ F.val.fst x) :
    Integrable (fun x =>
      ∑ ij : Fin N × Fin N, (F.val.snd ij x)^2 / F.val.fst x)
      (gibbsLaw N β H) := by
  apply integrable_finsetSum Finset.univ
  intro ij _
  convert sphericalFisher_coordinate_integrable hN β H hH F hFlo ij using 1
  ext x
  rw [div_eq_mul_inv]

theorem weighted_gradient_density_integrable_of_graph_representatives
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H)
    (u F₁ : sphericalSobolevGraph hN β H hH)
    (CF : ℝ≥0)
    (hFbound : ∀ᵐ x ∂gibbsLaw N β H, ‖F₁.val.fst x‖ ≤ CF)
    (F : Vector N → ℝ) (G : (Fin N × Fin N) → Vector N → ℝ)
    (hF : F =ᵐ[gibbsLaw N β H] F₁.val.fst)
    (hG : ∀ ij, G ij =ᵐ[gibbsLaw N β H] u.val.snd ij) :
    Integrable (fun x => F x *
      (∑ ij : Fin N × Fin N, (G ij x)^2)) (gibbsLaw N β H) := by
  apply (spherical_weighted_gradient_density_integrable hN β H hH u F₁ CF hFbound).congr
  filter_upwards [hF, ae_all_iff.mpr hG] with x hx hg
  rw [hx]
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  rw [hg ij]

theorem fisher_density_integrable_of_graph_representatives
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H)
    (F₁ : sphericalSobolevGraph hN β H hH)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β H, 1 ≤ F₁.val.fst x)
    (F : Vector N → ℝ) (GF : (Fin N × Fin N) → Vector N → ℝ)
    (hF : F =ᵐ[gibbsLaw N β H] F₁.val.fst)
    (hGF : ∀ ij, GF ij =ᵐ[gibbsLaw N β H] F₁.val.snd ij) :
    Integrable (fun x =>
      ∑ ij : Fin N × Fin N, (GF ij x)^2 / F x)
      (gibbsLaw N β H) := by
  apply (spherical_fisher_density_integrable hN β H hH F₁ hFlo).congr
  filter_upwards [hF, ae_all_iff.mpr hGF] with x hx hg
  apply Finset.sum_congr rfl
  intro ij _
  rw [hx,hg ij]

end SlowEquilibration.SphericalForm
