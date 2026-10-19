-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevLogChain
public import SlowEquilibration.SphericalGeneratorDomainForm
public import SlowEquilibration.ConditionedEntranceFisher

/-! The actual completed spherical Fisher test is obtained from the literal
logarithm chain rule and the full generator-domain form identity. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Actual normalized rotation gradient square, divided by the function.
The normalization agrees with the proved spherical Dirichlet form. -/
def sphericalFisher {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u : sphericalSobolevGraph hN β H hH) : ℝ :=
  ∑ ij : Fin N × Fin N, ∫ x,(u.val.snd ij x)^2*(u.val.fst x)⁻¹ ∂gibbsLaw N β H

/-- The literal inverse-function gradient gives the Fisher pairing.
No Fisher/test identity is assumed. -/
theorem sphericalCompletedDirichlet_log_eq_fisher {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u v : sphericalSobolevGraph hN β H hH)
    (hu : ∀ᵐ x ∂gibbsLaw N β H,1 ≤ u.val.fst x)
    (hv : v.val.snd=logGradientMultiplier u.val.fst hu u.val.snd) :
    sphericalCompletedDirichlet hN β H hH u v=sphericalFisher hN β H hH u := by
  change inner ℝ u.val.snd v.val.snd=_
  rw [hv,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ij _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplication_ae (gibbsLaw N β H) (fun x => (u.val.fst x)⁻¹)
    ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable u.val.fst).aemeasurable).aestronglyMeasurable)
    1 (lp_inv_norm_le_one u.val.fst hu) (u.val.snd ij)] with x hx
  change inner ℝ (u.val.snd ij x)
    (multiplication (gibbsLaw N β H) (fun x => (u.val.fst x)⁻¹)
      ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable u.val.fst).aemeasurable).aestronglyMeasurable)
      1 (lp_inv_norm_le_one u.val.fst hu) (u.val.snd ij) x)=_
  simp only [hx,RCLike.inner_apply,conj_trivial]
  ring

theorem sphericalFisher_nonnegative {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u : sphericalSobolevGraph hN β H hH)
    (hu : ∀ᵐ x ∂gibbsLaw N β H,1 ≤ u.val.fst x) :
    0 ≤ sphericalFisher hN β H hH u := by
  apply Finset.sum_nonneg
  intro ij _
  apply integral_nonneg_of_ae
  exact hu.mono (fun x hx => mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (by linarith)))

/-- The exact tested operator equation gives the actual spherical Fisher
estimate. Boundedness is used only for the constructed logarithm test;
there is no assumed chain rule, test identity or Fisher conclusion. -/
theorem sphericalGenerator_fisher_bound {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (U : (sphericalGenerator hN β H hH).domain)
    (F₀ : Lp ℝ 2 (gibbsLaw N β H)) (θ C : ℝ) (hθ : 0 ≤ θ) (hC : 1 ≤ C)
    (h₀ : ∀ᵐ x ∂gibbsLaw N β H,0 < F₀ x)
    (hU : ∀ᵐ x ∂gibbsLaw N β H,1 ≤ U.val x ∧ U.val x ≤ C)
    (he₀ : Integrable (fun x => F₀ x*Real.log (F₀ x)) (gibbsLaw N β H))
    (hmass : (∫ x,F₀ x ∂gibbsLaw N β H)=∫ x,U.val x ∂gibbsLaw N β H)
    (hgen : sphericalGenerator hN β H hH U=θ • (F₀-U.val)) :
    ∃ u : sphericalSobolevGraph hN β H hH,
      sphericalEnergyL2Map hN β H hH u=U.val ∧
      sphericalFisher hN β H hH u ≤ θ*∫ x,F₀ x*Real.log (F₀ x) ∂gibbsLaw N β H := by
  let := gibbsLaw_probability hN β hH
  obtain ⟨u,hu,hform⟩ := sphericalGenerator_domain_form hN β H hH U
  have hu' : u.val.fst=U.val := hu
  have hub : ∀ᵐ x ∂gibbsLaw N β H,1 ≤ u.val.fst x ∧ u.val.fst x ≤ C := by
    rw [hu'];exact hU
  obtain ⟨v,hvlog,hvgrad⟩ := sphericalSobolevGraph_log_chain hN β H hH u C hC hub
  have hv : v.val.fst=ᵐ[gibbsLaw N β H] fun x => Real.log (U.val x) := by
    simpa only [hu'] using hvlog
  have hi₀ : Integrable F₀ (gibbsLaw N β H) := (Lp.memLp F₀).integrable (by norm_num)
  have hi : Integrable U.val (gibbsLaw N β H) := (Lp.memLp U.val).integrable (by norm_num)
  have he : Integrable (fun x => U.val x*Real.log (U.val x)) (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) U.val v.val.fst).congr
    filter_upwards [hv] with x hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring
  have ht : Integrable (fun x => (F₀ x-U.val x)*Real.log (U.val x)) (gibbsLaw N β H) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (F₀-U.val) v.val.fst).congr
    filter_upwards [hv,Lp.coeFn_sub F₀ U.val] with x hx hs
    simp only [RCLike.inner_apply,conj_trivial,hx,hs,Pi.sub_apply]
    ring
  have htest : sphericalFisher hN β H hH u=
      θ*∫ x,(F₀ x-U.val x)*Real.log (U.val x) ∂gibbsLaw N β H := by
    rw [← sphericalCompletedDirichlet_log_eq_fisher hN β H hH u v
      (hub.mono (fun _ hx => hx.1)) hvgrad,hform v,hgen,real_inner_smul_left,L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hv,Lp.coeFn_sub F₀ U.val] with x hx hs
    change inner ℝ ((F₀-U.val) x) (v.val.fst x)=_
    simp only [RCLike.inner_apply,conj_trivial,hx,hs,Pi.sub_apply]
    ring
  refine ⟨u,hu,?_⟩
  exact ConditionedEntrance.fisher_bound_of_resolvent_test (gibbsLaw N β H) F₀ U.val hθ h₀
    (hU.mono (fun _ hx => hx.1)) hi₀ hi he₀ he ht hmass htest

end SlowEquilibration.SphericalForm
