-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeightedCrossAbsorption
public import SlowEquilibration.SphericalGibbsEquivalentMeasures

/-! A finite Gibbs oscillation controls the actual transported Fisher
integral. This estimate is for integration existence; the small source
commutator constants come from axis moments separately. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem sphericalFisher_changeGibbs_le (hN : 1≤N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N→ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (F₀ : sphericalSobolevGraph hN β₀ H₀ hH₀)
    (hF₀ : ∀ᵐ x ∂gibbsLaw N β₀ H₀,1≤F₀.val.fst x) (B : ℝ)
    (hB : ∀ x,OnSphere x → |β₁*H₁ x-β₀*H₀ x|≤B) :
    ∃ F₁ : sphericalSobolevGraph hN β₁ H₁ hH₁,
      (F₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] F₀.val.fst) ∧
      (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β₁ H₁] F₀.val.snd ij) ∧
      sphericalFisher hN β₁ H₁ hH₁ F₁≤Real.exp (2*B)*sphericalFisher hN β₀ H₀ hH₀ F₀ := by
  obtain ⟨F₁,hv,hg⟩ := sphericalSobolevGraph_changeGibbs hN β₀ β₁ H₀ H₁ hH₀ hH₁ F₀
  have hcmp := gibbsLaw_le_of_sphere_energy_bounds hN β₀ β₁ hH₀ hH₁
    (fun x hx => (abs_le.mp (hB x hx)).1) (fun x hx => (abs_le.mp (hB x hx)).2)
  refine ⟨F₁,hv,hg,?_⟩
  unfold sphericalFisher
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ij _
  have hi := sphericalFisher_coordinate_integrable hN β₀ H₀ hH₀ F₀ hF₀ ij
  calc
    _ = ∫ x,(F₀.val.snd ij x)^2*(F₀.val.fst x)⁻¹ ∂gibbsLaw N β₁ H₁ := by
      apply integral_congr_ae
      filter_upwards [hv,hg ij] with x hx hy
      rw [hx,hy]
    _ ≤ ∫ x,(F₀.val.snd ij x)^2*(F₀.val.fst x)⁻¹
        ∂(ENNReal.ofReal (Real.exp (B-(-B))) • gibbsLaw N β₀ H₀) := by
      apply integral_mono_measure hcmp
      · exact Measure.ae_smul_measure (hF₀.mono (fun x hx =>
          mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (by linarith)))) _
      · exact hi.smul_measure ENNReal.ofReal_ne_top
    _ = Real.exp (2*B)*(∫ x,(F₀.val.snd ij x)^2*(F₀.val.fst x)⁻¹ ∂gibbsLaw N β₀ H₀) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal (Real.exp_pos _).le]
      simp only [smul_eq_mul]
      congr 2
      ring

end SlowEquilibration.SphericalForm
