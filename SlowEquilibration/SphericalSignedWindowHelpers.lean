-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWindowIntensityMeasurable
public import SlowEquilibration.SignedPosteriorIntegration
public import SlowEquilibration.UnrestrictedConditionedDeterminants

/-! Integrable Jordan decompositions for the physical Kac--Rice intensities. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalIntrinsicKacRice WholeFieldRegression
open scoped ENNReal
noncomputable section

lemma sphereKRPrefactor_ne_zero (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    sphereKRPrefactor n μ Q ≠ 0 := by
  rw [sphereKRPrefactor_physical n μ hQ]
  apply mul_ne_zero (manuscriptRoundVolume_mass_ne_zero n)
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (mul_pos hQ (mixture_xi1_pos μ hQ))) _

lemma sphereKRPrefactor_ne_top (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    sphereKRPrefactor n μ Q ≠ ⊤ := by
  exact ENNReal.mul_ne_top (manuscriptRoundVolume_mass_ne_top n) ENNReal.ofReal_ne_top

lemma lintegral_lt_top_of_prefactor {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (F : Ω → ℝ≥0∞) {a r : ℝ≥0∞}
    (ha : a ≠ 0) (hr : r < ⊤) (he : r = a * ∫⁻ x, F x ∂ν) :
    (∫⁻ x, F x ∂ν) < ⊤ := by
  by_contra h
  have ht : (∫⁻ x, F x ∂ν) = ⊤ := eq_top_iff.mpr (le_of_not_gt h)
  exact hr.ne (he.trans (ENNReal.mul_eq_top.mpr (Or.inl ⟨ha, ht⟩)))

lemma weighted_integral_parts {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (q f g : Ω → ℝ≥0∞) (F : Ω → ℝ)
    (hf : AEMeasurable (fun x => q x * f x) ν)
    (hg : AEMeasurable (fun x => q x * g x) ν)
    (hfi : (∫⁻ x, q x * f x ∂ν) < ⊤) (hgi : (∫⁻ x, q x * g x ∂ν) < ⊤)
    (hF : ∀ x, F x = (f x).toReal - (g x).toReal) :
    Integrable (fun x => (q x).toReal * F x) ν ∧
    (∫ x, (q x).toReal * F x ∂ν) =
      (∫⁻ x, q x * f x ∂ν).toReal - (∫⁻ x, q x * g x ∂ν).toReal := by
  have he : (fun x => (q x).toReal * F x) =
      (fun x => (q x * f x).toReal - (q x * g x).toReal) := by
    funext x
    rw [hF x, mul_sub, ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [he]
  exact integrable_toReal_sub_integral ν _ _ hf hg hfi hgi

end
end SlowEquilibration.SphericalMarkedWindows
