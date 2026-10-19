-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! A reusable positive angular Fubini lemma. Pointwise expectation
factorization is sufficient to establish integrability of the full angular
partition once the comparison angular partition has finite weighted mean. -/

namespace SlowEquilibration.PositiveAngularFactorization
noncomputable section
open MeasureTheory
set_option autoImplicit false

theorem weighted_integral_factorization
    {α θ : Type*} [MeasurableSpace α] [MeasurableSpace θ]
    (ν : Measure α) (ρ : Measure θ) [SFinite ν] [SFinite ρ]
    (D : α → ℝ) (F G : α → θ → ℝ) (c : ℝ)
    (hD₀ : ∀ x, 0 ≤ D x)
    (hF₀ : ∀ x y, 0 ≤ F x y)
    (hG₀ : ∀ x y, 0 ≤ G x y)
    (hGmeas : Measurable (fun z : α × θ => D z.1 * G z.1 z.2))
    (hFmeas : Measurable (fun z : θ × α => D z.2 * F z.2 z.1))
    (hGangular : ∀ x, Integrable (G x) ρ)
    (hFpoint : ∀ y, Integrable (fun x => D x * F x y) ν)
    (hpoint : ∀ᵐ y ∂ρ, (∫ x, D x * F x y ∂ν) =
      c * (∫ x, D x * G x y ∂ν))
    (hGpart : Integrable (fun x => D x * (∫ y, G x y ∂ρ)) ν) :
    Integrable (fun x => D x * (∫ y, F x y ∂ρ)) ν ∧
    (∫ x, D x * (∫ y, F x y ∂ρ) ∂ν) =
      c * (∫ x, D x * (∫ y, G x y ∂ρ) ∂ν) := by
  have hGprod : Integrable (fun z : α × θ => D z.1 * G z.1 z.2) (ν.prod ρ) := by
    apply (integrable_prod_iff hGmeas.aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun x => (hGangular x).const_mul (D x)),?_⟩
    apply hGpart.congr
    filter_upwards [] with x
    have hn : (fun y : θ => ‖D x * G x y‖) =
        (fun y => D x * G x y) := by
      funext y
      exact Real.norm_eq_abs _ |>.trans
        (abs_of_nonneg (mul_nonneg (hD₀ x) (hG₀ x y)))
    rw [hn,integral_const_mul]
  have hGright : Integrable (fun y : θ => ∫ x, D x * G x y ∂ν) ρ :=
    hGprod.integral_prod_right
  have hFprod : Integrable (fun z : θ × α => D z.2 * F z.2 z.1) (ρ.prod ν) := by
    apply (integrable_prod_iff hFmeas.aestronglyMeasurable).mpr
    refine ⟨.of_forall hFpoint,?_⟩
    apply (hGright.const_mul c).congr
    filter_upwards [hpoint] with y hy
    have hn : (fun x : α => ‖D x * F x y‖) =
        (fun x => D x * F x y) := by
      funext x
      exact Real.norm_eq_abs _ |>.trans
        (abs_of_nonneg (mul_nonneg (hD₀ x) (hF₀ x y)))
    rw [hn]
    exact hy.symm
  have hFpart : Integrable (fun x => D x * (∫ y, F x y ∂ρ)) ν := by
    convert hFprod.integral_prod_right using 1
    funext x
    rw [← integral_const_mul]
  refine ⟨hFpart,?_⟩
  calc
    (∫ x, D x * (∫ y, F x y ∂ρ) ∂ν) =
        ∫ x, (∫ y, D x * F x y ∂ρ) ∂ν := by
          congr 1
          funext x
          rw [integral_const_mul]
    _ = ∫ y, (∫ x, D x * F x y ∂ν) ∂ρ :=
      (integral_integral_swap hFprod).symm
    _ = ∫ y, c * (∫ x, D x * G x y ∂ν) ∂ρ := integral_congr_ae hpoint
    _ = c * ∫ y, (∫ x, D x * G x y ∂ν) ∂ρ := integral_const_mul ..
    _ = c * ∫ x, D x * (∫ y, G x y ∂ρ) ∂ν := by
      congr 1
      rw [(integral_integral_swap hGprod).symm]
      congr 1
      funext x
      rw [integral_const_mul]

end
end SlowEquilibration.PositiveAngularFactorization
