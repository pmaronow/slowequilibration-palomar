-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexLatitudeMean
public import SlowEquilibration.SphericalLatitudeMeanSymmetry
public import SlowEquilibration.SphericalPlantedPoleUpper

@[expose] public section

/-! # Genuine signed latitude estimates for convex covariances

Negative latitudes are controlled by the actual quenched mean reflection
and actual continuum concentration. The tensor sample need not be even.
-/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem convex_plantedLatitudeProfile_eventually_uniform_upper
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {β ρ ε : ℝ} (hβ : 0 < β) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) μ.maxDegree {J | ∃ q ∈ Icc (-ρ) ρ,
          plantedProfileTrial μ β |q|+ε ≤ plantedLatitudeProfile n μ β u e q J} ≤
          ENNReal.ofReal (Real.exp (-γ*((n+1 : ℕ) : ℝ))) := by
  obtain ⟨γ,hγ,hconc⟩ := latitude_uniform_concentration_eventually
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)
    (by rw [covariancePolynomial_mixture]; exact μ.xi_pos (by norm_num)) hβ (half_pos hε)
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hconc,convex_plantedLatitudeMeanProfile_eventually_uniform_upper μ hconv
    hβ hρ (half_pos hε), eventually_ge_atTop 1] with n hconc hmean hn
  intro u hu e he
  apply (measure_mono ?_).trans (hconc (-ρ) ρ (by linarith [hρ.2]) hρ.2.le
    (by linarith [hρ.1]) u hu e he)
  rintro J ⟨q,hq,hJ⟩
  refine ⟨q,hq,?_⟩
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1,hρ.2],hq.2.trans hρ.2.le⟩
  have hqabs : |q| ∈ Icc (0 : ℝ) ρ := ⟨abs_nonneg q,abs_le.mpr hq⟩
  rw [plantedLatitudeProfile_centered hn μ hβ u hu e he hqa] at hJ
  have hm := (plantedLatitudeMeanProfile_le_abs hn μ hβ u hu e he hqa).trans
    (hmean |q| hqabs u hu e he)
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hf : ε/2 ≤ latitudeCenteredLogPartition (mixtureCoefficients μ) β u e q J/
      ((n+1 : ℕ) : ℝ) := by linarith
  exact ((le_div_iff₀ hN).mp hf).trans (le_abs_self _)

theorem plantedLatitudeProfile_signed_pole_upper {n : ℕ} (hn : 5 ≤ n)
    (μ : FiniteMixture) {β ρ A : ℝ} (hβ : 0 ≤ β) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hcut : β*derivativeConstant (mixtureCoefficients μ)+β^2*μ.xi 1+
      Real.log (1-ρ^2)/4 ≤ A)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J ∈ regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ∈ Ico ρ 1) :
    plantedLatitudeProfile n μ β u e q J ≤ A := by
  have harg : 0 < 1-q^2 := by nlinarith [sq_abs q,abs_nonneg q,hq.2]
  have hl0 : Real.log (1-q^2) ≤ 0 :=
    Real.log_nonpos harg.le (by nlinarith [sq_nonneg q])
  have hlog : Real.log (1-q^2) ≤ Real.log (1-ρ^2) :=
    Real.log_le_log harg (by nlinarith [hρ.1,hq.1,sq_abs q])
  have hc : (1/4 : ℝ) ≤ ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*((n+1 : ℕ) : ℝ))).mpr
    rw [Nat.cast_sub (show 2 ≤ n by omega)]
    push_cast
    have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hm := mul_le_mul_of_nonpos_right hc hl0
  have hb := plantedLatitudeProfile_le_of_regularDisorder (by omega) μ hβ J hJ u hu e he hq.2.le
  linarith

theorem plantedLatitudeProfile_signed_pole_event (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β)
    (A ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ ρ ∈ Ioo ρ₀ 1, ∀ n : ℕ, 5 ≤ n →
      (disorderLaw (n+1) μ.maxDegree).real (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ≤
        Real.exp (-((n+1 : ℕ) : ℝ)) ∧
      ∀ J ∈ regularDisorder (N := n+1) (P := μ.maxDegree),
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      ∀ q, |q| ∈ Ico ρ 1 → plantedLatitudeProfile n μ β u e q J ≤ A := by
  obtain ⟨ρ,hρ,hcut⟩ := exists_planted_pole_cutoff
    (β*derivativeConstant (mixtureCoefficients μ)+β^2*μ.xi 1) A ρ₀ hρ₀
  refine ⟨ρ,hρ,?_⟩
  intro n hn
  refine ⟨regularDisorder_failure_probability (by omega),?_⟩
  intro J hJ u hu e he q hq
  exact plantedLatitudeProfile_signed_pole_upper hn μ hβ ⟨hρ₀.1.trans hρ.1,hρ.2⟩
    hcut J hJ u hu e he hq

end
end SlowEquilibration.SphericalModel
