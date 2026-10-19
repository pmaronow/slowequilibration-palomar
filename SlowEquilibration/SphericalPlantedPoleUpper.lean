-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedUniformUpper

@[expose] public section

/-!
# Actual planted latitude bounds near the poles

The existing measurable tensor-regularity event has exponentially small
failure probability. On that actual event the planted latitude pressure is
bounded uniformly, while its exact spherical entropy tends to minus infinity
at the poles. No limiting pressure formula is used.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem covariancePolynomial_le_at_one {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {q : ℝ} (hq : |q| ≤ 1) :
    covariancePolynomial c q ≤ covariancePolynomial c 1 := by
  unfold covariancePolynomial
  apply Finset.sum_le_sum
  intro p _
  rw [one_pow,mul_one]
  apply mul_le_of_le_one_right (hc p)
  apply (le_abs_self _).trans
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) hq

theorem latitudeLogPartition_le_of_regularDisorder {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) {β : ℝ} (hβ : 0 ≤ β) (J : Disorder (n+1) P)
    (hJ : J ∈ regularDisorder) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    latitudeLogPartition c β u e q J ≤ β*derivativeConstant c*((n+1 : ℕ) : ℝ) := by
  have hs := (latitudeLaw_support hn u hu e he hq).mono fun _ hv => hv.1
  have hi := partitionAgainst_integrable (latitudeLaw u e q) hs β (field_contDiff c J).continuous
  have hp := partitionAgainst_pos (latitudeLaw u e q) hs β (field_contDiff c J).continuous
  have hb : partitionAgainst (latitudeLaw u e q) β (field c J) ≤
      Real.exp (β*derivativeConstant c*((n+1 : ℕ) : ℝ)) := by
    calc
      _ ≤ ∫ _x : Vector (n+1), Real.exp (β*derivativeConstant c*((n+1 : ℕ) : ℝ))
          ∂latitudeLaw u e q := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [hs] with x hx
        have hnorm : ‖x‖ ≤ Real.sqrt ((n+1 : ℕ) : ℝ) := by rw [← hx,Real.sqrt_sq (norm_nonneg _)]
        have hf := (field_regularDisorder_ball_bounds (by omega) c J hJ x hnorm).1
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hf) hβ
        nlinarith
      _ = _ := by simp
  have hl := Real.log_le_log hp hb
  rwa [Real.log_exp] at hl

/-- The exact planted profile is bounded on the true regularity event by
a dimension-free pressure constant plus the literal entropy coefficient. -/
theorem plantedLatitudeProfile_le_of_regularDisorder {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) (J : Disorder (n+1) μ.maxDegree)
    (hJ : J ∈ regularDisorder) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    plantedLatitudeProfile n μ β u e q J ≤
      β*derivativeConstant (mixtureCoefficients μ)+β^2*μ.xi 1+
        ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ))*Real.log (1-q^2) := by
  have hl := latitudeLogPartition_le_of_regularDisorder hn (mixtureCoefficients μ) hβ J hJ u hu e he hq
  have hc := covariancePolynomial_le_at_one (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hq
  simp only [covariancePolynomial_mixture] at hc
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  unfold plantedLatitudeProfile
  rw [latitude_logPartition_plantedShift hn _ (mixtureCoefficients_nonnegative μ) β u hu e he hq,
    covariancePolynomial_mixture]
  have hm := (div_le_iff₀ hN).mpr hl
  change Real.log (partitionAgainst (latitudeLaw u e q) β (field (mixtureCoefficients μ) J))/
    ((n+1 : ℕ) : ℝ) ≤ β*derivativeConstant (mixtureCoefficients μ) at hm
  have heq : (β^2*((n+1 : ℕ) : ℝ)*μ.xi q+
      Real.log (partitionAgainst (latitudeLaw u e q) β (field (mixtureCoefficients μ) J)))/
        ((n+1 : ℕ) : ℝ) = β^2*μ.xi q+
      Real.log (partitionAgainst (latitudeLaw u e q) β (field (mixtureCoefficients μ) J))/
        ((n+1 : ℕ) : ℝ) := by field_simp
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg β)
  linarith

/-- A deterministic latitude cutoff can force the entropy-plus-pressure
upper below any prescribed level, uniformly in dimension at least six. -/
theorem exists_planted_pole_cutoff (B A ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ ρ ∈ Ioo ρ₀ 1, B+Real.log (1-ρ^2)/4 ≤ A := by
  let v : ℝ := min ((1-ρ₀^2)/2) (Real.exp (4*(A-B)))
  have harg : 0 < 1-ρ₀^2 := by nlinarith [hρ₀.1,hρ₀.2]
  have hv : 0 < v := lt_min (by positivity) (Real.exp_pos _)
  have hvl : v < 1-ρ₀^2 := (min_le_left _ _).trans_lt (by linarith)
  have hv1 : v < 1 := by nlinarith [sq_nonneg ρ₀]
  let ρ := Real.sqrt (1-v)
  have hr : ρ^2=1-v := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hrlo : ρ₀ < ρ := by nlinarith [hρ₀.1]
  have hrhi : ρ < 1 := by nlinarith
  refine ⟨ρ,⟨hrlo,hrhi⟩,?_⟩
  have he : 1-ρ^2=v := by linarith
  rw [he]
  have hh := Real.log_le_log hv (min_le_right ((1-ρ₀^2)/2) (Real.exp (4*(A-B))))
  rw [Real.log_exp] at hh
  linarith

theorem plantedLatitudeProfile_pole_upper {n : ℕ} (hn : 5 ≤ n)
    (μ : FiniteMixture) {β ρ A : ℝ} (hβ : 0 ≤ β) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hcut : β*derivativeConstant (mixtureCoefficients μ)+β^2*μ.xi 1+
      Real.log (1-ρ^2)/4 ≤ A)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J ∈ regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : q ∈ Ico ρ 1) :
    plantedLatitudeProfile n μ β u e q J ≤ A := by
  have hq0 : 0 < q := hρ.1.trans_le hq.1
  have harg : 0 < 1-q^2 := by nlinarith [hq.2]
  have hl0 : Real.log (1-q^2) ≤ 0 := Real.log_nonpos harg.le (by nlinarith [sq_nonneg q])
  have hlog : Real.log (1-q^2) ≤ Real.log (1-ρ^2) :=
    Real.log_le_log harg (by nlinarith [hρ.1,hq.1])
  have hc : (1/4 : ℝ) ≤ ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*((n+1 : ℕ) : ℝ))).mpr
    rw [Nat.cast_sub (show 2 ≤ n by omega)]
    push_cast
    have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hm := mul_le_mul_of_nonpos_right hc hl0
  have hb := plantedLatitudeProfile_le_of_regularDisorder (by omega) μ hβ J hJ u hu e he
    (abs_le.mpr ⟨by linarith,hq.2.le⟩)
  linarith

/-- The literal pole profiles can be forced below any fixed level on the
existing actual measurable event, whose failure is at most exp(-N). -/
theorem plantedLatitudeProfile_pole_event (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β)
    (A ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ ρ ∈ Ioo ρ₀ 1, ∀ n : ℕ, 5 ≤ n →
      (disorderLaw (n+1) μ.maxDegree).real (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ≤
        Real.exp (-((n+1 : ℕ) : ℝ)) ∧
      ∀ J ∈ regularDisorder (N := n+1) (P := μ.maxDegree),
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      ∀ q ∈ Ico ρ 1, plantedLatitudeProfile n μ β u e q J ≤ A := by
  obtain ⟨ρ,hρ,hcut⟩ := exists_planted_pole_cutoff
    (β*derivativeConstant (mixtureCoefficients μ)+β^2*μ.xi 1) A ρ₀ hρ₀
  refine ⟨ρ,hρ,?_⟩
  intro n hn
  refine ⟨regularDisorder_failure_probability (by omega),?_⟩
  intro J hJ u hu e he q hq
  exact plantedLatitudeProfile_pole_upper hn μ hβ ⟨hρ₀.1.trans hρ.1,hρ.2⟩ hcut J hJ u hu e he hq

end SlowEquilibration.SphericalModel
