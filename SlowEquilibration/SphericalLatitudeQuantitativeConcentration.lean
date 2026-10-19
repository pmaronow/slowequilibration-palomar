-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeUniformConcentration

/-! The explicit latitude concentration exponent is independent of tensor
degree. Only the dimension threshold depends on the finite cutoff. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_polynomial_tail_explicit (d : ℕ) {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(((n+1 : ℕ) : ℝ))/2)+
        2*((((n+1 : ℕ) : ℝ))^d+1)*Real.exp (-α*((n+1 : ℕ) : ℝ)) ≤
          Real.exp (-min (1/4) (α/2)*((n+1 : ℕ) : ℝ)) := by
  let γ : ℝ := min (1/4) (α/2)
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  have hδ : 0 < 1/2-γ := by have := min_le_left (1/4 : ℝ) (α/2); dsimp [γ]; linarith
  have hη : 0 < α-γ := by have := min_le_right (1/4 : ℝ) (α/2); dsimp [γ]; linarith
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexp {a : ℝ} (ha : 0 < a) :
      Tendsto (fun n : ℕ => Real.exp (-a*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop ha) using 1
    ext n
    simp only [Function.comp_apply,neg_mul]
  have hpoly : Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ))^d*
      Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) (α-γ) hη).comp hN using 1
    ext n
    simp only [Function.comp_apply,Real.rpow_natCast]
  have hr : Tendsto (fun n : ℕ => Real.exp (-(1/2-γ)*((n+1 : ℕ) : ℝ))+
      2*((((n+1 : ℕ) : ℝ))^d*Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ))+
        Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ)))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using (hexp hδ).add ((hpoly.add (hexp hη)).const_mul 2)
  filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ)<1 by norm_num))] with n hn
  have e₁ : Real.exp (-(((n+1 : ℕ) : ℝ))/2) =
      Real.exp (-(1/2-γ)*((n+1 : ℕ) : ℝ))*Real.exp (-γ*((n+1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e₂ : Real.exp (-α*((n+1 : ℕ) : ℝ)) =
      Real.exp (-(α-γ)*((n+1 : ℕ) : ℝ))*Real.exp (-γ*((n+1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hn.le (Real.exp_nonneg (-γ*((n+1 : ℕ) : ℝ)))
  rw [one_mul] at hm
  rw [e₁,e₂]
  nlinarith

theorem latitude_uniform_concentration_explicit {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a b : ℝ), -1 ≤ a → b ≤ 1 → a ≤ b →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) P {J | ∃ q ∈ Icc a b,
          ε*((n+1 : ℕ) : ℝ) ≤ |latitudeCenteredLogPartition c β u e q J|} ≤
          ENNReal.ofReal (Real.exp (-min (1/4) (((ε/2)^2/(2*β^2*covariancePolynomial c 1))/2)*((n+1 : ℕ) : ℝ))) := by
  let α : ℝ := (ε/2)^2/(2*β^2*covariancePolynomial c 1)
  have hα : 0 < α := by unfold α; positivity
  let γ : ℝ := min (1/4) (α/2)
  have hγtail := latitude_polynomial_tail_explicit (2*(P+2)) hα
  let K : ℝ := 4 * |β| * Real.sqrt (spatialVariance c)*(2*((P+1 : ℕ) : ℝ)+1)
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hK : ∀ᶠ n : ℕ in atTop, K ≤ (ε/2)*((n+1 : ℕ) : ℝ) :=
    (hN.const_mul_atTop (by positivity : 0 < ε/2)).eventually (eventually_ge_atTop K)
  filter_upwards [hγtail,hK,eventually_ge_atTop 1] with n htail hK hn
  intro a b ha hb hab u hu e he
  have hmesh := latitude_uniform_concentration_finite_mesh hn (latitudeMeshSize_pos n P)
    c hc hcov hβ (show 0 < ε/2 by positivity) (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))
    ha hb hab u hu e he
  have herr := latitude_polynomial_mesh_error_le n P c β ha hb hab
  have hsubset : {J : Disorder (n+1) P | ∃ q ∈ Icc a b,
      ε*((n+1 : ℕ) : ℝ) ≤ |latitudeCenteredLogPartition c β u e q J|} ⊆
      {J : Disorder (n+1) P | ∃ q ∈ Icc a b,
        (ε/2)*((n+1 : ℕ) : ℝ)+latitudeModulusScale n c β*
          (2*Real.sqrt (Fintype.card (Coordinate (n+1) P) : ℝ)+Real.sqrt ((n+1 : ℕ) : ℝ))*
            Real.sqrt ((b-a)/(latitudeMeshSize n P : ℝ)) ≤
              |latitudeCenteredLogPartition c β u e q J|} := by
    rintro J ⟨q,hq,hJ⟩
    refine ⟨q,hq,?_⟩
    change _ ≤ K at herr
    linarith
  have heα : -((ε/2)^2*((n+1 : ℕ) : ℝ))/(2*β^2*covariancePolynomial c 1) =
      -α*((n+1 : ℕ) : ℝ) := by unfold α; ring
  rw [Real.sq_sqrt (by positivity),heα] at hmesh
  apply ((measure_mono hsubset).trans hmesh).trans
  have hrhs : ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)/2))+
      ((latitudeMeshSize n P+1 : ℕ) : ℝ≥0∞)*ENNReal.ofReal (2*Real.exp (-α*((n+1 : ℕ) : ℝ))) =
      ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)/2)+
        2*((((n+1 : ℕ) : ℝ))^(2*(P+2))+1)*Real.exp (-α*((n+1 : ℕ) : ℝ))) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [latitudeMeshSize,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
    ring
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal htail

/-- A common variance bound gives a common exponent for all degrees. -/
theorem latitude_uniform_concentration_of_variance_bound {P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β ε B : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hB : 0 < B)
    (hvar : β^2*covariancePolynomial c 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a b : ℝ), -1 ≤ a → b ≤ 1 → a ≤ b →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
        disorderLaw (n+1) P {J | ∃ q ∈ Icc a b,
          ε*((n+1 : ℕ) : ℝ) ≤ |latitudeCenteredLogPartition c β u e q J|} ≤
          ENNReal.ofReal (Real.exp (-min (1/4) (((ε/2)^2/(2*B))/2)*((n+1 : ℕ) : ℝ))) := by
  filter_upwards [latitude_uniform_concentration_explicit c hc hcov hβ hε] with n hn
  intro a b ha hb hab u hu e he
  apply (hn a b ha hb hab u hu e he).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2*β^2*covariancePolynomial c 1 := by positivity
  have hh : (ε/2)^2/(2*B) ≤ (ε/2)^2/(2*β^2*covariancePolynomial c 1) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hd
    nlinarith
  have hm : min (1/4) (((ε/2)^2/(2*B))/2) ≤
      min (1/4) (((ε/2)^2/(2*β^2*covariancePolynomial c 1))/2) :=
    min_le_min le_rfl (by linarith)
  have hN : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
  nlinarith

end SlowEquilibration.SphericalModel
