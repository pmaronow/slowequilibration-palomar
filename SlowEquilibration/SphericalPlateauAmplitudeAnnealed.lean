-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFeatureBounds
public import SlowEquilibration.SphericalPlateauAmplitudeDerivative
public import SlowEquilibration.GaussianDensity

@[expose] public section

/-! # Exact actual bank Gaussian exponential moments and pole-budget bound -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem amplitudeField_exp_integral (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (u : Vector (n+1)) :
    (∫ D : BankDisorder n μ,Real.exp (β*amplitudeField μ x e p₀ s D u) ∂bankLaw n μ)=
      Real.exp (β^2*‖amplitudeBankFeature μ x e p₀ s u‖^2/2) := by
  let v := amplitudeBankFeature μ x e p₀ s u
  have he (D : BankDisorder n μ) : β*amplitudeField μ x e p₀ s D u=
      β*inner ℝ v (euclideanBank D) := by
    have hh := amplitudeBankLinear_apply μ β x e p₀ s u (euclideanBank D)
    rw [unpackBank_euclideanBank] at hh
    simpa only [amplitudeBankLinear,smul_apply,smul_eq_mul,innerSL_apply_apply,v] using hh.symm
  simp_rw [he]
  have hm : (∫ D : BankDisorder n μ,Real.exp (β*inner ℝ v (euclideanBank D)) ∂bankLaw n μ)=
      ∫ w : EuclideanBank n μ,Real.exp (β*inner ℝ v w) ∂stdGaussian (EuclideanBank n μ) :=
    (actual_bank_flattened_gaussian n μ).integral_comp
    ((Real.continuous_exp.comp ((continuous_const.mul
      ((innerSL ℝ v).continuous)))).aestronglyMeasurable)
  change (∫ D : BankDisorder n μ,Real.exp (β*inner ℝ v (euclideanBank D)) ∂bankLaw n μ)=
    ∫ w : EuclideanBank n μ,Real.exp (β*inner ℝ v w) ∂stdGaussian (EuclideanBank n μ) at hm
  rw [hm,GaussianDensity.integral_exp_inner_stdGaussian]

lemma finite_xi_le_one_of_abs_le (μ : FiniteMixture) {r : ℝ} (hr : |r|≤1) :
    μ.xi r≤μ.xi 1 := by
  unfold FiniteMixture.xi
  apply Finset.sum_le_sum
  intro p _
  simp only [one_pow,mul_one]
  have hp : |r|^p≤1 := pow_le_one₀ (abs_nonneg r) hr
  calc
    μ.coeff p*r^p≤μ.coeff p*1 := mul_le_mul_of_nonneg_left
      (((le_abs_self (r^p)).trans_eq (abs_pow r p)).trans hp) (μ.nonneg p)
    _=μ.coeff p := mul_one _

/-- Genuine weighted exponential budget at every physical spin. Integrating
this bound over a polar region gives its actual annealed partition budget. -/
theorem amplitudeWeightedPoint_exp_integral_le (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (hK : 0 ≤ sourceK J δ) (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (hs : ∀ j,|s j|≤2)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ)) :
    (∫ D : BankDisorder n μ,Real.exp
      (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D u-
        2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)) ∂bankLaw n μ)≤
      Real.exp (3*β^2*((n+1:ℕ):ℝ)*μ.xi 1) := by
  let A := amplitudeBasePotential μ β J δ q₁ q₂ x u
  have hfun : (fun D : BankDisorder n μ => Real.exp
      (β*amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D u-
        2*((n+1:ℕ):ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)))=
      fun D => Real.exp A*Real.exp (β*amplitudeField μ x (latitudeFrameAt x) p₀ s D u) := by
    funext D
    rw [← Real.exp_add]
    congr 1
    unfold A amplitudeBasePotential amplitudePlantedField
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  rw [hfun,integral_const_mul,amplitudeField_exp_integral,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hξ := finite_xi_le_one_of_abs_le μ
    (abs_le.mpr (overlap_mem_Icc_of_norm_sq (by omega : 1≤n+1) x u hx hu))
  have hp : 0 ≤ sourceProfile J δ q₁ q₂ (overlap x u) := profile_nonneg _ _ _ hK _
  have hNp : 0≤((n+1:ℕ):ℝ) := by positivity
  have hA : A≤β^2*((n+1:ℕ):ℝ)*μ.xi 1 := by
    have hh := mul_le_mul_of_nonneg_left hξ (mul_nonneg (sq_nonneg β) hNp)
    unfold A amplitudeBasePotential
    simp only [Nat.cast_add,Nat.cast_one] at hh hNp ⊢
    nlinarith
  have hNorm := amplitudeBankFeature_norm_le μ x hx p₀ s hs u hu
  have hNon : 0≤((n+1:ℕ):ℝ)*μ.xi 1 := mul_nonneg hNp (μ.xi_pos (by norm_num)).le
  have hSq := Real.sq_sqrt hNon
  have hVar : ‖amplitudeBankFeature μ x (latitudeFrameAt x) p₀ s u‖^2≤
      4*((n+1:ℕ):ℝ)*μ.xi 1 := by
    nlinarith [Real.sqrt_nonneg (((n+1:ℕ):ℝ)*μ.xi 1),
      norm_nonneg (amplitudeBankFeature μ x (latitudeFrameAt x) p₀ s u)]
  nlinarith [sq_nonneg β]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
