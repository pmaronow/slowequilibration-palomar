-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MeasureCovariance
public import SlowEquilibration.SphereSupportedIntegrals
public import SlowEquilibration.SphericalModel

/-! Literal exponential tilt defects and their genuine sphere estimates. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem positive_exp_sub_one_le {s : ℝ} (_hs : 0≤s) :
    Real.exp s-1≤s*Real.exp s := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s)) (Real.exp_pos s).le
  have he : Real.exp (-s)*Real.exp s=1 := by rw [←Real.exp_add];simp
  nlinarith

/-- The literal exponential deviation obeys its true global scalar bound. -/
theorem abs_exp_sub_one_le (w : ℝ) : |Real.exp w-1|≤|w| *Real.exp |w| := by
  have hs : 0≤|w| := abs_nonneg w
  have h1 := positive_exp_sub_one_le hs
  have he := Real.exp_le_exp.mpr (le_abs_self w)
  have he1 : 1≤Real.exp |w| := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hs
  have h2 := Real.add_one_le_exp w
  have hab := neg_abs_le w
  have hm := mul_le_mul_of_nonneg_left he1 hs
  exact abs_le.mpr ⟨by nlinarith,by linarith⟩

/-- The literal weighted reverse-density defect obeys its true scalar square bound. -/
theorem exp_reverse_defect_le_square (w : ℝ) :
    Real.exp w*(1-Real.exp (-w))^2≤w^2*Real.exp |w| := by
  have hsym : Real.exp w*(1-Real.exp (-w))^2=Real.exp w+Real.exp (-w)-2 := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero w]
    ring
  have heq : Real.exp w+Real.exp (-w)=Real.exp |w|+Real.exp (-|w|) := by
    by_cases hw : 0≤w
    · rw [abs_of_nonneg hw]
    · rw [abs_of_neg (lt_of_not_ge hw),neg_neg,add_comm]
  have hs : 0≤|w| := abs_nonneg w
  have ha := positive_exp_sub_one_le hs
  have hb : 1-Real.exp (-|w|)≤|w| := by linarith [Real.add_one_le_exp (-|w|)]
  have hbn : 0≤1-Real.exp (-|w|) := by
    have hh := Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
    simpa only [Real.exp_zero] using (sub_nonneg.mpr hh)
  have han : 0≤|w| *Real.exp |w| := mul_nonneg hs (Real.exp_pos _).le
  have hh := mul_le_mul ha hb hbn han
  have he : Real.exp |w| *Real.exp (-|w|)=1 := by rw [←Real.exp_add];simp
  rw [hsym,heq,←sq_abs w]
  nlinarith

/-- Every continuous actual spherical tilt has its true eta and epsilon
bounds in terms of its weighted correction square, with no moment premise. -/
theorem sphere_exponential_tilt_defects_le {N : ℕ} (hN : 1≤N)
    {β : ℝ} (hβ : 0≤β) (W : Vector N→ℝ) (hW : Continuous W) :
    (∫ u,|Real.exp (β*W u)-1| ∂sphereLaw N)≤
      β*Real.sqrt (∫ u,(W u)^2*Real.exp (2*β*|W u|) ∂sphereLaw N) ∧
    (∫ u,Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw N)≤
      β^2*(∫ u,(W u)^2*Real.exp (2*β*|W u|) ∂sphereLaw N) := by
  let ν := sphereLaw N
  let A := fun u => |Real.exp (β*W u)-1|
  let B := fun u => (W u)^2*Real.exp (2*β*|W u|)
  have hA : Continuous A := (((hW.const_mul β).rexp).sub continuous_const).abs
  have hB : Continuous B := (hW.pow 2).mul ((hW.abs.const_mul (2*β)).rexp)
  have hiA := integrable_sphereSupported_continuous ν (sphereLaw_support hN) hA
  have hiA2 : Integrable (fun u => (A u)^2) ν := integrable_sphereSupported_continuous ν (sphereLaw_support hN) (hA.pow 2)
  have hiB := integrable_sphereSupported_continuous ν (sphereLaw_support hN) hB
  have hmA := memLp_sphereSupported_continuous ν (sphereLaw_support hN) hA (2 : ENNReal)
  have hm1 := memLp_sphereSupported_continuous ν (sphereLaw_support hN)
    (continuous_const : Continuous (fun _ : Vector N => (1 : ℝ))) (2 : ENNReal)
  have hCS := MeasureCovariance.norm_integral_smul_sq_le ν A (fun _ => (1 : ℝ)) hmA hm1
  have hAS : (∫ u,A u ∂ν)^2≤∫ u,(A u)^2 ∂ν := by
    simpa only [smul_eq_mul,mul_one,Real.norm_eq_abs,sq_abs,abs_one,one_pow,
      integral_const,probReal_univ,one_smul] using hCS
  have hpoint : ∀ u,(A u)^2≤β^2*B u := by
    intro u
    have h := abs_exp_sub_one_le (β*W u)
    rw [abs_mul,abs_of_nonneg hβ] at h
    have hs : |Real.exp (β*W u)-1|^2≤(β*|W u| *Real.exp (β*|W u|))^2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
    have he : (Real.exp (β*|W u|))^2=Real.exp (2*β*|W u|) := by
      rw [pow_two,←Real.exp_add]
      congr 1
      ring
    dsimp only [A,B]
    simpa only [mul_pow,sq_abs,he,mul_assoc] using hs
  have hBS : (∫ u,A u ∂ν)^2≤β^2*(∫ u,B u ∂ν) := by
    apply hAS.trans
    exact (integral_mono hiA2 (hiB.const_mul (β^2)) hpoint).trans_eq (integral_const_mul _ _)
  have hBN : 0≤∫ u,B u ∂ν := integral_nonneg (fun u => by dsimp only [B];positivity)
  have hAN : 0≤∫ u,A u ∂ν := integral_nonneg (fun u => by dsimp only [A];positivity)
  refine ⟨?_,?_⟩
  · change (∫ u,A u ∂ν)≤β*Real.sqrt (∫ u,B u ∂ν)
    have hroot := Real.sq_sqrt hBN
    have hn : 0≤β*Real.sqrt (∫ u,B u ∂ν) := by positivity
    nlinarith
  · have hE : Continuous (fun u => Real.exp (β*W u)*(1-Real.exp (-β*W u))^2) := by fun_prop
    have hiE := integrable_sphereSupported_continuous ν (sphereLaw_support hN) hE
    apply (integral_mono hiE (hiB.const_mul (β^2)) ?_).trans_eq (integral_const_mul _ _)
    intro u
    have h := exp_reverse_defect_le_square (β*W u)
    rw [mul_pow,abs_mul,abs_of_nonneg hβ] at h
    dsimp only [B]
    simp only [neg_mul]
    have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (W u)] :
      β*|W u|≤2*β*|W u|)) (mul_nonneg (sq_nonneg β) (sq_nonneg (W u)))
    convert h.trans hm using 1
    ring


/-- A genuine weighted square estimate yields the literal tilt-defect
rates at the same actual spherical dimension. -/
theorem sphere_exponential_tilt_defects_of_square_bound {N d : ℕ} (hN : 1≤N)
    {β C : ℝ} (hβ : 0≤β) (hC : 0≤C) (W : Vector N→ℝ) (hW : Continuous W)
    (hSquare : (∫ u,(W u)^2*Real.exp (2*β*|W u|) ∂sphereLaw N)≤C*(N : ℝ)^(2-(d : ℝ))) :
    (∫ u,|Real.exp (β*W u)-1| ∂sphereLaw N)≤β*Real.sqrt C*(N : ℝ)^(1-(d : ℝ)/2) ∧
    (∫ u,Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw N)≤β^2*C*(N : ℝ)^(2-(d : ℝ)) := by
  have h := sphere_exponential_tilt_defects_le hN hβ W hW
  have hNr : 0<(N : ℝ) := by exact_mod_cast (show 0<N by omega)
  have hpow : Real.sqrt ((N : ℝ)^(2-(d : ℝ)))=(N : ℝ)^(1-(d : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hNr.le]
    congr 1
    ring
  refine ⟨?_,?_⟩
  · apply h.1.trans
    apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hSquare) hβ).trans_eq
    rw [Real.sqrt_mul hC,hpow]
    ring
  · exact h.2.trans ((mul_le_mul_of_nonneg_left hSquare (sq_nonneg β)).trans_eq (by ring))

end
end SlowEquilibration.SphericalModel
