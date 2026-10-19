-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.StrongFieldGlobal
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Genuine Gaussian Laplace exclusion for the strong-field exponent

These are actual Lebesgue integrals. The negative height gap and quadratic
coercivity are proved from the literal semicircle integral in the preceding
modules. A uniform additive exponent error and any fixed polynomial
prefactor are absorbed with an explicit real threshold, before choosing N.
-/

namespace SlowEquilibration.StrongFieldComplexity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory

def planeVolume : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

def gaussianPlane (c : ℝ) (z : ℝ × ℝ) : ℝ := Real.exp (-c*(z.1^2+z.2^2))

lemma gaussianPlane_eq_prod (c : ℝ) (z : ℝ × ℝ) :
    gaussianPlane c z = Real.exp (-c*z.1^2)*Real.exp (-c*z.2^2) := by
  rw [gaussianPlane, ← Real.exp_add]
  congr 1
  ring

theorem gaussianPlane_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianPlane c) planeVolume := by
  have h := (integrable_exp_neg_mul_sq hc).smul_prod (integrable_exp_neg_mul_sq hc)
  simpa only [smul_eq_mul, ← gaussianPlane_eq_prod, planeVolume] using h

theorem integral_gaussianPlane {c : ℝ} (hc : 0 < c) :
    (∫ z, gaussianPlane c z ∂planeVolume) = Real.pi/c := by
  simp only [gaussianPlane_eq_prod, planeVolume]
  calc
    _ = (∫ x : ℝ, Real.exp (-c*x^2))*(∫ x : ℝ, Real.exp (-c*x^2)) :=
      integral_prod_mul (μ := (volume : Measure ℝ)) (ν := volume)
        (fun x : ℝ => Real.exp (-c*x^2)) (fun x : ℝ => Real.exp (-c*x^2))
    _ = Real.pi/c := by
      rw [integral_gaussian, ← pow_two, Real.sq_sqrt (by positivity)]

/-- Literal mass of the exponentially tilted BCNS scalar exponent. -/
def laplaceMass (a b variance : ℝ) (S : Set (ℝ × ℝ)) (δ N : ℝ) : ℝ :=
  ∫ z in S, Real.exp (N*(exponent a b variance z.1 z.2+δ)) ∂planeVolume

theorem laplace_integrable {a b variance N : ℝ} (hb : 0 < b) (hab : b < a)
    (hvariance : 0 < variance) (hN : 0 < N) (δ : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.exp (N*(exponent a b variance z.1 z.2+δ)))
      planeVolume := by
  let c := precisionCoefficient (a+b) variance (a/(a+b))
  let C := coercivityConstant a b
  have hc : 0 < c := precisionCoefficient_pos (by linarith) hvariance
  have hg := (gaussianPlane_integrable (mul_pos hN hc)).const_mul (Real.exp (N*(C+δ)))
  apply hg.mono'
  · have he := exponent_continuous a b variance
    have hf : Continuous (fun z : ℝ × ℝ => Real.exp (N*(exponent a b variance z.1 z.2+δ))) := by
      fun_prop
    exact hf.aestronglyMeasurable
  · apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), gaussianPlane, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left
      (exponent_le_quadratic_coercivity hb hab hvariance z.1 z.2) hN.le
    change N*exponent a b variance z.1 z.2 ≤ N*(C-c*(z.1^2+z.2^2)) at h
    nlinarith

theorem laplaceMass_nonneg (a b variance : ℝ) (S : Set (ℝ × ℝ)) (δ N : ℝ) :
    0 ≤ laplaceMass a b variance S δ N := by
  exact integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- The proved closed-set gap and tails combine into a genuine Gaussian
envelope with both coefficients positive. -/
theorem exists_exponential_envelope_closed {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (hheight : ∀ z ∈ S, |z.1| ≠ Real.sqrt a) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ z ∈ S,
      exponent a b variance z.1 z.2 ≤ -γ-κ*(z.1^2+z.2^2) := by
  obtain ⟨η,hη,hgap⟩ := exists_uniform_exponent_gap_closed hb hab hvariance hS hheight
  let c := precisionCoefficient (a+b) variance (a/(a+b))
  let C := coercivityConstant a b
  let θ := η/(2*(C+η))
  have hc : 0 < c := precisionCoefficient_pos (by linarith) hvariance
  have hC : 0 < C := coercivityConstant_pos a b
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(C+η))).mpr
    linarith
  have hθeq : θ*(C+η) = η/2 := by
    dsimp [θ]
    field_simp
  refine ⟨η/2,θ*c,by positivity,mul_pos hθ hc,?_⟩
  intro z hz
  have h1 := mul_le_mul_of_nonneg_left (hgap z hz) (by linarith : 0 ≤ 1-θ)
  have h2 := mul_le_mul_of_nonneg_left
    (exponent_le_quadratic_coercivity hb hab hvariance z.1 z.2) hθ.le
  change θ*exponent a b variance z.1 z.2 ≤ θ*(C-c*(z.1^2+z.2^2)) at h2
  nlinarith

/-- Explicit integral bound robust to every uniform exponent error below
one quarter of the genuine gap. -/
theorem exists_laplace_decay_closed {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (hheight : ∀ z ∈ S, |z.1| ≠ Real.sqrt a) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ (δ N : ℝ), δ ≤ γ/4 → 1 ≤ N →
      laplaceMass a b variance S δ N ≤
        (Real.pi/κ)*Real.exp (-(3*γ/4)*N) := by
  obtain ⟨γ,κ,hγ,hκ,henv⟩ := exists_exponential_envelope_closed hb hab hvariance hS hheight
  refine ⟨γ,κ,hγ,hκ,?_⟩
  intro δ N hδ hN
  have hN0 : 0 < N := by linarith
  have hf := (laplace_integrable hb hab hvariance hN0 δ).restrict (s := S)
  have hg := (gaussianPlane_integrable hκ).const_mul (Real.exp (-(3*γ/4)*N))
  have hpoint : ∀ z ∈ S, Real.exp (N*(exponent a b variance z.1 z.2+δ)) ≤
      Real.exp (-(3*γ/4)*N)*gaussianPlane κ z := by
    intro z hz
    rw [gaussianPlane, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left (henv z hz) hN0.le
    have hδ' := mul_le_mul_of_nonneg_left hδ hN0.le
    have hsq : 0 ≤ z.1^2+z.2^2 := by positivity
    have hκsq : 0 ≤ κ*(z.1^2+z.2^2) := mul_nonneg hκ.le hsq
    nlinarith
  unfold laplaceMass
  calc
    _ ≤ ∫ z in S, Real.exp (-(3*γ/4)*N)*gaussianPlane κ z ∂planeVolume :=
      setIntegral_mono_on hf (hg.restrict (s := S)) hS.measurableSet hpoint
    _ ≤ ∫ z, Real.exp (-(3*γ/4)*N)*gaussianPlane κ z ∂planeVolume :=
      setIntegral_le_integral hg (ae_of_all _ (fun _ => by unfold gaussianPlane; positivity))
    _ = (Real.pi/κ)*Real.exp (-(3*γ/4)*N) := by
      rw [integral_const_mul, integral_gaussianPlane hκ]
      ring

/-- A completely explicit real threshold for absorbing a fixed polynomial
prefactor into an exponential. -/
def polynomialAbsorptionThreshold (B : ℝ) (d : ℕ) (α : ℝ) : ℝ :=
  max 1 (B*((d+1).factorial : ℝ)/α^(d+1))

theorem polynomial_le_exp_of_threshold {B α N : ℝ} (d : ℕ)
    (_hB : 0 ≤ B) (hα : 0 < α) (hN : polynomialAbsorptionThreshold B d α ≤ N) :
    B*N^d ≤ Real.exp (α*N) := by
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 ≤ N := by linarith
  have hbase : B*((d+1).factorial : ℝ) ≤ N*α^(d+1) := by
    have ht : B*((d+1).factorial : ℝ)/α^(d+1) ≤ N := (le_max_right _ _).trans hN
    exact (div_le_iff₀ (pow_pos hα _)).mp ht
  have hf : 0 < ((d+1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (d+1)
  have hscaled := mul_le_mul_of_nonneg_right hbase (pow_nonneg hN0 d)
  apply le_trans _ (Real.pow_div_factorial_le_exp (α*N) (mul_nonneg hα.le hN0) (d+1))
  apply (le_div_iff₀ hf).mpr
  rw [mul_pow, pow_succ N]
  convert hscaled using 1 <;> ring

/-- Fixed polynomial prefactors and uniform exponent errors are absorbed
before N is chosen, with the explicit threshold displayed in the result. -/
theorem exists_laplace_polynomial_decay_closed {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (hheight : ∀ z ∈ S, |z.1| ≠ Real.sqrt a) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ (B : ℝ) (d : ℕ), 0 ≤ B →
      ∀ (δ N : ℝ), δ ≤ γ/4 →
        polynomialAbsorptionThreshold (B*(Real.pi/κ)) d (γ/4) ≤ N →
        B*N^d*laplaceMass a b variance S δ N ≤ Real.exp (-(γ/2)*N) := by
  obtain ⟨γ,κ,hγ,hκ,hdecay⟩ := exists_laplace_decay_closed hb hab hvariance hS hheight
  refine ⟨γ,κ,hγ,hκ,?_⟩
  intro B d hB δ N hδ hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 ≤ N := by linarith
  have hpoly := polynomial_le_exp_of_threshold d
    (mul_nonneg hB (by positivity : 0 ≤ Real.pi/κ)) (by positivity : 0 < γ/4) hN
  have hmass := mul_le_mul_of_nonneg_left (hdecay δ N hδ hN1)
    (mul_nonneg hB (pow_nonneg hN0 d))
  calc
    B*N^d*laplaceMass a b variance S δ N ≤
        (B*(Real.pi/κ)*N^d)*Real.exp (-(3*γ/4)*N) := by nlinarith [hmass]
    _ ≤ Real.exp ((γ/4)*N)*Real.exp (-(3*γ/4)*N) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = Real.exp (-(γ/2)*N) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Literal low-height window used to exclude a low spherical maximum. -/
def heightWindow (a ε : ℝ) : Set (ℝ × ℝ) := Icc 0 (Real.sqrt a-ε) ×ˢ univ

theorem heightWindow_isClosed (a ε : ℝ) : IsClosed (heightWindow a ε) :=
  isClosed_Icc.prod isClosed_univ

theorem exists_laplace_polynomial_decay_heightWindow {a b variance ε : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance) (hε : 0 < ε) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ (B : ℝ) (d : ℕ), 0 ≤ B →
      ∀ (δ N : ℝ), δ ≤ γ/4 →
        polynomialAbsorptionThreshold (B*(Real.pi/κ)) d (γ/4) ≤ N →
        B*N^d*laplaceMass a b variance (heightWindow a ε) δ N ≤ Real.exp (-(γ/2)*N) := by
  apply exists_laplace_polynomial_decay_closed hb hab hvariance (heightWindow_isClosed a ε)
  intro z hz
  have hz0 : 0 ≤ z.1 := hz.1.1
  have hz1 : z.1 ≤ Real.sqrt a-ε := hz.1.2
  rw [abs_of_nonneg hz0]
  intro he
  linarith

theorem laplaceMass_heightWindow_eq_iterated {a b variance N : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance) (hN : 0 < N) (δ ε : ℝ) :
    laplaceMass a b variance (heightWindow a ε) δ N =
      ∫ h in Icc 0 (Real.sqrt a-ε),
        ∫ k, Real.exp (N*(exponent a b variance h k+δ)) := by
  rw [laplaceMass, heightWindow]
  have hi := (laplace_integrable hb hab hvariance hN δ).restrict
    (s := Icc (0 : ℝ) (Real.sqrt a-ε) ×ˢ (univ : Set ℝ))
  dsimp only [planeVolume] at hi ⊢
  have he := setIntegral_prod
    (fun z : ℝ × ℝ => Real.exp (N*(exponent a b variance z.1 z.2+δ))) hi
  simpa only [Measure.restrict_univ] using he

/-- A lower cutoff strictly above the negative endpoint allows Gaussian
constant terms in the physical Hamiltonian. -/
def heightBand (a ε ℓ : ℝ) : Set (ℝ × ℝ) := Icc ℓ (Real.sqrt a-ε) ×ˢ univ

theorem heightBand_isClosed (a ε ℓ : ℝ) : IsClosed (heightBand a ε ℓ) :=
  isClosed_Icc.prod isClosed_univ

theorem exists_laplace_polynomial_decay_heightBand {a b variance ε ℓ : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance) (hε : 0 < ε)
    (hℓ : -Real.sqrt a < ℓ) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ (B : ℝ) (d : ℕ), 0 ≤ B →
      ∀ (δ N : ℝ), δ ≤ γ/4 →
        polynomialAbsorptionThreshold (B*(Real.pi/κ)) d (γ/4) ≤ N →
        B*N^d*laplaceMass a b variance (heightBand a ε ℓ) δ N ≤ Real.exp (-(γ/2)*N) := by
  apply exists_laplace_polynomial_decay_closed hb hab hvariance (heightBand_isClosed a ε ℓ)
  intro z hz he
  have hz0 : ℓ ≤ z.1 := hz.1.1
  have hz1 : z.1 ≤ Real.sqrt a-ε := hz.1.2
  rcases eq_or_eq_neg_of_abs_eq he with h | h <;> linarith

/-- The literal half-negative window needed when the field has a Gaussian
constant component. -/
theorem exists_laplace_polynomial_decay_halfNegativeWindow {a b variance ε : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance) (hε : 0 < ε) :
    ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧ ∀ (B : ℝ) (d : ℕ), 0 ≤ B →
      ∀ (δ N : ℝ), δ ≤ γ/4 →
        polynomialAbsorptionThreshold (B*(Real.pi/κ)) d (γ/4) ≤ N →
        B*N^d*laplaceMass a b variance
          (heightBand a ε (-Real.sqrt a/2)) δ N ≤ Real.exp (-(γ/2)*N) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (hb.trans hab)
  exact exists_laplace_polynomial_decay_heightBand hb hab hvariance hε (by linarith)

theorem laplaceMass_heightBand_eq_iterated {a b variance N : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance) (hN : 0 < N) (δ ε ℓ : ℝ) :
    laplaceMass a b variance (heightBand a ε ℓ) δ N =
      ∫ h in Icc ℓ (Real.sqrt a-ε),
        ∫ k, Real.exp (N*(exponent a b variance h k+δ)) := by
  rw [laplaceMass, heightBand]
  have hi := (laplace_integrable hb hab hvariance hN δ).restrict
    (s := Icc ℓ (Real.sqrt a-ε) ×ˢ (univ : Set ℝ))
  dsimp only [planeVolume] at hi ⊢
  have he := setIntegral_prod
    (fun z : ℝ × ℝ => Real.exp (N*(exponent a b variance z.1 z.2+δ))) hi
  simpa only [Measure.restrict_univ] using he

end
end SlowEquilibration.StrongFieldComplexity
