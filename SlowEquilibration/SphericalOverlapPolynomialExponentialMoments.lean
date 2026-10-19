-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSubcriticalOverlapMoment
public import SlowEquilibration.SphereSupportedIntegrals

/-! Genuine uniform polynomial and exponentially weighted polynomial
moments of the actual uniform-sphere overlap. -/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalAging.HardSphereDynamics SphericalForm
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

def polynomialGaussianConstant (j : ℕ) (a : ℝ) : ℝ :=
  (j.factorial:ℝ)*Real.exp (1/(4*a))

theorem polynomialGaussianConstant_pos (j : ℕ) (a : ℝ) :
    0 < polynomialGaussianConstant j a := by
  unfold polynomialGaussianConstant
  positivity

/-- A true scalar Gaussian-envelope bound, including odd powers. -/
theorem pow_le_polynomialGaussianConstant_mul_exp (j : ℕ) {a t : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) :
    t^j ≤ polynomialGaussianConstant j a*Real.exp (a*t^2) := by
  have hfactor : 0 < (j.factorial:ℝ) := by positivity
  have hp := (div_le_iff₀ hfactor).mp (Real.pow_div_factorial_le_exp t ht j)
  have hcomp : t ≤ a*t^2+1/(4*a) := by
    have he : (1/(4*a))*(4*a)=1 := by field_simp
    nlinarith [sq_nonneg (2*a*t-1)]
  calc
    _ ≤ Real.exp t*(j.factorial:ℝ) := hp
    _ ≤ Real.exp (a*t^2+1/(4*a))*(j.factorial:ℝ) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcomp) hfactor.le
    _ = _ := by rw [Real.exp_add];unfold polynomialGaussianConstant;ring

theorem inverse_sqrt_nat_pow_eq_rpow {N : ℝ} (hN : 0 < N) (j : ℕ) :
    ((Real.sqrt N)^j)⁻¹=N^(-(j:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hN.le,← Real.rpow_neg hN.le]
  congr 1
  ring

theorem overlap_polynomial_exp_pointwise (j : ℕ) {a : ℝ} (ha : 0 < a)
    {N : ℝ} (hN : 0 < N) (b r : ℝ) :
    |r|^j*Real.exp (b*N*r^2) ≤
      polynomialGaussianConstant j a*N^(-(j:ℝ)/2)*Real.exp ((b+a)*N*r^2) := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hp := pow_le_polynomialGaussianConstant_mul_exp j ha
    (mul_nonneg hs.le (abs_nonneg r))
  rw [mul_pow,show a*(Real.sqrt N*|r|)^2=a*N*r^2 by
    rw [mul_pow,Real.sq_sqrt hN.le,sq_abs];ring] at hp
  have hraw : |r|^j ≤ polynomialGaussianConstant j a*Real.exp (a*N*r^2)/((Real.sqrt N)^j) := by
    apply (le_div_iff₀ (pow_pos hs j)).mpr
    exact (mul_comm _ _).trans_le hp
  calc
    _ ≤ (polynomialGaussianConstant j a*Real.exp (a*N*r^2)/((Real.sqrt N)^j))*
      Real.exp (b*N*r^2) := mul_le_mul_of_nonneg_right hraw (Real.exp_pos _).le
    _ = _ := by
      rw [div_eq_mul_inv,inverse_sqrt_nat_pow_eq_rpow hN j]
      have he : Real.exp (a*N*r^2)*Real.exp (b*N*r^2)=Real.exp ((b+a)*N*r^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show polynomialGaussianConstant j a*Real.exp (a*N*r^2)*N^(-(j:ℝ)/2)*
        Real.exp (b*N*r^2)=polynomialGaussianConstant j a*N^(-(j:ℝ)/2)*
          (Real.exp (a*N*r^2)*Real.exp (b*N*r^2)) by ring,he]

/-- The full subcritical range b<1/2, with constants and dimension cutoff
chosen before the spherical center. No overlap moment is assumed. -/
theorem sphere_overlap_polynomial_exp_square_eventually_bounded (j : ℕ) {b : ℝ}
    (hb : 0 ≤ b) (hsub : b < 1/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ x : Vector N,‖x‖^2=(N:ℝ) →
      Integrable (fun u : Vector N=>|overlap x u|^j*Real.exp (b*(N:ℝ)*(overlap x u)^2)) (sphereLaw N) ∧
      (∫ u : Vector N,|overlap x u|^j*Real.exp (b*(N:ℝ)*(overlap x u)^2) ∂sphereLaw N) ≤
        C*(N:ℝ)^(-(j:ℝ)/2) := by
  let a := (1/2-b)/2
  have ha : 0 < a := by dsimp only [a];linarith
  have hba : 0 ≤ b+a := by positivity
  have hbasub : b+a < 1/2 := by dsimp only [a];linarith
  obtain ⟨C,hC,hExp⟩ := sphere_overlap_exp_square_eventually_bounded hba hbasub
  refine ⟨polynomialGaussianConstant j a*C,mul_pos (polynomialGaussianConstant_pos j a) hC,?_⟩
  filter_upwards [hExp,eventually_ge_atTop 1] with N hn hN
  intro x hx
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hF : Continuous (fun u : Vector N=>|overlap x u|^j*Real.exp (b*(N:ℝ)*(overlap x u)^2)) := by
    unfold overlap
    fun_prop
  have hG : Continuous (fun u : Vector N=>Real.exp ((b+a)*(N:ℝ)*(overlap x u)^2)) := by
    unfold overlap
    fun_prop
  have hFI := integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN) hF
  have hGI := (integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN) hG).const_mul
    (polynomialGaussianConstant j a*(N:ℝ)^(-(j:ℝ)/2))
  refine ⟨hFI,?_⟩
  calc
    _ ≤ ∫ u : Vector N,polynomialGaussianConstant j a*(N:ℝ)^(-(j:ℝ)/2)*
      Real.exp ((b+a)*(N:ℝ)*(overlap x u)^2) ∂sphereLaw N :=
        integral_mono hFI hGI (fun u=>overlap_polynomial_exp_pointwise j ha hNp b (overlap x u))
    _ = polynomialGaussianConstant j a*(N:ℝ)^(-(j:ℝ)/2)*
      (∫ u : Vector N,Real.exp ((b+a)*(N:ℝ)*(overlap x u)^2) ∂sphereLaw N) := integral_const_mul _ _
    _ ≤ polynomialGaussianConstant j a*(N:ℝ)^(-(j:ℝ)/2)*C :=
      mul_le_mul_of_nonneg_left (hn x hx) (by positivity [polynomialGaussianConstant_pos j a])
    _ = _ := by ring

/-- Every fixed natural overlap power has its genuine N^(-j/2) rate,
uniformly at every actual spherical axis, including odd j. -/
theorem sphere_overlap_polynomial_eventually_bounded (j : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ x : Vector N,‖x‖^2=(N:ℝ) →
      Integrable (fun u : Vector N=>|overlap x u|^j) (sphereLaw N) ∧
      (∫ u : Vector N,|overlap x u|^j ∂sphereLaw N) ≤ C*(N:ℝ)^(-(j:ℝ)/2) := by
  simpa only [zero_mul,Real.exp_zero,mul_one] using
    sphere_overlap_polynomial_exp_square_eventually_bounded j (by norm_num : 0 ≤ (0:ℝ)) (by norm_num : (0:ℝ) < 1/2)

end
end SlowEquilibration.SphericalModel
