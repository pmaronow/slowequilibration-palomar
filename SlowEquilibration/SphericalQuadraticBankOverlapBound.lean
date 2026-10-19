-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSubcriticalOverlapMoment

@[expose] public section

/-! Uniform second-moment overlap factor for the quadratic latitude bank.
The transverse sphere has dimension `n`, while the covariance retains the
ambient dimension `n+1`; a strict subcritical margin absorbs that shift. -/

namespace SlowEquilibration.SphericalQuadraticBankOverlapBound
noncomputable section
open Filter Set MeasureTheory SphericalModel
open SphericalAging.HardSphereDynamics SphericalForm
open scoped Topology
set_option autoImplicit false

/-- The Gaussian quadratic-bank replica factor is uniformly bounded for
all latitudes in one band whenever its coefficient has the printed strict
margin. The integral is over the genuine transverse spherical law. -/
theorem quadratic_bank_overlap_factor_eventually_bounded
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (B : Set ℝ) (c : ℝ → ℝ)
    (hc : ∀ a ∈ B, 0 ≤ c a ∧ 2*c a ≤ 1-ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ x : Vector n, ‖x‖^2=(n:ℝ) →
          ∀ a ∈ B,
            (∫ y : Vector n,
              Real.exp (c a*((n+1:ℕ):ℝ)*(overlap x y)^2)
              ∂sphereLaw n) ≤ C := by
  let b : ℝ := (1-ε/2)/2
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbsub : b < 1/2 := by dsimp [b]; linarith
  obtain ⟨C,hC,hbound⟩ :=
    sphere_overlap_exp_square_eventually_bounded hb0 hbsub
  refine ⟨C,hC,?_⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, 2/ε ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2/ε))
  filter_upwards [hbound,hlarge,eventually_ge_atTop 1] with n hn hnlarge hn1
  intro x hx a ha
  have hc₀ := (hc a ha).1
  have hc₁ := (hc a ha).2
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hεn : 2 ≤ ε*(n:ℝ) := by
    have hh := (div_le_iff₀ hε).mp hnlarge
    nlinarith
  have hcoef : c a*((n+1:ℕ):ℝ) ≤ b*(n:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hc₁
      (show 0 ≤ ((n+1:ℕ):ℝ) by positivity)
    dsimp [b]
    push_cast at hmul ⊢
    nlinarith [hc₀]
  have hcont₁ : Continuous (fun y : Vector n =>
      Real.exp (c a*((n+1:ℕ):ℝ)*(overlap x y)^2)) := by
    unfold overlap
    fun_prop
  have hcont₂ : Continuous (fun y : Vector n =>
      Real.exp (b*(n:ℝ)*(overlap x y)^2)) := by
    unfold overlap
    fun_prop
  have hi₁ : Integrable (fun y : Vector n =>
      Real.exp (c a*((n+1:ℕ):ℝ)*(overlap x y)^2)) (sphereLaw n) :=
    integrable_sphereSupported_continuous (sphereLaw n)
      (sphereLaw_support hn1) hcont₁
  have hi₂ : Integrable (fun y : Vector n =>
      Real.exp (b*(n:ℝ)*(overlap x y)^2)) (sphereLaw n) :=
    integrable_sphereSupported_continuous (sphereLaw n)
      (sphereLaw_support hn1) hcont₂
  have hmono : (∫ y : Vector n,
      Real.exp (c a*((n+1:ℕ):ℝ)*(overlap x y)^2) ∂sphereLaw n) ≤
      (∫ y : Vector n,
        Real.exp (b*(n:ℝ)*(overlap x y)^2) ∂sphereLaw n) := by
    apply integral_mono hi₁ hi₂
    intro y
    apply Real.exp_le_exp.mpr
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg (overlap x y))
  exact hmono.trans (hn x hx)

end
end SlowEquilibration.SphericalQuadraticBankOverlapBound
