-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeQuadraticEnvelope
public import SlowEquilibration.RadialLaplaceBounds

@[expose] public section

/-! The proper-pure latitude Laplace upper bound, including the physical
entropy prefactor, with the exact Gaussian `N⁻¹ᐟ²` width. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeLaplaceUpper
noncomputable section
open Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeQuadraticEnvelope
open RadialGaussianBounds RadialLaplaceBounds
set_option autoImplicit false

/-- The bounded physical latitude factor times the actual exponent has a
sharp one-dimensional Laplace upper bound, uniformly in nearby energies. -/
theorem sourcePureLatitudeExponent_weighted_laplace_upper
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
    let q := Real.sqrt Q
    ∃ ε b C C₂ : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 < C ∧ 0 ≤ C₂ ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      (∀ e ∈ Icc (E-ε) (E+ε), ∀ a ∈ Icc (q-b) (q+b),
        sourcePureLatitudeExponent p alpha Q β e a ≤
          sourcePureLatitudeExponent p alpha Q β E q+
            β*(e-E)+C₂*(e-E)^2) ∧
      ∀ (N : ℝ), 0 < N → ∀ e ∈ Icc (E-ε) (E+ε),
        (∫ a in Icc (q-b) (q+b),
          (1-a^2)^(-(3/2:ℝ))*
            Real.exp (N*sourcePureLatitudeExponent p alpha Q β e a)) ≤
          C*Real.exp (N*(sourcePureLatitudeExponent p alpha Q β E q+
            β*(e-E)+C₂*(e-E)^2))/Real.sqrt N := by
  dsimp only
  obtain ⟨ε,b,c,C₂,hε,hb,hbq,hc,hC₂,hband,henv⟩ :=
    sourcePureLatitudeExponent_contact_quadratic_envelope p hp alpha halpha h
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  let D : Set ℝ := Icc (q-b) (q+b)
  let W := (1-(q+b)^2)^(-(3/2:ℝ))
  let C := upperConstant W (c/4)
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hqD : q+b ∈ D := ⟨by linarith,le_refl _⟩
  have hqb : q+b < 1 := (hband hqD).2
  have hs0 : 0 < 1-(q+b)^2 := by nlinarith [hq0,hb,hqb]
  have hW : 0 < W := Real.rpow_pos_of_pos hs0 _
  have hC : 0 < C := by
    dsimp [C,upperConstant]
    exact mul_pos hW (Real.sqrt_pos.mpr (div_pos Real.pi_pos (by linarith : 0 < c/4)))
  refine ⟨ε,b,C,C₂,hε,hb,hbq,hC,hC₂,hband,?_,?_⟩
  · intro e he a ha
    have hh := henv e he a ha
    have hnonneg : 0 ≤ c/4*(a-q)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  intro N hN e he
  let θ := sourcePureLatitudeExponent p alpha Q β E q+
    β*(e-E)+C₂*(e-E)^2
  let f := fun a : ℝ => (1-a^2)^(-(3/2:ℝ))*
    Real.exp (N*sourcePureLatitudeExponent p alpha Q β e a)
  have hs (a : ℝ) (ha : a ∈ D) : 0 < 1-a^2 := by
    have hh := hband ha
    nlinarith [hh.1,hh.2]
  have hweight : ContinuousOn (fun a : ℝ => (1-a^2)^(-(3/2:ℝ))) D := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro a ha
    exact Or.inl (hs a ha).ne'
  have hprofile : ContinuousOn (sourcePureLatitudeExponent p alpha Q β e) D := by
    intro a ha
    exact (sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β e a
      h.overlap_range.1 (hband ha)).continuousAt.continuousWithinAt
  have hf : IntegrableOn f D := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hweight.mul (Real.continuous_exp.comp_continuousOn (hprofile.const_mul N))
  have hweightBound (a : ℝ) (ha : a ∈ D) :
      (1-a^2)^(-(3/2:ℝ)) ≤ W := by
    have ha0 : 0 ≤ a := by have hh := ha.1; linarith
    have ha1 : a ≤ q+b := ha.2
    have hsq : a^2 ≤ (q+b)^2 := by
      have hh : 0 ≤ ((q+b)-a)*((q+b)+a) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact Real.rpow_le_rpow_of_nonpos hs0 (by linarith) (by norm_num)
  have hpoint (a : ℝ) (ha : a ∈ D) :
      f a ≤ W*Real.exp (N*θ)*gaussian (c/4*N) q a := by
    have hp := henv e he a ha
    have hExp : Real.exp (N*sourcePureLatitudeExponent p alpha Q β e a) ≤
        Real.exp (N*θ)*gaussian (c/4*N) q a := by
      unfold gaussian
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [θ] at *
      nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hp)]
    exact (mul_le_mul (hweightBound a ha) hExp (Real.exp_nonneg _)
      (Real.rpow_nonneg (by linarith [hs a ha]) _)).trans_eq (by ring)
  have hupper := laplace_integral_upper (f := f) (U := D) measurableSet_Icc
    hf hW.le (by linarith : 0 < c/4) hN hpoint
  exact hupper

/-- The same contact-centered envelope bounds the source band maximized
exponent, with the precise first energy derivative `β`. -/
theorem sourcePureLatitudeExponent_band_maximum_comparison
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
    let q := Real.sqrt Q
    ∃ ε b C₂ : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 ≤ C₂ ∧
      ∀ e ∈ Icc (E-ε) (E+ε), ∀ a ∈ Icc (q-b) (q+b),
        sourcePureLatitudeExponent p alpha Q β e a ≤
          sourcePureLatitudeExponent p alpha Q β E q+
            β*(e-E)+C₂*(e-E)^2 := by
  dsimp only
  obtain ⟨ε,b,c,C₂,hε,hb,hbq,hc,hC₂,_,henv⟩ :=
    sourcePureLatitudeExponent_contact_quadratic_envelope p hp alpha halpha h
  refine ⟨ε,b,C₂,hε,hb,hbq,hC₂,?_⟩
  intro e he a ha
  have hh := henv e he a ha
  have hneg : -c/4*(a-Real.sqrt Q)^2 ≤ 0 := by
    have : 0 ≤ c/4*(a-Real.sqrt Q)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  linarith

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeLaplaceUpper
