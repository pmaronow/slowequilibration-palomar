-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceUpperSelected
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! The deterministic one-sided energy integral in source Corollary 12.17.
It retains the exact exponential decay in the lower-window displacement. -/

namespace SlowEquilibration.SourceMixedLowSumIntegral
noncomputable section
open Set MeasureTheory
set_option autoImplicit false

theorem integral_below_window_exp_bound
    (f : ℝ → ℝ) (l m M a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A)
    (hf : IntegrableOn f (Icc l (m-M)))
    (hbound : ∀ E ∈ Icc l (m-M), f E ≤ A*Real.exp (a*(E-m))) :
    (∫ E in Icc l (m-M), f E ∂volume) ≤
      A/a*Real.exp (-a*M) := by
  have hExpInt : IntegrableOn (fun E : ℝ => Real.exp (a*(E-m))) (Iic (m-M)) := by
    have hh := (integrableOn_exp_mul_Iic ha (m-M)).mul_const (Real.exp (-a*m))
    have hpoint (E : ℝ) : Real.exp (a*(E-m)) =
        Real.exp (a*E)*Real.exp (-a*m) := by
      rw [←Real.exp_add]
      congr 1
      ring
    simpa only [IntegrableOn,hpoint] using hh
  have hMajorInt : IntegrableOn (fun E : ℝ => A*Real.exp (a*(E-m))) (Iic (m-M)) :=
    hExpInt.const_mul A
  have hMajorCompact : IntegrableOn (fun E : ℝ => A*Real.exp (a*(E-m)))
      (Icc l (m-M)) := hMajorInt.mono_set (fun _ hE => hE.2)
  have hStep : (∫ E in Icc l (m-M), f E ∂volume) ≤
      ∫ E in Icc l (m-M), A*Real.exp (a*(E-m)) ∂volume :=
    setIntegral_mono_on hf hMajorCompact measurableSet_Icc hbound
  have hStep2 : (∫ E in Icc l (m-M), A*Real.exp (a*(E-m)) ∂volume) ≤
      ∫ E in Iic (m-M), A*Real.exp (a*(E-m)) ∂volume :=
    setIntegral_mono_set hMajorInt
      (.of_forall (fun _ => mul_nonneg hA (Real.exp_pos _).le))
      (.of_forall (fun _ hE => hE.2))
  have hTail : (∫ E in Iic (m-M), A*Real.exp (a*(E-m)) ∂volume) =
      A/a*Real.exp (-a*M) := by
    rw [integral_const_mul]
    have hpoint (E : ℝ) : Real.exp (a*(E-m)) = Real.exp (-a*m)*Real.exp (a*E) := by
      rw [←Real.exp_add]
      congr 1
      ring
    simp_rw [hpoint]
    rw [integral_const_mul,integral_exp_mul_Iic ha]
    have hexp : Real.exp (-a*m)*Real.exp (a*(m-M)) = Real.exp (-a*M) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [show A*(Real.exp (-a*m)*(Real.exp (a*(m-M))/a)) =
      A/a*(Real.exp (-a*m)*Real.exp (a*(m-M))) by ring,hexp]
  exact hStep.trans (hStep2.trans_eq hTail)

/-- The quadratic energy error remains linear in the distance below the
centering throughout the source's coarse window. -/
theorem centered_energy_square_window_bound
    {N τ h u : ℝ} (hN : 0 < N) (hu : 0 ≤ u)
    (hcenter : 3*|h| ≤ τ*N) (hupper : u ≤ τ*N+h) :
    (h-u)^2/N ≤ h^2/N+2*τ*u := by
  have hcap : 2*|h|+h ≤ τ*N := by
    nlinarith [le_abs_self h]
  have hu2 : u^2 ≤ u*(τ*N+h) := by
    nlinarith [mul_le_mul_of_nonneg_left hupper hu]
  have hcross : -2*h*u ≤ 2*|h| * u := by
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs h) hu]
  have hcap' : (2*|h|+h)*u ≤ τ*N*u :=
    mul_le_mul_of_nonneg_right hcap hu
  have hsq : (h-u)^2 ≤ h^2+2*τ*N*u := by
    nlinarith [hu2,hcross,hcap']
  apply (div_le_iff₀ hN).mpr
  calc
    (h-u)^2 ≤ h^2+2*τ*N*u := hsq
    _ = (h^2/N+2*τ*u)*N := by field_simp

/-- The Palm exponent and the all-critical intensity slope together have
strictly negative rate below the window. -/
theorem centered_energy_decay_exponent
    {N τ h u β cPlus C₂ : ℝ}
    (hN : 0 < N) (hu : 0 ≤ u)
    (hcenter : 3*|h| ≤ τ*N) (hupper : u ≤ τ*N+h)
    (hC₂ : 0 < C₂)
    (hτ : τ ≤ (β-cPlus)/(4*C₂)) :
    (cPlus-β)*u+C₂*(h-u)^2/N ≤
      C₂*h^2/N-(β-cPlus)/2*u := by
  have hsq := centered_energy_square_window_bound hN hu hcenter hupper
  have hrate : 2*C₂*τ ≤ (β-cPlus)/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C₂)).mp hτ
    nlinarith
  have hsq' := mul_le_mul_of_nonneg_left hsq hC₂.le
  calc
    _ = (cPlus-β)*u+C₂*((h-u)^2/N) := by ring
    _ ≤ (cPlus-β)*u+C₂*(h^2/N+2*τ*u) := by
      simpa only [add_comm] using add_le_add_left hsq' ((cPlus-β)*u)
    _ = C₂*h^2/N+((cPlus-β)+2*C₂*τ)*u := by ring
    _ ≤ C₂*h^2/N-(β-cPlus)/2*u := by
      nlinarith [mul_le_mul_of_nonneg_right hrate hu]

/-- Combining a source intensity envelope with the Palm band upper bound
gives the exact integrable density below the centered window. -/
theorem intensity_palm_product_below_window
    (dens palm : ℝ → ℝ) {N m E₀ τ E β cPlus C₂ Cdens C₁ D : ℝ}
    (hN : 0 < N) (hC₂ : 0 < C₂) (hCdens : 0 ≤ Cdens)
    (hC₁ : 0 ≤ C₁) (hD : 0 ≤ D)
    (hE : E ≤ m) (hlow : N*(E₀-τ) ≤ E)
    (hcenter : 3*|m-N*E₀| ≤ τ*N)
    (hτ : τ ≤ (β-cPlus)/(4*C₂))
    (hP0 : 0 ≤ palm E)
    (hdens : dens E ≤ Cdens*Real.exp (cPlus*(m-E)))
    (hP : palm E ≤ C₁*D*Real.exp
      (β*(E-m)+C₂*(E-N*E₀)^2/N)) :
    dens E*palm E ≤
      (Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N)) *
        Real.exp (((β-cPlus)/2)*(E-m)) := by
  let u := m-E
  let h := m-N*E₀
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hupper : u ≤ τ*N+h := by dsimp [u,h]; linarith [hlow]
  have hrate := centered_energy_decay_exponent hN hu hcenter hupper hC₂ hτ
  have hdensmajor : 0 ≤ Cdens*Real.exp (cPlus*u) := by positivity
  have hPmajor : 0 ≤ C₁*D*Real.exp (β*(E-m)+C₂*(E-N*E₀)^2/N) := by
    positivity
  have hproduct : dens E*palm E ≤
      (Cdens*Real.exp (cPlus*u))*
        (C₁*D*Real.exp (β*(E-m)+C₂*(E-N*E₀)^2/N)) := by
    apply mul_le_mul (by simpa only [u] using hdens) hP hP0 hdensmajor
  have harg : β*(E-m)+C₂*(E-N*E₀)^2/N =
      -β*u+C₂*(h-u)^2/N := by
    dsimp [u,h]
    ring
  calc
    dens E*palm E ≤ (Cdens*Real.exp (cPlus*u))*
        (C₁*D*Real.exp (β*(E-m)+C₂*(E-N*E₀)^2/N)) := hproduct
    _ = Cdens*C₁*D*Real.exp ((cPlus-β)*u+C₂*(h-u)^2/N) := by
      rw [harg]
      have hexp : Real.exp (cPlus*u)*Real.exp (-β*u+C₂*(h-u)^2/N) =
          Real.exp ((cPlus-β)*u+C₂*(h-u)^2/N) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        _ = Cdens*C₁*D*(Real.exp (cPlus*u)*Real.exp (-β*u+C₂*(h-u)^2/N)) := by ring
        _ = _ := by rw [hexp]
    _ ≤ Cdens*C₁*D*Real.exp (C₂*h^2/N-(β-cPlus)/2*u) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate)
        (by positivity)
    _ = (Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N)) *
        Real.exp (((β-cPlus)/2)*(E-m)) := by
      rw [show C₂*h^2/N-(β-cPlus)/2*u =
        C₂*(m-N*E₀)^2/N+(β-cPlus)/2*(E-m) by dsimp [u,h]; ring]
      rw [Real.exp_add]
      ring

/-- The complete deterministic integral of the source intensity and Palm
envelopes, with the finite-size centering correction retained explicitly. -/
theorem intensity_palm_below_window_integral
    (dens palm : ℝ → ℝ) {N m E₀ τ M β cPlus C₂ Cdens C₁ D : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hC₂ : 0 < C₂)
    (hCdens : 0 ≤ Cdens) (hC₁ : 0 ≤ C₁) (hD : 0 ≤ D)
    (hgap : 0 < β-cPlus)
    (hcenter : 3*|m-N*E₀| ≤ τ*N)
    (hτ : τ ≤ (β-cPlus)/(4*C₂))
    (hInt : IntegrableOn (fun E => dens E*palm E)
      (Icc (N*(E₀-τ)) (m-M)))
    (hP0 : ∀ E ∈ Icc (N*(E₀-τ)) (m-M), 0 ≤ palm E)
    (hDens : ∀ E ∈ Icc (N*(E₀-τ)) (m-M),
      dens E ≤ Cdens*Real.exp (cPlus*(m-E)))
    (hPalm : ∀ E ∈ Icc (N*(E₀-τ)) (m-M),
      palm E ≤ C₁*D*Real.exp
        (β*(E-m)+C₂*(E-N*E₀)^2/N)) :
    (∫ E in Icc (N*(E₀-τ)) (m-M), dens E*palm E ∂volume) ≤
      (Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N))/
        ((β-cPlus)/2)*Real.exp (-((β-cPlus)/2)*M) := by
  have ha : 0 < (β-cPlus)/2 := by linarith
  have hA : 0 ≤ Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N) := by
    positivity
  apply integral_below_window_exp_bound
    (fun E => dens E*palm E) (N*(E₀-τ)) m M ((β-cPlus)/2)
    (Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N)) ha hA hInt
  intro E hE
  exact intensity_palm_product_below_window dens palm
    hN hC₂ hCdens hC₁ hD (by linarith [hE.2,hM]) hE.1
    hcenter hτ (hP0 E hE) (hDens E hE) (hPalm E hE)

end
end SlowEquilibration.SourceMixedLowSumIntegral
