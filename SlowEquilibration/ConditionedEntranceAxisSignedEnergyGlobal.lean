-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisDisintegrationGlobalL1
public import SlowEquilibration.ConditionedEntranceSignedAxisEnergyIntegration

/-! A signed physical Gibbs-fibre energy inequality integrates exactly
under the single global tilt. Every term is assumed L¹ under that actual
tilt; the source-specific modules derive these inputs from the model. -/
@[expose] public section
noncomputable section
open MeasureTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem axisGibbs_signed_energy_global
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2))
    (fB fA fR fK fC : Vector N×Vector N → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hM : 0 < ∫ z : Vector N×Vector N,
      Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))
    (hBi : Integrable fB (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hAi : Integrable fA (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hRi : Integrable fR (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hKi : Integrable fK (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hCi : Integrable fC (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hpoint : ∀ u : Vector N, OnSphere u →
      (∫ x, fB (u,x) ∂gibbsLaw N β (H u))+
        lam/2*(∫ x, fA (u,x) ∂gibbsLaw N β (H u)) ≤
      (∫ x, fR (u,x) ∂gibbsLaw N β (H u))-
        lam/2*(∫ x, fK (u,x) ∂gibbsLaw N β (H u))-
        (∫ x, fC (u,x) ∂gibbsLaw N β (H u))) :
    let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
    let M := ∫ z, Real.exp (w z)
      ∂((sphereLaw N).prod (gibbsLaw N β H₀))
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    (∫ z, fB z ∂ν)+lam/2*(∫ z, fA z ∂ν) ≤
      (∫ z, fR z ∂ν)+lam/2*|∫ z, fK z ∂ν|+|∫ z, fC z ∂ν| := by
  dsimp only
  let m : Vector N → ℝ := fun u => partition N β (H u)/partition N β H₀
  let M := ∫ z : Vector N×Vector N,
    Real.exp (β*(H z.1 z.2-H₀ z.2))
      ∂((sphereLaw N).prod (gibbsLaw N β H₀))
  let t : Vector N → ℝ := fun u => m u/M
  let B : Vector N → ℝ := fun u => ∫ x, fB (u,x) ∂gibbsLaw N β (H u)
  let A : Vector N → ℝ := fun u => ∫ x, fA (u,x) ∂gibbsLaw N β (H u)
  let R : Vector N → ℝ := fun u => ∫ x, fR (u,x) ∂gibbsLaw N β (H u)
  let K : Vector N → ℝ := fun u => ∫ x, fK (u,x) ∂gibbsLaw N β (H u)
  let C : Vector N → ℝ := fun u => ∫ x, fC (u,x) ∂gibbsLaw N β (H u)
  have ht : ∀ᵐ u ∂sphereLaw N, 0 ≤ t u := by
    filter_upwards [] with u
    have hHu : Continuous (H u) := hH.comp (continuous_const.prodMk continuous_id)
    exact div_nonneg (div_nonneg (partition_pos hN β hHu).le
      (partition_pos hN β hH₀).le) hM.le
  obtain ⟨hBint,hBeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fB hM hBi
  obtain ⟨hAint,hAeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fA hM hAi
  obtain ⟨hRint,hReq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fR hM hRi
  obtain ⟨hKint,hKeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fK hM hKi
  obtain ⟨hCint,hCeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fC hM hCi
  have hpointAe : ∀ᵐ u ∂sphereLaw N,
      B u+lam/2*A u ≤ R u-lam/2*K u-C u := by
    filter_upwards [sphereLaw_support hN] with u hu
    exact hpoint u ((onSphere_iff_norm_sq u).mpr hu)
  have hh := signed_fibre_energy_integral_abs (sphereLaw N)
    t B A R K C lam hlam ht hBint hAint hRint hKint hCint hpointAe
  rw [hBeq,hAeq,hReq,hKeq,hCeq] at hh
  exact hh

end SlowEquilibration.ConditionedEntrance
