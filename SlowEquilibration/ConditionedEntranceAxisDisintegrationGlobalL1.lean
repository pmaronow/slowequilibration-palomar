-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisDisintegrationL1
public import SlowEquilibration.ConditionedEntranceNormalizedTiltIntegrable

/-! An actual globally tilted L¹ observable disintegrates to a genuine
L¹ partition-weighted Gibbs-fibre observable, with equal expectations. -/
@[expose] public section
noncomputable section
open MeasureTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 350000

theorem axisGibbs_globalTilt_integral_disintegration_L1
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H₀ : Vector N → ℝ) (hH₀ : Continuous H₀)
    (H : Vector N → Vector N → ℝ)
    (hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2))
    (f : Vector N×Vector N → ℝ)
    (hM : 0 < ∫ z : Vector N×Vector N,
      Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))
    (hf : Integrable f (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀))))) :
    let M := ∫ z : Vector N×Vector N,
      Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀))
    let m : Vector N → ℝ := fun u => partition N β (H u)/partition N β H₀
    let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
    Integrable (fun u => (m u/M)*
      (∫ x, f (u,x) ∂gibbsLaw N β (H u))) (sphereLaw N) ∧
    (∫ u, (m u/M)*
      (∫ x, f (u,x) ∂gibbsLaw N β (H u)) ∂sphereLaw N) =
      ∫ z, f z ∂normalizedTilt
        ((sphereLaw N).prod (gibbsLaw N β H₀)) w M := by
  dsimp only
  let w : Vector N×Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let M := ∫ z, Real.exp (w z)
    ∂((sphereLaw N).prod (gibbsLaw N β H₀))
  have hw : Measurable w :=
    ((hH.sub (hH₀.comp continuous_snd)).const_mul β).measurable
  have hif := (integrable_normalizedTilt_iff
    ((sphereLaw N).prod (gibbsLaw N β H₀)) w f hw hM).1 hf
  exact ⟨axisGibbs_partitionWeighted_fibre_integrable hN β H₀ hH₀ H hH
    f M hM hif,
    axisGibbs_globalTilt_integral_disintegration_integrable hN β H₀ hH₀ H hH f hif⟩

end SlowEquilibration.ConditionedEntrance
