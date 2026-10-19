-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPalmFullExpIntegrable

@[expose] public section

/-! The sharp physical GOE determinant moment and scalar Gaussian posterior
give pointwise integrability needed for angular Palm Fubini. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory Filter SphericalModel ConditionedDeterminantMoments
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem sq_eq_scaled_sq (x m : ℝ) (hm : m ≠ 0) :
    x^2 = m^2*(x/m)^2 := by
  field_simp [hm]

theorem intrinsicDet_physicalMixedPalm_sq_integrable_eventually
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
        (mark : EuclideanSpace ℝ (Fin 2)),
        2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ mark 1 →
        Integrable (fun J => (intrinsicDet μ Q u J)^2)
          (mixedLaw μ Q u hu mark) := by
  have hdet := mixed_conditioned_determinant_moments_sharp_eventually μ hQ hnp hg
  filter_upwards [hdet] with d hd
  intro u hu mark hmark
  obtain ⟨_,_,hm,hDint,_⟩ := hd u hu mark hmark 2 (by norm_num)
  simp only [Real.rpow_two] at hDint
  let m := ∫ J, intrinsicDet μ Q u J ∂mixedLaw μ Q u hu mark
  have hm' : m ≠ 0 := (ne_of_gt hm)
  convert hDint.const_mul (m^2) using 1
  funext J
  change (intrinsicDet μ Q u J)^2 = m^2*(intrinsicDet μ Q u J/m)^2
  exact sq_eq_scaled_sq _ m hm'

theorem originalLatitudeBankPoint_det_integrable_eventually
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) {g : ℝ} (hg : 0 < g)
    (a β : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
        (mark : EuclideanSpace ℝ (Fin 2)),
        2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ mark 1 →
        ∀ y : Vector (d+1),
          Integrable (fun J => intrinsicDet μ Q u J *
            originalLatitudeBankPoint μ a β u J y)
            (mixedLaw μ Q u hu mark) := by
  filter_upwards [intrinsicDet_physicalMixedPalm_sq_integrable_eventually
      μ hQ hnp hg] with d hd
  intro u hu mark hmark y
  exact originalLatitudeBankPoint_det_integrable_of_det_sq μ Q a β u hu mark
    (hd u hu mark hmark) y

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
