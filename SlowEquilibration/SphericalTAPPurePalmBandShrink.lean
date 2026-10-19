-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPurePalmLaplaceBridge

@[expose] public section

/-! The positive pure latitude Laplace integral decreases when its
physical contact band is narrowed. -/

namespace SlowEquilibration.SphericalTAPPurePalmBandShrink
noncomputable section
open Set MeasureTheory
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
set_option autoImplicit false

theorem sourcePureLatitudeLaplace_mono_band
    (d p : ℕ) (hp : 2 ≤ p) (alpha : ℝ)
    {Q : ℝ} (hQ : 0 < Q) (β e q b₁ b₂ : ℝ)
    (hbb : b₁ ≤ b₂)
    (hband : Icc (q-b₂) (q+b₂) ⊆ Ioo (-1:ℝ) 1) :
    (∫ a in Icc (q-b₁) (q+b₁),
      (1-a^2)^(-(3/2:ℝ)) *
        Real.exp (((d+2:ℕ):ℝ)*sourcePureLatitudeExponent p alpha Q β e a)) ≤
    (∫ a in Icc (q-b₂) (q+b₂),
      (1-a^2)^(-(3/2:ℝ)) *
        Real.exp (((d+2:ℕ):ℝ)*sourcePureLatitudeExponent p alpha Q β e a)) := by
  let S₁ := Icc (q-b₁) (q+b₁)
  let S₂ := Icc (q-b₂) (q+b₂)
  let f := fun a : ℝ => (1-a^2)^(-(3/2:ℝ)) *
    Real.exp (((d+2:ℕ):ℝ)*sourcePureLatitudeExponent p alpha Q β e a)
  have hsub : S₁ ⊆ S₂ := by
    intro a ha
    exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
  have hs (a : ℝ) (ha : a ∈ S₂) : 0 < 1-a^2 := by
    have hh := hband ha
    nlinarith [hh.1,hh.2]
  have hfcont : ContinuousOn f S₂ := by
    have hpow : ContinuousOn (fun a : ℝ => (1-a^2)^(-(3/2:ℝ))) S₂ := by
      apply ContinuousOn.rpow_const (by fun_prop)
      intro a ha
      exact Or.inl (hs a ha).ne'
    have hprof : ContinuousOn (sourcePureLatitudeExponent p alpha Q β e) S₂ := by
      intro a ha
      exact (sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β e a
        hQ (hband ha)).continuousAt.continuousWithinAt
    exact hpow.mul (Real.continuous_exp.comp_continuousOn
      (hprof.const_mul _))
  have hfint : IntegrableOn f S₂ :=
    hfcont.integrableOn_compact isCompact_Icc
  have hf0 : ∀ a ∈ S₂, 0 ≤ f a := by
    intro a ha
    exact mul_nonneg (Real.rpow_nonneg (hs a ha).le _) (Real.exp_pos _).le
  exact setIntegral_mono_set hfint
    (ae_restrict_of_forall_mem measurableSet_Icc hf0)
    (.of_forall (fun a ha => hsub ha))

end
end SlowEquilibration.SphericalTAPPurePalmBandShrink
