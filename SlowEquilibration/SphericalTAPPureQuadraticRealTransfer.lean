-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPurePalmFixedMarkUpper

@[expose] public section

/-! The real source quadratic-section estimate has the exact nonnegative
ENNReal form consumed by physical pure latitude coarea. -/

namespace SlowEquilibration.SphericalTAPPureQuadraticRealTransfer
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open GOEPhysicalPotential SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPPurePalmFixedMarkUpper
open scoped ENNReal
set_option autoImplicit false

theorem pure_quadratic_real_sections_to_band
    (d : ℕ) (hd : 1 ≤ d)
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q β e q b C : ℝ) (hb : 0 < b) (hC : 0 ≤ C)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hquad : let μ := FiniteMixture.pure p hp alpha halpha
      ∀ a ∈ Icc (q-b) (q+b),
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J))
        (pureLaw p hp alpha halpha Q u hu e) ∧
      (∫ J, intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J)
        ∂pureLaw p hp alpha halpha Q u hu e) ≤
      C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a))) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let B := fun a : ℝ => (Real.sqrt (1-a^2))^(d-1) *
      (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a)))
    Integrable (fun J => intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b))))
      (pureLaw p hp alpha halpha Q u hu e) ∧
    (∫ J, intrinsicDet μ Q u J *
      partitionOn β (field (mixtureCoefficients μ) J)
        (overlapRegion u (Icc (q-b) (q+b)))
      ∂pureLaw p hp alpha halpha Q u hu e) ≤
      (latitudeNormalization (d+1)).toReal *
        ∫ a in Icc (q-b) (q+b), B a ∂volume := by
  dsimp only at hquad ⊢
  apply pure_fixed_mark_physical_band_upper_of_quadratic_sections
    d hd p hp alpha halpha Q β e C hC u hu hb.le
    (by have hh := hband ⟨le_refl _,by linarith⟩; linarith [hh.1])
    (by have hh := hband ⟨by linarith,le_refl _⟩; linarith [hh.2])
  dsimp only
  intro a ha
  obtain ⟨hInt,hLe⟩ := hquad a ha
  let μ := FiniteMixture.pure p hp alpha halpha
  have hNonneg : ∀ J : Disorder (d+2) μ.maxDegree,
      0 ≤ intrinsicDet μ Q u J *
        partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
          (field (mixtureCoefficients μ) J) := by
    intro J
    apply mul_nonneg (abs_nonneg _)
    unfold partitionAgainst
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (.of_forall hNonneg)]
  exact ENNReal.ofReal_le_ofReal hLe

end
end SlowEquilibration.SphericalTAPPureQuadraticRealTransfer
