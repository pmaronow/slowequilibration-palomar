-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPurePalmCoareaReal
public import SlowEquilibration.SphericalTAPPureQuadraticSectionBridge

@[expose] public section

/-! Source-faithful fixed-mark reduction of the physical Palm band to the
printed determinant–quadratic latitude section estimate. -/

namespace SlowEquilibration.SphericalTAPPurePalmFixedMarkUpper
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPPurePalmCoareaReal
open SphericalTAPPureQuadraticSectionBridge GOEPhysicalPotential
set_option autoImplicit false

/-- The actual physical determinant-weighted band expectation is bounded
by the manuscript's annealed latitude integral, and is integrable, once the
printed quadratic-correlation estimate holds at each latitude. -/
theorem pure_fixed_mark_physical_band_upper_of_quadratic_sections
    (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha)
    (Q β e C : ℝ) (hC : 0 ≤ C)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    {q b : ℝ} (hb : 0 ≤ b) (hbelow : -1 < q-b) (habove : q+b < 1)
    (hquad : let μ := FiniteMixture.pure p hp alpha halpha
      ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J))
        ∂pureLaw p hp alpha halpha Q u hu e) ≤
      ENNReal.ofReal (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*(β*e*(a/Real.sqrt Q)^p+β^2/2*sourcePureLatitudeVariance p alpha a)))) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let B := fun a : ℝ => (Real.sqrt (1-a^2))^(d-1) *
      (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
        Real.exp (((d+2:ℕ):ℝ)*(β*e*(a/Real.sqrt Q)^p+β^2/2*sourcePureLatitudeVariance p alpha a)))
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
  let μ := FiniteMixture.pure p hp alpha halpha
  let B := fun a : ℝ => (Real.sqrt (1-a^2))^(d-1) *
    (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) *
      Real.exp (((d+2:ℕ):ℝ)*(β*e*(a/Real.sqrt Q)^p+β^2/2*sourcePureLatitudeVariance p alpha a)))
  have hBcont : Continuous B := by
    dsimp [B,sourcePureLatitudeVariance]
    fun_prop
  have hBint : IntegrableOn B (Icc (q-b) (q+b)) :=
    hBcont.continuousOn.integrableOn_compact isCompact_Icc
  have hdN : 0 ≤ physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e) := by
    unfold physicalMean
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hB0 : ∀ a ∈ Icc (q-b) (q+b), 0 ≤ B a := by
    intro a _
    dsimp [B]
    positivity
  have hsection : ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          latitudeDensityPartition (d+1) β
            (field (mixtureCoefficients μ) J) u a)
        ∂pureLaw p hp alpha halpha Q u hu e) ≤
      ENNReal.ofReal (B a) := by
    intro a ha
    exact pure_quadratic_section_to_coarea_density
      d p hp alpha halpha Q β e a C u hu (hquad a ha)
  exact pure_weighted_band_integral_le_sections
    d hd p hp alpha halpha Q β e u hu hb hbelow habove
    B hBint hB0 hsection

end
end SlowEquilibration.SphericalTAPPurePalmFixedMarkUpper
