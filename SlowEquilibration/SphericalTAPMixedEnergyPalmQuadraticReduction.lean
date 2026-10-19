-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedEnergyPalmCoareaComplete
public import SlowEquilibration.SphericalTAPMixedPalmFixedMarkUpper
public import SlowEquilibration.UnrestrictedConditionalMeans

@[expose] public section

/-! Reduction of the exact original mixed energy-Palm band expectation to
the printed determinant--quadratic latitude section lemma. Every geometric,
measurability, Fubini, denominator, and radial-integrability step is proved. -/

namespace SlowEquilibration.SphericalTAPMixedEnergyPalmQuadraticReduction
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open GOEPhysicalPotential
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedPhysicalRadialLower
open SphericalTAPMixedBandExponent
open SphericalTAPMixedEnergyPalmCoareaComplete
open SphericalTAPMixedPalmFixedMarkUpper
open UnrestrictedConditionalMeans
set_option autoImplicit false

theorem mixed_energy_palm_upper_of_quadratic_sections
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β e L R q b C : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R) (hb : 0 < b) (hC : 0 ≤ C)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (0:ℝ) 1)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (hquad : ∀ k ∈ Ioo L R, ∀ a ∈ Icc (q-b) (q+b),
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      ENNReal.ofReal (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a))) :
    sourceMixedEnergyPalmBandExpectation d μ Q β e L R q b u hu ≤
      C*(latitudeNormalization (d+1)).toReal *
        (sourceMixedJointLaplace d μ β Q e L R q b /
          sourceMixedRadialLaplace d μ Q e L R) := by
  have hbelow : -1 < q-b := by
    have hh := hband (show q-b ∈ Icc (q-b) (q+b) from
      ⟨le_refl _,by linarith⟩)
    linarith [hh.1]
  have habove : q+b < 1 :=
    (hband (show q+b ∈ Icc (q-b) (q+b) from
      ⟨by linarith,le_refl _⟩)).2
  have hmark (k : ℝ) (hk : k ∈ Ioo L R) :
      (∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (q-b) (q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      C*(latitudeNormalization (d+1)).toReal *
        (∫ a in Icc (q-b) (q+b),
          (Real.sqrt (1-a^2))^(d-1) *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) := by
    obtain ⟨_,hNum⟩ :=
      mixed_fixed_mark_physical_band_upper_of_quadratic_sections
        d hd μ Q β e k C hC u hu hb.le hbelow habove (hquad k hk)
    obtain ⟨_,hDenEq,hDenPos⟩ :=
      mixed_conditional_mean μ hQ hnp u hu (scorePairEquiv (e,k))
    have hscore : (scorePairEquiv (e,k)) 1 = k := by
      simp [scorePairEquiv_apply]
    rw [hscore] at hDenEq
    have hB :
      (∫ a in Icc (q-b) (q+b),
        (Real.sqrt (1-a^2))^(d-1) *
          (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) ∂volume) =
      C*physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        (∫ a in Icc (q-b) (q+b),
          (Real.sqrt (1-a^2))^(d-1) *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with a
      ring
    rw [hDenEq]
    apply (div_le_iff₀ (by simpa [hDenEq] using hDenPos)).2
    calc
      _ ≤ (latitudeNormalization (d+1)).toReal *
          (∫ a in Icc (q-b) (q+b),
            (Real.sqrt (1-a^2))^(d-1) *
              (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
                Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) ∂volume) := hNum
      _ = (C*(latitudeNormalization (d+1)).toReal *
          (∫ a in Icc (q-b) (q+b),
            (Real.sqrt (1-a^2))^(d-1) *
              Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume)) *
          physicalMean d (d+2) (Q^2*μ.xi2 Q) k := by rw [hB]; ring
  exact mixed_energy_palm_coarea_ratio_of_fixed_marks
    d hd μ hQ β e L R q b C hEdge hLR hb hC hband u hu hmark

end
end SlowEquilibration.SphericalTAPMixedEnergyPalmQuadraticReduction
