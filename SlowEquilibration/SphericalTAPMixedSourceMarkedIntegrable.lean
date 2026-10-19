-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceCommonPalmEnvelope
public import SlowEquilibration.SphericalTAPMixedPalmRatioIntegrable
public import SlowEquilibration.SphericalTAPMixedPalmFixedMarkUpper
public import SlowEquilibration.UnrestrictedConditionalMeans

/-! The source quadratic latitude estimate makes the literal fixed-mark
determinant-weighted band integrable, and its physical Palm ratio integrable
under the compact all-critical radial law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTAPMixedSourceMarkedIntegrable

open Set MeasureTheory Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalAnalyticNeighborhood
open SphericalQuadraticLatitudeJetCovariance
open SphericalTAPMixedPalmFixedMarkUpper SphericalTAPMixedPalmRatioIntegrable
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedBandExponent GOEPhysicalPotential
open UnrestrictedConditionalMeans
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem source_mixed_fixed_mark_and_radial_ratio_integrable
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R) :
    ∃ b₀ C : ℝ, 0 < b₀ ∧ 0 < C ∧
      Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀) ⊆ Ioo (0:ℝ) 1 ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ e : ℝ,
        ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
          (∀ k ∈ Ioo L R,
            Integrable (fun J => intrinsicDet μ Q u J *
              partitionOn β (field (mixtureCoefficients μ) J)
                (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))))
              (mixedLaw μ Q u hu (scorePairEquiv (e,k))) ∧
            (∫ J, intrinsicDet μ Q u J *
              partitionOn β (field (mixtureCoefficients μ) J)
                (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)))
              ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
              (∫ J, intrinsicDet μ Q u J
                ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
              C*(latitudeNormalization (d+1)).toReal *
                (∫ a in Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
                  (Real.sqrt (1-a^2))^(d-1) *
                    Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume)) ∧
          Integrable (fun k : ℝ =>
            (∫ J, intrinsicDet μ Q u J *
              partitionOn β (field (mixtureCoefficients μ) J)
                (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)))
              ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
              (∫ J, intrinsicDet μ Q u J
                ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))))
            (sourceAllCriticalRadialLaw d μ Q e L R) := by
  let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
  let g := (L-edge)/2
  have hg : 0 < g := by dsimp [g,edge]; linarith
  obtain ⟨bq,C,hbq,hbqQ,hC,hQuad⟩ :=
    source_mb_quadratic_physicalMixedPalm μ hnp h hg
  obtain ⟨bm,ε₂,hbm,hbmQ,hε₂,hε₂one,hbandm,hbankm⟩ :=
    quadratic_fixed_band_margin μ h
  let b₀ := min bq bm
  have hb₀ : 0 < b₀ := lt_min hbq hbm
  have hband₀ : Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀) ⊆ Ioo (0:ℝ) 1 := by
    intro a ha
    apply hbandm
    have hh := min_le_right bq bm
    exact ⟨by dsimp [b₀] at *; linarith [ha.1],
      by dsimp [b₀] at *; linarith [ha.2]⟩
  refine ⟨b₀,C,hb₀,hC,hband₀,?_⟩
  filter_upwards [hQuad,Filter.eventually_ge_atTop 1] with d hqd hd
  intro b hb hbb e u hu
  have hband : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 := by
    intro a ha
    apply hband₀
    exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
  have hbelow : -1 < Real.sqrt Q-b := by
    have hh := hband (show Real.sqrt Q-b ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b)
      from ⟨le_refl _,by linarith⟩)
    linarith [hh.1]
  have habove : Real.sqrt Q+b < 1 :=
    (hband (show Real.sqrt Q+b ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b)
      from ⟨by linarith,le_refl _⟩)).2
  have hquadE (k : ℝ) (hk : k ∈ Ioo L R)
      (a : ℝ) (ha : a ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) :
      (∫⁻ J, ENNReal.ofReal
        (intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      ENNReal.ofReal (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) := by
    have hkmark : edge+g ≤ (scorePairEquiv (e,k)) 1 := by
      simp only [scorePairEquiv_apply]
      dsimp [edge,g]
      linarith [hk.1]
    obtain ⟨hInt,hLe⟩ := hqd u hu (scorePairEquiv (e,k)) hkmark
      b hb (hbb.trans (min_le_left bq bm)) a ha
    have hNonneg : ∀ J : Disorder (d+2) μ.maxDegree,
        0 ≤ intrinsicDet μ Q u J *
          partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
            (field (mixtureCoefficients μ) J) := by
      intro J
      apply mul_nonneg (abs_nonneg _)
      unfold partitionAgainst
      exact integral_nonneg (fun _ => (Real.exp_pos _).le)
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (.of_forall hNonneg)]
    simpa [scorePairEquiv_apply] using ENNReal.ofReal_le_ofReal hLe
  have hmark (k : ℝ) (hk : k ∈ Ioo L R) :
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))))
        (mixedLaw μ Q u hu (scorePairEquiv (e,k))) ∧
      (∫ J, intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)))
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
      C*(latitudeNormalization (d+1)).toReal *
        (∫ a in Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
          (Real.sqrt (1-a^2))^(d-1) *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) := by
    obtain ⟨hInt,hNum⟩ :=
      mixed_fixed_mark_physical_band_upper_of_quadratic_sections
        d hd μ Q β e k C hC.le u hu hb.le hbelow habove (hquadE k hk)
    obtain ⟨_,hDenEq,hDenPos⟩ :=
      mixed_conditional_mean μ h.overlap_range.1 hnp u hu (scorePairEquiv (e,k))
    have hscore : (scorePairEquiv (e,k)) 1 = k := by simp [scorePairEquiv_apply]
    rw [hscore] at hDenEq
    have hB :
      (∫ a in Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
        (Real.sqrt (1-a^2))^(d-1) *
          (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) ∂volume) =
      C*physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
        (∫ a in Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
          (Real.sqrt (1-a^2))^(d-1) *
            Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with a
      ring
    refine ⟨hInt,?_⟩
    rw [hDenEq]
    apply (div_le_iff₀ (by simpa [hDenEq] using hDenPos)).2
    calc
      _ ≤ (latitudeNormalization (d+1)).toReal *
          (∫ a in Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            (Real.sqrt (1-a^2))^(d-1) *
              (C * physicalMean d (d+2) (Q^2*μ.xi2 Q) k *
                Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a)) ∂volume) := hNum
      _ = (C*(latitudeNormalization (d+1)).toReal *
          (∫ a in Icc (Real.sqrt Q-b) (Real.sqrt Q+b),
            (Real.sqrt (1-a^2))^(d-1) *
              Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume)) *
          physicalMean d (d+2) (Q^2*μ.xi2 Q) k := by rw [hB]; ring
  refine ⟨hmark,?_⟩
  apply mixed_markPalm_band_ratio_integrable_of_bound
    d μ h.overlap_range.1 β e L R (Real.sqrt Q) b C hEdge hLR hC.le u hu
  intro k hk
  exact (hmark k hk).2

end SlowEquilibration.SphericalTAPMixedSourceMarkedIntegrable
