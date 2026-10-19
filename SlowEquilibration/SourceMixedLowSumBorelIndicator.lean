-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedLowSumCorollary

@[expose] public section

/-! The source's half-open low-energy window and arbitrary Borel center
indicator follow from the stronger closed-window nonnegative marked bound. -/

namespace SlowEquilibration.SourceMixedLowSumBorelIndicator
noncomputable section
open MeasureTheory Set Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalBandSectionBridge
open SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumCorollary
open SphericalKacRiceGluing
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

/-- Monotonicity of the literal original critical-point sum in both score
window and nonnegative whole-field mark. -/
theorem actualScoreWindowCount_mono_window_mark
    {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K₁ K₂ : Set (EuclideanSpace ℝ (Fin 2))) (hK : K₁ ⊆ K₂)
    (ψ₁ ψ₂ : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (hψ : ∀ J u, ψ₁ J u ≤ ψ₂ J u)
    (J : Disorder (n+1) P) :
    actualScoreWindowCount n c K₁ ψ₁ J ≤
      actualScoreWindowCount n c K₂ ψ₂ J := by
  rw [actualScoreWindowCount_eq_indicator,
    actualScoreWindowCount_eq_indicator]
  unfold actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro u
  dsimp only
  by_cases h₁ : actualScore c J u ∈ K₁
  · have h₂ : actualScore c J u ∈ K₂ := hK h₁
    simpa only [h₁, h₂, ↓reduceIte] using hψ J u
  · by_cases h₂ : actualScore c J u ∈ K₂
    · simp only [h₁, h₂, ↓reduceIte]
      exact bot_le
    · simp only [h₁, h₂, ↓reduceIte]
      exact le_refl _

/-- The printed half-open energy interval and any Borel indicator of the
critical point's physical energy and center satisfy the same uniform
source Corollary 12.17 estimate. -/
theorem source_mixed_band_partition_below_window_sum_borel
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ L R ε b₀ C C₂ Cenv τ₀ a₀ : ℝ,
      0 < ε ∧ 0 < b₀ ∧ 0 < C ∧ 0 < C₂ ∧ 0 < Cenv ∧
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧
      markK μ β Q < R ∧
      Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀) ⊆ Ioo (0:ℝ) 1 ∧
      τ₀ = min ε ((β-(β*x+β)/2)/(4*C₂)) ∧
      a₀ = (β-(β*x+β)/2)/2 ∧ 0 < τ₀ ∧ 0 < a₀ ∧
      ∃ data : SourceMaximumFirstMomentConclusions μ β x Q L R,
        ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
          ∀ᶠ d : ℕ in atTop,
            ∀ b : ℝ, 0 < b → b ≤ b₀ →
            ∀ M : ℝ, 0 ≤ M →
            ∀ A : Set (ℝ × Vector (d+2)), MeasurableSet A →
              (∫⁻ J, actualScoreWindowCount (d+1)
                (centerCoefficients (mixtureCoefficients μ) Q)
                (physicalEnergyWindow (d+2)
                  (Ico (((d+2:ℕ):ℝ)*(markE μ β x Q-τ))
                    (data.center d-M)) (Ioo L R))
                (fun J u => if (field
                    (centerCoefficients (mixtureCoefficients μ) Q) J u,u) ∈ A
                  then sourceMixedBandMark d μ β (Real.sqrt Q) b J u
                  else 0) J
                ∂disorderLaw (d+2) μ.maxDegree) ≤
              ENNReal.ofReal
                (C*sourceCriticalBandScale (d+1) μ h.overlap_range β
                  (data.center d)*Real.exp (-a₀*M)) := by
  obtain ⟨L,R,ε,b₀,C,C₂,Cenv,τ₀,a₀,hε,hb₀,hC,hC₂,hCenv,
    hEdge,hLK,hKR,hband,hτdef,hadef,hτ,hapos,data,hMain⟩ :=
    source_mixed_band_partition_below_window_sum μ h hnp
  refine ⟨L,R,ε,b₀,C,C₂,Cenv,τ₀,a₀,hε,hb₀,hC,hC₂,hCenv,
    hEdge,hLK,hKR,hband,hτdef,hadef,hτ,hapos,data,?_⟩
  intro τ hτ hτbound
  filter_upwards [hMain τ hτ hτbound] with d hd
  intro b hb hbb M hM A _hA
  let lo := ((d+2:ℕ):ℝ)*(markE μ β x Q-τ)
  let hi := data.center d-M
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ψ := fun J : Disorder (d+2) μ.maxDegree =>
    fun u : Vector (d+2) =>
      if (field c J u,u) ∈ A then
        sourceMixedBandMark d μ β (Real.sqrt Q) b J u else 0
  have hK : physicalEnergyWindow (d+2) (Ico lo hi) (Ioo L R) ⊆
      physicalEnergyWindow (d+2) (Icc lo hi) (Ioo L R) := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.le⟩,hz.2⟩
  have hψ : ∀ J u, ψ J u ≤ sourceMixedBandMark d μ β (Real.sqrt Q) b J u := by
    intro J u
    dsimp [ψ]
    split_ifs
    · exact le_refl _
    · exact bot_le
  have hpoint (J : Disorder (d+2) μ.maxDegree) :
      actualScoreWindowCount (d+1) c
        (physicalEnergyWindow (d+2) (Ico lo hi) (Ioo L R)) ψ J ≤
      actualScoreWindowCount (d+1) c
        (physicalEnergyWindow (d+2) (Icc lo hi) (Ioo L R))
        (sourceMixedBandMark d μ β (Real.sqrt Q) b) J :=
    actualScoreWindowCount_mono_window_mark (d+1) c _ _ hK
      ψ _ hψ J
  exact (lintegral_mono hpoint).trans (hd b hb hbb M hM)

end
end SlowEquilibration.SourceMixedLowSumBorelIndicator
