-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedDeterminantSelectionLoss
public import SlowEquilibration.SourcePhysicalPairRetainedNormalization

/-! Original retained mean comparison with a posterior sphere-regularity
constant selected from the fixed contact-data mark box. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_mixed_actual_retained_normalization_fixed_regularity
    (μ : FiniteMixture) {β x Q ε η δMax M C : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) (hδMax : 0 < δMax)
    (hC : 0 < C)
    (hMbound : |markE μ β x Q|+δMax+
      |2*Real.sqrt (Q^2*μ.xi2 Q)+
        (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2|+
      |markK μ β Q+1|+1 ≤ M)
    (hreg : ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
      ∀ h₀ k₀ : ℝ, |h₀| ≤ M → |k₀| ≤ M →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])).real
          {J | C < sourceSphereRegularity c J} ≤
          (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2)) :
    let E := markE μ β x Q
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
    let b₀ := markK μ β Q+1
    ∃ L R δ C₂ : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc L R ⊆ Ioo a₀ b₀ ∧ a₀ < L ∧ 0 < δ ∧ δ < G/4 ∧
      δ ≤ δMax ∧ 0 < C₂ ∧ ∃ grid : ℕ, 1 ≤ grid ∧
      Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        0 ≤ sourceSelectionWeightError C₂ μ Q G g grid n ∧
        sourceSelectionWeightError C₂ μ Q G g grid n < 1 ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
          K ⊆ {b | b 0 ∈ Icc (E-δ) (E+δ) ∧ b 1 ∈ Icc L R} →
          (1-sourceSelectionWeightError C₂ μ Q G g grid n)*
            sourceUnfilteredScoreWindowMean (n+1) μ Q K ≤
              sourceRetainedScoreWindowMean (n+1) μ Q K (g/2) C ε η E G ∧
          sourceRetainedScoreWindowMean (n+1) μ Q K (g/2) C ε η E G ≤
            sourceUnfilteredScoreWindowMean (n+1) μ Q K := by
  dsimp only
  obtain ⟨L,R,δ,C₂,hL,hR,hsub,hgapL,hδ,hδG,hδMax',hC₂,grid,hgrid,hlm,hloss⟩ :=
    source_mixed_physical_posterior_determinant_selection_loss_fixed_regularity
      μ h hnp hε hη hεη hδMax hC hMbound hreg
  refine ⟨L,R,δ,C₂,hL,hR,hsub,hgapL,hδ,hδG,hδMax',hC₂,grid,hgrid,hlm,?_⟩
  filter_upwards [hloss] with n hn
  refine ⟨sourceSelectionWeightError_nonneg _ _ _ _ _ _ _,hn.1,?_⟩
  intro K hK hsub
  apply source_mixed_retained_window_mean_bounds (n+1) (by omega) μ
    h.overlap_range.1 hnp K hK _ C ε η _ _ _ hn.1.le
  intro u hu b hb
  have hmarks := hsub hb
  have H := hn.2 u hu (b 0) hmarks.1 (b 1) hmarks.2
  have he : WithLp.toLp 2 ![b 0,b 1] = b := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  simpa only [he] using H

end
end SlowEquilibration.PairConditionalDeterminantMoments
