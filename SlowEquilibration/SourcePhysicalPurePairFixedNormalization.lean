-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairFixedDeterminantSelectionLoss
public import SlowEquilibration.SourcePhysicalPurePairRetainedNormalization

/-! Pure retained value-window normalization, keeping the one-point
sphere-regularity cutoff fixed before ε and η. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_pure_actual_retained_normalization_fixed_regularity
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q ε η δMax M C : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η)
    (hδMax : 0 < δMax) (hC : 0 < C)
    (hMbound : |markE (FiniteMixture.pure p hp a ha) β x Q|+δMax+1 ≤ M)
    (hreg : ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
      ∀ h₀ : ℝ, |h₀| ≤ M →
        let μ := FiniteMixture.pure p hp a ha
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (valueConditionedLaw c u hu h₀).real
          {J | C < sourceSphereRegularity c J} ≤
          (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2)) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ δ C₂ : ℝ, 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧ 0 < C₂ ∧
      ∃ grid : ℕ, 1 ≤ grid ∧
        Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop,
          0 ≤ sourceSelectionWeightError C₂ μ Q G g grid n ∧
          sourceSelectionWeightError C₂ μ Q G g grid n < 1 ∧
          ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
            (1-sourceSelectionWeightError C₂ μ Q G g grid n)*
              sourceUnfilteredValueWindowMean (n+1) μ Q I ≤
              sourceRetainedValueWindowMean (n+1) μ Q I (g/2) C ε η E G ∧
            sourceRetainedValueWindowMean (n+1) μ Q I (g/2) C ε η E G ≤
              sourceUnfilteredValueWindowMean (n+1) μ Q I := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  obtain ⟨δ,C₂,hδ,hδG,hδMax',hC₂,grid,hgrid,hError,hloss⟩ :=
    source_pure_physical_posterior_determinant_selection_loss_fixed_regularity
      p hp a ha h hε hη hεη hδMax hC hMbound hreg
  refine ⟨δ,C₂,hδ,hδG,hδMax',hC₂,grid,hgrid,hError,?_⟩
  filter_upwards [hloss] with n hn
  refine ⟨sourceSelectionWeightError_nonneg _ _ _ _ _ _ _,hn.1,?_⟩
  intro I hI hsub
  apply source_value_retained_window_mean_bounds (n+1) (by omega) μ
    h.overlap_range.1 I hI _ C ε η _ _ _ hn.1.le
  intro u hu b hb
  exact hn.2 u hu b (hsub hb)

end
end SlowEquilibration.PairConditionalDeterminantMoments
