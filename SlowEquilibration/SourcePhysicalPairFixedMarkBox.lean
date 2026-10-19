-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairBandFailureProbability
public import SlowEquilibration.SourcePhysicalPairCountBounds
public import SlowEquilibration.SourcePhysicalPairPosteriorSphereRegularity

/-! A contact-data mark box fixed before selecting the positive-overlap
exclusion parameters.  This is the order needed to choose the regularity
constant and pair-intensity cutoff before the collar and separation widths. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Filter
open SphericalModel SphericalTAPCertificate TwoAtomStationarity LatitudeGroundTrial
open SphericalGaussianJet SphericalMarkedWindows SphericalPairCountGluing
open SphericalPairChartKacRice
open scoped ENNReal Topology
open Set
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem source_mixed_fixed_mark_box_before_overlap_parameters (μ : FiniteMixture)
    {β x Q δMax : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) (hδMax : 0 < δMax) :
    let E := markE μ β x Q
    let g := (markK μ β Q - 2*Real.sqrt (Q^2*μ.xi2 Q))/2
    let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
    let b₀ := markK μ β Q+1
    ∃ M : ℝ, |E|+δMax+|a₀|+|b₀|+1 ≤ M ∧ 0 ≤ M ∧
      ∀ {ε η : ℝ}, 0 < ε → 0 < η → ε < 1-η →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ L R δ : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
          Icc L R ⊆ Ioo a₀ b₀ ∧ 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧
          ∀ h₀ ∈ Icc (E-δ) (E+δ), ∀ k₀ ∈ Icc L R,
            |h₀| ≤ M ∧ |k₀| ≤ M := by
  dsimp only
  let E := markE μ β x Q
  let g := (markK μ β Q - 2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
  let b₀ := markK μ β Q+1
  let M := |E|+δMax+|a₀|+|b₀|+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have ha : a₀ < markK μ β Q := by dsimp [a₀,g]; linarith
  have hb : markK μ β Q < b₀ := by dsimp [b₀]; linarith
  refine ⟨M,?_,hM,?_⟩
  · change M ≤ M
    exact (le_refl M)
  intro ε η hε hη hεη
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',_⟩ :=
    source_mixed_physical_posterior_band_failure μ h hnp hε hη hεη ha hb hδMax
  refine ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',?_⟩
  intro h₀ hh k₀ hk
  have hk' := hsub hk
  constructor
  · apply abs_le.mpr
    constructor <;> dsimp [M] <;>
      linarith [hh.1,hh.2,le_abs_self E,neg_le_abs E,abs_nonneg a₀,abs_nonneg b₀]
  · apply abs_le.mpr
    constructor <;> dsimp [M] <;>
      linarith [hk'.1,hk'.2,le_abs_self b₀,neg_le_abs a₀,
        abs_nonneg E,abs_nonneg a₀,abs_nonneg b₀]

/-- The regularity cutoff and actual integrated pair cutoff are selected
from that same fixed mark box before ε or η.  Both probabilistic estimates
are the already proved original posterior/Kac--Rice estimates. -/
theorem source_mixed_fixed_pair_constants_before_overlap_parameters (μ : FiniteMixture)
    {β x Q δMax α : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) (hd : 4 ≤ μ.minDegree)
    (hδMax : 0 < δMax) (hα : 1/4 < α) :
    let E := markE μ β x Q
    let g := (markK μ β Q - 2*Real.sqrt (Q^2*μ.xi2 Q))/2
    let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
    let b₀ := markK μ β Q+1
    ∃ M C cut Cpair : ℝ,
      |E|+δMax+|a₀|+|b₀|+1 ≤ M ∧ 0 ≤ M ∧ 0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 hd ∧ 0 < Cpair ∧
      (∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
        ∀ h₀ k₀ : ℝ, |h₀| ≤ M → |k₀| ≤ M →
          let c := centerCoefficients (mixtureCoefficients μ) Q
          (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])).real
            {J | C < sourceSphereRegularity c J} ≤
            (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2)) ∧
      (∀ᶠ n : ℕ in atTop, ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
        (∀ z ∈ K, |z 0| ≤ M ∧ |z 1| ≤ M ∧
          2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1) →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (∫⁻ J, actualSpherePairCount (n+2) c (pairRadius μ h.overlap_range.1 hd)
          (actualMixedPairWindowMark c K cut (fun _ _ => 1)) J
          ∂disorderLaw (n+3) μ.maxDegree) ≤
          ENNReal.ofReal (1+Cpair*(((n+3:ℕ):ℝ)^(1-4*α)+
            1/Real.sqrt (n+3:ℕ)+Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4))) *
          (∫⁻ J, actualScoreWindowCount (n+2) c K (fun _ _ => 1) J
            ∂disorderLaw (n+3) μ.maxDegree)^2) ∧
      (∀ {ε η : ℝ}, 0 < ε → 0 < η → ε < 1-η →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ L R δ : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
          Icc L R ⊆ Ioo a₀ b₀ ∧ 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧
          ∀ h₀ ∈ Icc (E-δ) (E+δ), ∀ k₀ ∈ Icc L R,
            |h₀| ≤ M ∧ |k₀| ≤ M) := by
  dsimp only
  let g := (markK μ β Q - 2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  obtain ⟨M,hMbound,hM,hbox⟩ :=
    source_mixed_fixed_mark_box_before_overlap_parameters μ h hnp hδMax
  obtain ⟨C,hC,hreg⟩ :=
    source_mixed_physical_posterior_sphere_regularity μ h.overlap_range.1 hnp hM
  obtain ⟨cut,Cpair,hcut,hcutOne,hcutRadius,hCpair,hpair⟩ :=
    source_mixed_actual_subcritical_pair_count_bound μ h.overlap_range.1 hnp hd hM hg hα
  exact ⟨M,C,cut,Cpair,hMbound,hM,hC,hcut,hcutOne,hcutRadius,hCpair,hreg,hpair,hbox⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
