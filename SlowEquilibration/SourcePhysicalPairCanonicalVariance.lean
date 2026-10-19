-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedWindowSecondMoment
public import SlowEquilibration.SourcePhysicalPairRetainedWindowGeometry
public import SlowEquilibration.SourcePhysicalPairRetainedWindowLimits
public import SlowEquilibration.SourcePhysicalPairRetainedSquareCollar
public import SlowEquilibration.SourcePhysicalPairPosteriorSphereRegularity

/-! The actual retained count in the manuscript's logarithmically centered
physical energy window has the printed first-moment limit and a variance
bound with the same center, radial window, and selection event.  The pair
cutoff and regularity constant precede the overlap parameters, which in
turn precede the mesoscopic exponent and the fixed energy window. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The mixed-model retained count uses the genuine logarithmic centering
from the one-point Kac--Rice theorem.  Its variance is controlled by the
actual ordered-pair integral, including the negative-overlap simplex term.
No first-moment or pair-intensity conclusion is supplied as a premise. -/
theorem source_mixed_actual_retained_canonical_window_variance
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ C cut η ε L R : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 hd ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss (g/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧ sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
          ∃ D : ℝ, 0 < D ∧
          ∀ a b : ℝ, a < b →
            let G := gap μ Q (markY β Q) (markZ x Q) ε η
            let K n := physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)+a) (d.center (n+1)+b)) (Ioo L R)
            let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
              (g/2) C ε η E G
            Tendsto aN atTop
              (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) ∧
              ∀ᶠ n : ℕ in atTop,
                ProbabilityTheory.variance
                  (fun J => (sourceRetainedScoreWindowCount (n+2)
                    (centerCoefficients (mixtureCoefficients μ) Q) (K n)
                    (g/2) C ε η E G J).toReal)
                  (disorderLaw (n+3) μ.maxDegree) ≤
                D*sourcePrintedPairError α n*(aN n)^2+
                  (1+(1-ε)/(cut^2-ε))*aN n ∧
                MemLp
                  (fun J => (sourceRetainedScoreWindowCount (n+2)
                    (centerCoefficients (mixtureCoefficients μ) Q) (K n)
                    (g/2) C ε η E G J).toReal) 2
                  (disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
  let b₀ := markK μ β Q+1
  let M := |E|+δMax+|a₀|+|b₀|+1
  have hMbound : |markE μ β x Q|+δMax+
      |2*Real.sqrt (Q^2*μ.xi2 Q)+
        (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2|+
      |markK μ β Q+1|+1 ≤ M := le_refl _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨C,hC,hreg⟩ :=
    source_mixed_physical_posterior_sphere_regularity μ h.overlap_range.1 hnp hM
  obtain ⟨cut,hcut,hcutOne,hcutRad,hall⟩ :=
    source_mixed_actual_retained_fixed_window_second_moment
      μ h hnp hd hδMax hC hMbound hreg
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hκ : 0 < g/2 := div_pos hg (by norm_num)
  obtain ⟨η,ε,hη,hηCollar,hε,hεCut,hεη⟩ :=
    source_pair_cutoff_collar_parameters hκ hC hcut
  have hεOne : ε < cut^2 := by nlinarith [sq_pos_of_pos hcut]
  obtain ⟨L₀,R₀,ω,C₂,hL₀,hR₀,hsub,hgapL,hω,hωG,hωMax,hC₂,
      grid,hgrid,hError,hwindow⟩ := hall hη hε hεη hηCollar hεCut
  obtain ⟨ρ,hρ,hScore⟩ := source_contact_score_neighborhood μ h hnp
  let L := max L₀ (markK μ β Q-ρ)
  let R := min R₀ (markK μ β Q+ρ)
  let δ' := min ω ρ
  have hL : L < markK μ β Q := max_lt hL₀ (by linarith)
  have hR : markK μ β Q < R := lt_min hR₀ (by linarith)
  have hEdge : sourceRadialEdge μ Q < L := by
    dsimp [sourceRadialEdge]
    exact (lt_of_lt_of_le (by linarith :
      2*Real.sqrt (Q^2*μ.xi2 Q) < L₀) (le_max_left _ _))
  have hδ' : 0 < δ' := lt_min hω hρ
  have hBand : ∀ e ∈ Icc (markE μ β x Q-δ') (markE μ β x Q+δ'),
      ∀ k ∈ Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧
        sourceEnergySlope μ Q e k ≤ (β*x+β)/2 := by
    intro e he k hk
    apply hScore e k
    · apply abs_le.mpr
      have ht : δ' ≤ ρ := min_le_right _ _
      constructor <;> linarith [he.1,he.2]
    · apply abs_le.mpr
      have ht1 : markK μ β Q-ρ ≤ L := le_max_right _ _
      have ht2 : R ≤ markK μ β Q+ρ := min_le_right _ _
      constructor <;> linarith [hk.1,hk.2]
  obtain ⟨d⟩ := sourceMaximum_first_moments μ h hnp hEdge ⟨hL,hR⟩ hδ' hBand
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hvar⟩ := hwindow hα hHalf
  refine ⟨D,hD,?_⟩
  intro a b hab
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let K (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (d.center (n+1)+a) (d.center (n+1)+b)) (Ioo L R)
  let aN (n : ℕ) := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
    (g/2) C ε η E G
  have hcenter : ∀ᶠ n : ℕ in atTop,
      (n+3:ℕ)*(E-ω) ≤ d.center (n+1)+a ∧
        d.center (n+1)+b ≤ (n+3:ℕ)*(E+ω) :=
    (tendsto_add_atTop_nat 1).eventually
      (source_logarithmic_center_offset_bounds
        (mul_pos h.beta_pos h.weight_range.1)
        d.log_constant_pos.le hω d.center d.logarithmic_correction a b)
  have hK : ∀ n : ℕ, MeasurableSet (K n) := by
    intro n
    exact rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul ((n+3:ℕ):ℝ)))
      measurableSet_Ioo
  have hsubK : ∀ᶠ n : ℕ in atTop,
      K n ⊆ {z | z 0 ∈ Icc (E-ω) (E+ω) ∧ z 1 ∈ Icc L₀ R₀} := by
    filter_upwards [hcenter] with n hn
    intro z hz
    have H := source_physical_window_subset_coarse
      (n:=n+1) hn.1 hn.2 hz
    exact ⟨H.1,⟨(le_max_left _ _).trans H.2.1,
      H.2.2.trans (min_le_left _ _)⟩⟩
  have hBounds : ∀ᶠ n : ℕ in atTop,
      let bN := sourceUnfilteredScoreWindowMean (n+2) μ Q (K n)
      (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*bN ≤ aN n ∧
        aN n ≤ bN ∧
        ProbabilityTheory.variance
          (fun J => (sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q) (K n)
            (g/2) C ε η E G J).toReal)
          (disorderLaw (n+3) μ.maxDegree) ≤
            D*sourcePrintedPairError α n*(aN n)^2+
              (1+(1-ε)/(cut^2-ε))*aN n ∧
        MemLp
          (fun J => (sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q) (K n)
            (g/2) C ε η E G J).toReal) 2
          (disorderLaw (n+3) μ.maxDegree) := by
    filter_upwards [hvar,hsubK] with n hv hs
    have H := hv (K n) (hK n) hs
    exact ⟨H.1,H.2.1,H.2.2.2.1,H.2.2.2.2⟩
  have hall : Tendsto (fun n : ℕ =>
      sourceCriticalWindowMean (n+1) μ Q (Ioo L R)
        (d.center (n+1)+a) (d.center (n+1)+b)) atTop
      (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) :=
    (d.critical_window_limit a b hab).comp (tendsto_add_atTop_nat 1)
  have hError' : Tendsto
      (fun n : ℕ => sourceSelectionWeightError C₂ μ Q G g grid (n+1))
      atTop (𝓝 0) := hError.comp (tendsto_add_atTop_nat 1)
  have hOne : Tendsto (fun _n : ℕ => (1:ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hlo : Tendsto (fun n : ℕ =>
      (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*
      sourceCriticalWindowMean (n+1) μ Q (Ioo L R)
        (d.center (n+1)+a) (d.center (n+1)+b)) atTop
      (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) := by
    simpa only [sub_zero,one_mul,Function.comp_def] using
      (hOne.sub hError').mul hall
  constructor
  · apply hlo.squeeze' hall
    · filter_upwards [hBounds] with n hn
      have H := hn.1
      rw [sourceUnfilteredScoreWindowMean_physical (n+1)] at H
      exact H
    · filter_upwards [hBounds] with n hn
      have H := hn.2.1
      rw [sourceUnfilteredScoreWindowMean_physical (n+1)] at H
      exact H
  · filter_upwards [hBounds] with n hn
    exact hn.2.2

end
end SlowEquilibration.PairConditionalDeterminantMoments
