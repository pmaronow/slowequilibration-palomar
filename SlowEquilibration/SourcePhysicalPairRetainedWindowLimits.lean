-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedNormalization
public import SlowEquilibration.SourcePhysicalPairRetainedWindowGeometry

/-! Actual retained fixed-window means, with the original genuine
centering chosen internally. Neither its first-moment limit nor the
selection loss is assumed in the source endpoint. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open SphericalSequentialRegression LatitudeGroundTrial TwoAtomStationarity
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceRetainedPhysicalWindowMean (n:ℕ) (μ:FiniteMixture) (Q:ℝ) (U:Set ℝ)
    (l r κ C ε η E G:ℝ):ℝ:=
  sourceRetainedScoreWindowMean (n+1) μ Q (physicalEnergyWindow (n+2) (Icc l r) U) κ C ε η E G

lemma sourceUnfilteredScoreWindowMean_physical (n:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (U:Set ℝ) (l r:ℝ) :
    sourceUnfilteredScoreWindowMean (n+1) μ Q (physicalEnergyWindow (n+2) (Icc l r) U)=
      sourceCriticalWindowMean n μ Q U l r:=by
  rw [sourceCriticalWindowMean,sourceCriticalWindowMass_def]
  rfl

/-- Constants, radial interval, and actual normalized centering are
chosen before all fixed windows. The limit is the printed source mean. -/
theorem source_mixed_actual_retained_fixed_window_limits (μ:FiniteMixture)
    {β x Q ε η δMax:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hε:0<ε) (hη:0<η) (hεη:ε<1-η)
    (hδMax:0<δMax) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R C:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧ sourceRadialEdge μ Q<L ∧ 0<C ∧
      ∃ d:SourceMaximumFirstMomentConclusions μ β x Q L R,
      ∀ a b:ℝ,a<b → Tendsto
        (fun n:ℕ=>sourceRetainedPhysicalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b)
          (g/2) C ε η E G) atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))):=by
  dsimp only
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  obtain ⟨L₀,R₀,δ,C,C₂,hL₀,hR₀,hgapL,hδ,_hδG,_hδMax,hC,_hC₂,grid,_hgrid,herror,hnorm⟩:=
    source_mixed_actual_retained_normalization μ h hnp hε hη hεη hδMax
  obtain ⟨ρ,hρ,hScore⟩:=source_contact_score_neighborhood μ h hnp
  let L:=max L₀ (markK μ β Q-ρ)
  let R:=min R₀ (markK μ β Q+ρ)
  let δ':=min δ ρ
  have hL:L < markK μ β Q:=max_lt hL₀ (by linarith)
  have hR:markK μ β Q<R:=lt_min hR₀ (by linarith)
  have hEdge:sourceRadialEdge μ Q<L:=by
    dsimp [sourceRadialEdge]
    exact (lt_of_lt_of_le (by linarith : 2*Real.sqrt (Q^2*μ.xi2 Q)<L₀) (le_max_left _ _))
  have hδ':0<δ':=lt_min hδ hρ
  have hBand:∀ e ∈ Icc (markE μ β x Q-δ') (markE μ β x Q+δ'),∀ k ∈ Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2:=by
    intro e he k hk
    apply hScore e k
    · apply abs_le.mpr
      have ht:δ' ≤ ρ:=min_le_right _ _
      constructor <;> linarith [he.1,he.2]
    · apply abs_le.mpr
      have ht1:markK μ β Q-ρ ≤ L:=le_max_right _ _
      have ht2:R ≤ markK μ β Q+ρ:=min_le_right _ _
      constructor <;> linarith [hk.1,hk.2]
  obtain ⟨d⟩:=sourceMaximum_first_moments μ h hnp hEdge ⟨hL,hR⟩ hδ' hBand
  refine ⟨L,R,C,hL,hR,hEdge,hC,d,?_⟩
  intro a b hab
  have hall:=d.critical_window_limit a b hab
  have hOne:Tendsto (fun _n:ℕ=>(1:ℝ)) atTop (𝓝 1):=tendsto_const_nhds
  have hlo: Tendsto (fun n:ℕ=>(1-sourceSelectionWeightError C₂ μ Q G g grid n)*
      sourceCriticalWindowMean n μ Q (Ioo L R) (d.center n+a) (d.center n+b)) atTop
        (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))):=by
    simpa only [sub_zero,one_mul] using (hOne.sub herror).mul hall
  apply hlo.squeeze' hall
  · filter_upwards [hnorm,source_logarithmic_center_offset_bounds
      (mul_pos h.beta_pos h.weight_range.1) d.log_constant_pos.le hδ d.center d.logarithmic_correction a b]
      with n hn hcenter
    let K:=physicalEnergyWindow (n+2) (Icc (d.center n+a) (d.center n+b)) (Ioo L R)
    have hK:MeasurableSet K:=rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul ((n+2:ℕ):ℝ))) measurableSet_Ioo
    have hsub:K ⊆ {z:EuclideanSpace ℝ (Fin 2)|z 0 ∈ Icc (E-δ) (E+δ) ∧ z 1 ∈ Icc L₀ R₀}:=by
      intro z hz
      have H:=source_physical_window_subset_coarse hcenter.1 hcenter.2 hz
      refine ⟨H.1,?_⟩
      exact ⟨(le_max_left _ _).trans H.2.1,H.2.2.trans (min_le_left _ _)⟩
    have H:=(hn.2.2 K hK hsub).1
    rw [sourceUnfilteredScoreWindowMean_physical] at H
    exact H
  · filter_upwards [hnorm,source_logarithmic_center_offset_bounds
      (mul_pos h.beta_pos h.weight_range.1) d.log_constant_pos.le hδ d.center d.logarithmic_correction a b]
      with n hn hcenter
    let K:=physicalEnergyWindow (n+2) (Icc (d.center n+a) (d.center n+b)) (Ioo L R)
    have hK:MeasurableSet K:=rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul ((n+2:ℕ):ℝ))) measurableSet_Ioo
    have hsub:K ⊆ {z:EuclideanSpace ℝ (Fin 2)|z 0 ∈ Icc (E-δ) (E+δ) ∧ z 1 ∈ Icc L₀ R₀}:=by
      intro z hz
      have H:=source_physical_window_subset_coarse hcenter.1 hcenter.2 hz
      refine ⟨H.1,?_⟩
      exact ⟨(le_max_left _ _).trans H.2.1,H.2.2.trans (min_le_left _ _)⟩
    have H:=(hn.2.2 K hK hsub).2
    rw [sourceUnfilteredScoreWindowMean_physical] at H
    exact H

end
end SlowEquilibration.PairConditionalDeterminantMoments
