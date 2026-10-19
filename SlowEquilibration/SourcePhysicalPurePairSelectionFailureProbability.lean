-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairBandFailureProbability
public import SlowEquilibration.SourcePhysicalPairSelectionFailureRates

/-! The original proper-pure near-ground selection event, with a genuine
value-only posterior and all three failure components internally proved. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalParisiPureLatitudeCovariance
open scoped RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Pure homogeneity and the actual contact equation give the exact
radial mark; the redundant radial observation is never conditioned. -/
theorem source_pure_markK_eq_degree_mul_markE (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {β x Q:ℝ} (h:Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    markK (FiniteMixture.pure p hp a ha) β Q=
      (p:ℝ)*markE (FiniteMixture.pure p hp a ha) β x Q:=by
  let μ:=FiniteMixture.pure p hp a ha
  have hpow1:Q^(p-1)*Q=Q^p:=by rw [←pow_succ,Nat.sub_add_cancel (show 1 ≤ p by omega)]
  have hpow2:Q^(p-2)*Q^2=Q^p:=by rw [←pow_add,Nat.sub_add_cancel hp]
  have hxi2:μ.xi2 Q=a*(p:ℝ)*((p:ℝ)-1)*Q^(p-2):=by
    simp only [μ,FiniteMixture.xi2,FiniteMixture.pure,Finsupp.support_single p ha.ne',
      Finset.sum_singleton,FiniteMixture.curvatureCoeff,Finsupp.single_eq_same]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have hA:markA μ Q=a*(p:ℝ)*Q^p:=by
    unfold markA
    rw [pure_xi1]
    calc
      _=a*(p:ℝ)*(Q^(p-1)*Q):=by ring
      _=_:=by rw [hpow1]
  have hB:markB μ Q=a*(p:ℝ)*((p:ℝ)-1)*Q^p:=by
    unfold markB
    rw [hxi2]
    calc
      _=a*(p:ℝ)*((p:ℝ)-1)*(Q^(p-2)*Q^2):=by ring
      _=_:=by rw [hpow2]
  have hY:=markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
    h.contact_value h.contact_derivative
  rw [hA] at hY
  have hy:=markY_pos h.beta_pos h.overlap_range
  change markK μ β Q=(p:ℝ)*markE μ β x Q
  unfold markK markE
  rw [hA,hB,FiniteMixture.pure_xi]
  field_simp [hy.ne']
  nlinarith [hY]

/-- Constants and the value-mark neighborhood are chosen before dimension.
Contact curvature supplies a true spectral margin; the whole original
band and actual covariant jet failures come from the physical posterior. -/
theorem source_pure_physical_posterior_selection_failure
    (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {β x Q ε η δMax:ℝ} (h:Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδMax:0<δMax) :
    let μ:=FiniteMixture.pure p hp a ha
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ δ C:ℝ,0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧
      ∃ grid:ℕ,1 ≤ grid ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (u:Vector (n+2)) (hu:‖u‖^2=(n+2:ℕ)),∀ h₀ ∈ Icc (E-δ) (E+δ),
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        (valueConditionedLaw c u hu h₀).real
          {J|¬sourceSelectionEvent c (g/2) C ε η E G J u} ≤
          sourceSelectionFailureRate μ Q G g grid n:=by
  dsimp only
  let μ:=FiniteMixture.pure p hp a ha
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  have hpR:(0:ℝ)<p:=by exact_mod_cast (show 0<p by omega)
  let δBound:=min δMax (g/(2*(p:ℝ)))
  have hδBound:0<δBound:=lt_min hδMax (div_pos hg (by positivity))
  obtain ⟨δ,hδ,hδG,hδB,K,hK,grid,hgrid,hband⟩:=
    source_pure_physical_posterior_band_failure p hp a ha h hε hη hεη hδBound
  have hδMax':δ ≤ δMax:=hδB.trans (min_le_left _ _)
  have hδp:(p:ℝ)*δ ≤ g/2:=by
    have H:=mul_le_mul_of_nonneg_left (hδB.trans (min_le_right _ _)) hpR.le
    have he:(p:ℝ)*(g/(2*(p:ℝ)))=g/2:=by field_simp
    simpa only [he] using H
  let M:=|E|+δ+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨C,hC,hreg⟩:=source_value_physical_posterior_sphere_regularity μ h.overlap_range.1 hM
  refine ⟨δ,C,hδ,hδG,hδMax',hC,grid,hgrid,?_⟩
  have hband':∀ᶠ n:ℕ in atTop,_:=(tendsto_add_atTop_nat 1).eventually hband
  filter_upwards [hband',source_pure_physical_posterior_hessian_margin p hp a ha h.overlap_range.1 hg]
    with n hbandN hhess
  intro u hu h₀ hh
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let ν:=valueConditionedLaw c u hu h₀
  let :IsProbabilityMeasure ν:=by unfold ν valueConditionedLaw;infer_instance
  have hhM:|h₀| ≤ M:=by
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hh.1,hh.2,le_abs_self E,neg_le_abs E]
  have hshift:2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h₀:=by
    have H:=mul_le_mul_of_nonneg_left hh.1 hpR.le
    change (p:ℝ)*(E-δ) ≤ (p:ℝ)*h₀ at H
    have he:=source_pure_markK_eq_degree_mul_markE p hp a ha h
    change markK μ β Q=(p:ℝ)*E at he
    dsimp only [g] at hδp hg ⊢
    nlinarith
  have H:=sourceSelectionEvent_failure_probability c (g/2) C ε η E G _ _ _ u ν
    (hhess u hu h₀ hshift) (hreg (n+1) u hu h₀ hhM) (hbandN u hu h₀ hh)
  refine H.trans_eq ?_
  change _=sourceSelectionFailureRate μ Q G g grid n
  unfold sourceBandFailureRate sourceSelectionFailureRate
  dsimp only [μ,G]
  push_cast
  ring

end
end SlowEquilibration.PairConditionalDeterminantMoments
