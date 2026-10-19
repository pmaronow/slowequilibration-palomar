-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairUnitLatitudeMesh
public import SlowEquilibration.SourcePhysicalPairPhysicalPosteriorRegularity
public import SlowEquilibration.SphericalParisiLatitudePosteriorTail
public import SlowEquilibration.LatitudeGroundMarkNeighborhood

/-! A genuine posterior estimate for the whole original overlap band.
The grid is chosen before the dimension; the actual fixed-latitude mean
and concentration theorems are applied at its finitely many points. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalCriticalLatitude
open SphericalParisiConditionedLatitudeCovariance SphericalParisiLatitudePosteriorGround
open SphericalParisiLatitudePosteriorTail LatitudeGroundTrial SphericalTAPCertificate
open TwoAtomStationarity
open scoped RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceBandFailureRate (μ:FiniteMixture) (Q G:ℝ) (k n:ℕ):ℝ:=
  (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2)+
    (k+1:ℕ)*Real.exp (-(n+1:ℕ)*(G/8)^2/(2*μ.xi Q))

theorem sourceBandHeight_failure_probability_of_mesh {n P k:ℕ}
    (hn:1 ≤ n) (hk:1 ≤ k) (c:Degree P→ℝ) {K ε η s H A B:ℝ}
    (hK:0 ≤ K) (hε:0<ε) (hη:0<η) (hab:ε ≤ 1-η)
    (hmesh:2*sourcePosteriorDerivativeConstant c K*Real.sqrt (((1-η)-ε)/(k:ℝ)) ≤ s)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (ν:Measure (Disorder (n+1) P)) [IsFiniteMeasure ν]
    (hreg:ν.real (sourcePosteriorOrderedRegularity (N:=n+1) (P:=P) K)ᶜ ≤ A)
    (hgrid:∀ i:Fin (k+1),ν.real {J|(n+1:ℕ)*H<sourceUnitLatitudeMaximum c u
      (sourceLatitudeIsometry u hu) (latitudeMeshPoint k ε (1-η) i) J} ≤ B) :
    ν.real {J|¬sourceOverlapBandHeight c ε η ((n+1:ℕ)*(H+s)) J u} ≤ A+(k+1:ℕ)*B:=by
  classical
  refine (measureReal_mono (sourceBandHeight_failure_subset_mesh hn hk c hK hε hη hab hmesh u hu)).trans ?_
  calc
    _ ≤ ν.real (sourcePosteriorOrderedRegularity (N:=n+1) (P:=P) K)ᶜ+
      ν.real (⋃ i:Fin (k+1),{J|(n+1:ℕ)*H<sourceUnitLatitudeMaximum c u
        (sourceLatitudeIsometry u hu) (latitudeMeshPoint k ε (1-η) i) J}):=
      measureReal_union_le _ _
    _ ≤ A+∑ i:Fin (k+1),ν.real {J|(n+1:ℕ)*H<sourceUnitLatitudeMaximum c u
        (sourceLatitudeIsometry u hu) (latitudeMeshPoint k ε (1-η) i) J}:=
      add_le_add hreg (measureReal_iUnion_fintype_le _)
    _ ≤ A+∑ _i:Fin (k+1),B:=add_le_add le_rfl (Finset.sum_le_sum (fun i _=>hgrid i))
    _ = _:=by simp

/-- The only box input here is the scalar trial inequality. The posterior
regularity, height tail, finite mesh, and full-band loss are all derived. -/
theorem source_mixed_physical_posterior_band_failure_of_trial_box (μ:FiniteMixture)
    {Q ε η E G L R δ y z:ℝ} (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree)
    (hε:0<ε) (hη:0<η) (hεη:ε ≤ 1-η) (hG:0<G) (hδ:0 ≤ δ)
    (hy:0<y) (hz:0<z)
    (htrial:∀ r ∈ Icc ε (1-η),∀ h ∈ Icc (E-δ) (E+δ),∀ k ∈ Icc L R,
      sourceConditionalMean μ Q h k r+
        functional (centeredFirst μ Q r) (centeredSecond μ Q r)
          (height y z r) (z/y) (location r) ≤ E-7*G/8) :
    ∃ K:ℝ,0<K ∧ ∃ grid:ℕ,1 ≤ grid ∧
      ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),
        ∀ h ∈ Icc (E-δ) (E+δ),∀ k ∈ Icc L R,
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h,k])).real
          {J|¬sourceOverlapBandHeight c ε η ((n+1:ℕ)*(E-G/2)) J u} ≤
          sourceBandFailureRate μ Q G grid n:=by
  let M:=|E|+δ+|L|+|R|+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨K,hK,hreg⟩:=source_mixed_physical_posterior_orderedRegularity μ hQ hnp hM
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨grid,hgrid,hmesh⟩:=source_radial_mesh_exists (a:=ε) (b:=1-η)
    (L:=sourcePosteriorDerivativeConstant c K) (s:=G/8) hεη
    (sourcePosteriorDerivativeConstant_pos c hK.le) (div_pos hG (by norm_num))
  have hpoints:∀ i:Fin (grid+1),∀ᶠ n:ℕ in atTop,
      ∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),
      ∀ h ∈ Icc (E-δ) (E+δ),∀ k ∈ Icc L R,
      (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h,k])).real
        {J|(n+1:ℕ)*(E-5*G/8)<sourceUnitLatitudeMaximum c u (sourceLatitudeIsometry u hu)
          (latitudeMeshPoint grid ε (1-η) i) J} ≤
        Real.exp (-(n+1:ℕ)*(G/8)^2/(2*μ.xi Q)):=by
    intro i
    let r:=latitudeMeshPoint grid ε (1-η) i
    have hrband:r ∈ Icc ε (1-η):=latitudeMeshPoint_mem hgrid hεη i
    have hr:r ∈ Ioo (0:ℝ) 1:=⟨hε.trans_le hrband.1,by linarith [hrband.2]⟩
    obtain ⟨hs,_he,hb⟩:=trial_endpoint hy hz hr
    have ht:=eventual_actual_mixed_latitude_trial_upper_tail μ hQ hnp hr
      (div_nonneg hz.le hy.le) hs hb (ε:=G/8) (t:=G/8)
      (div_pos hG (by norm_num)) (by positivity)
    filter_upwards [ht] with n hn
    intro u hu h hh k hk
    let ν:=mixedConditionedLaw c u hu (WithLp.toLp 2 ![h,k])
    let :IsProbabilityMeasure ν:=by unfold ν mixedConditionedLaw;infer_instance
    have H:=hn u hu (sourceLatitudeIsometry u hu) (sourceLatitudeIsometry_orthogonal u hu) h k
    dsimp only at H
    have hT:=htrial r hrband h hh k hk
    apply (measureReal_mono (μ:=ν) ?_).trans H
    intro J hJ
    change (n+1:ℕ)*(sourceConditionalMean μ Q h k r+
      functional (centeredFirst μ Q r) (centeredSecond μ Q r) (height y z r) (z/y) (location r)+G/8)+
        (n+1:ℕ)*(G/8) ≤ mixedLatitudeMaximum n μ Q r u (sourceLatitudeIsometry u hu) J
    change (n+1:ℕ)*(E-5*G/8) < mixedLatitudeMaximum n μ Q r u (sourceLatitudeIsometry u hu) J at hJ
    have hhT:=mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    nlinarith
  refine ⟨K,hK,grid,hgrid,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpoints,eventually_ge_atTop (1:ℕ)] with n hn hdim
  intro u hu h hh k hk
  dsimp only
  let ν:=mixedConditionedLaw c u hu (WithLp.toLp 2 ![h,k])
  let :IsProbabilityMeasure ν:=by unfold ν mixedConditionedLaw;infer_instance
  have hhM:|h| ≤ M:=by
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hh.1,hh.2,le_abs_self E,neg_le_abs E,abs_nonneg L,abs_nonneg R]
  have hkM:|k| ≤ M:=by
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hk.1,hk.2,le_abs_self R,neg_le_abs L,abs_nonneg E,abs_nonneg L,abs_nonneg R]
  have H:=sourceBandHeight_failure_probability_of_mesh hdim hgrid c hK.le hε hη hεη hmesh u hu ν
    (hreg n u hu h k hhM hkM) (fun i=>hn i u hu h hh k hk)
  have he:(E-5*G/8)+G/8=E-G/2:=by ring
  simpa only [he,sourceBandFailureRate] using H

/-- Actual certified mixed ground marks admit a uniform compact mark box
with an internally derived exponentially small whole-band failure. -/
theorem source_mixed_physical_posterior_band_failure (μ:FiniteMixture)
    {β x Q ε η a₀ b₀ δMax:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hε:0<ε) (hη:0<η) (hεη:ε<1-η)
    (ha:a₀ < markK μ β Q) (hb:markK μ β Q<b₀) (hδMax:0<δMax) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    ∃ L R δ:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧ Icc L R ⊆ Ioo a₀ b₀ ∧
      0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ ∃ K:ℝ,0<K ∧ ∃ grid:ℕ,1 ≤ grid ∧
      ∀ᶠ n:ℕ in atTop,∀ (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)),
        ∀ h₀ ∈ Icc (E-δ) (E+δ),∀ k₀ ∈ Icc L R,
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])).real
          {J|¬sourceOverlapBandHeight c ε η ((n+1:ℕ)*(E-G/2)) J u} ≤
          sourceBandFailureRate μ Q G grid n:=by
  dsimp only
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',htrial⟩:=
    exists_mixed_uniform_trial_gap μ h hnp hε hη hεη ha hb hδMax
  have hy:=markY_pos h.beta_pos h.overlap_range
  have hz:0 < markZ x Q:=div_pos (mul_pos h.weight_range.1 h.overlap_range.1)
    (sub_pos.mpr h.overlap_range.2)
  obtain ⟨hG,_⟩:=source_trial_gap μ h hnp hε hη hεη
  obtain ⟨K,hK,grid,hgrid,hall⟩:=source_mixed_physical_posterior_band_failure_of_trial_box
    μ h.overlap_range.1 hnp hε hη hεη.le hG hδ.le hy hz htrial
  exact ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',K,hK,grid,hgrid,hall⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
