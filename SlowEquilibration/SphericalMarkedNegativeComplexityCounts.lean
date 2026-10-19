-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedGlobalLoss
public import SlowEquilibration.SphericalMarkedWholeLineIntensityBounds
public import SlowEquilibration.SphericalMarkedMaximumEvents
public import SlowEquilibration.QuadraticPlaneEnvelopes

/-! An actual negative marked complexity gap implies exponential decay of
the original-disorder critical count. Both compact shifts and unbounded score
tails are integrated using genuine one-point intensity bounds. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel SphericalGaussianJet
open SphericalSequentialRegression QuadraticPlaneEnvelopes StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

irreducible_def sourceMarkedOriginalCountMass (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) : ℝ≥0∞ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  ∫⁻ J,actualScoreWindowCount (n+1) c K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree

theorem sourceMarkedOriginalCountMass_finite (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (K : Set (EuclideanSpace ℝ (Fin 2))) :
    sourceMarkedOriginalCountMass n μ Q K < ⊤ := by
  rw [sourceMarkedOriginalCountMass_def]
  exact bounded_scoreWindowCount_lintegral_lt_top (n+1) (by omega) μ hQ K _ 1 (by simp)
    (fun _ _ => le_rfl)

theorem sourceMarkedOriginalCountMass_eq_plane_integral (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    sourceMarkedOriginalCountMass n μ Q K=
      ∫⁻ z in scorePairEquiv ⁻¹' K,mixedCriticalIntensity n μ Q (scorePairEquiv z) ∂planeVolume := by
  rw [sourceMarkedOriginalCountMass_def,actual_mixed_count_intensity n μ hQ hnp K hK]
  exact (scorePairEquiv_measurePreserving.setLIntegral_comp_preimage_emb
    scorePairEquiv.measurableEmbedding _ K).symm

/-- The abstract gap in this helper is a pointwise bound on the actual
complexity, not a desired count or probability estimate. Source applications
below derive that gap from the genuine source contact and eigenvalue. -/
theorem sourceMarkedOriginalCountMass_exponential_of_gap (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ z ∈ K,markedComplexity μ Q z ≤ -γ) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ n : ℕ in atTop,
      sourceMarkedOriginalCountMass n μ Q K ≤ ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ))) := by
  let S := scorePairEquiv ⁻¹' K
  let theta := fun z : ℝ × ℝ => sourceRadialProfile μ Q z.1 z.2
  let R := fun n : ℕ => fun z : ℝ × ℝ => mixedCriticalIntensity n μ Q (scorePairEquiv z)
  let κ := sourceMarkedLeastCurvature μ Q
  have hκ : 0 < κ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  have hcoerc : ∀ z : ℝ × ℝ,theta z ≤ sourceMarkedCoercivityConstant μ β x Q-
      κ/8*(z.1^2+z.2^2) := fun z => sourceMarkedComplexity_global_coercivity μ h hnp z.1 z.2
  have hnegative : ∀ z ∈ S,theta z ≤ -γ := fun z hz => hgap (scorePairEquiv z) hz
  obtain ⟨η,ρ,hη,hρ,hTheta⟩ := gap_and_coercivity_envelope hγ
    (sourceMarkedCoercivityConstant_pos μ h hnp) (show 0 < κ/8 by positivity)
      hnegative hcoerc
  obtain ⟨B1,hB1,hSharp⟩ := sourceMixedIntensity_compact_upper μ h.overlap_range.1 hnp
  obtain ⟨B2,hB2,hCrude⟩ := sourceMixedIntensity_crude_upper μ h.overlap_range.1 hnp
  have hSharp' : ∀ {Z eps : ℝ},0 ≤ Z → 0 < eps →
      ∀ᶠ n : ℕ in atTop,∀ z : ℝ × ℝ,|z.2| ≤ Z →
        R n z ≤ ENNReal.ofReal (B1*(n+2 : ℕ)*Real.exp ((n+2 : ℕ)*(theta z+eps))) := by
    intro Z eps hZ heps
    filter_upwards [hSharp hZ heps] with n hn
    intro z hz
    exact hn z.1 z.2 hz
  have hCrude' : ∀ n : ℕ,∀ z : ℝ × ℝ,
      R n z ≤ ENNReal.ofReal (B2*(n+2 : ℕ)*Real.exp ((n+2 : ℕ)*
        ((1-Real.log (Q*μ.xi1 Q))/2+GaussianCrudeDeterminant.crudeConstant (Q^2*μ.xi2 Q)+
          |z.2|-κ/2*(z.1^2+z.2^2)))) := by
    intro n z
    apply (hCrude n z.1 z.2).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hscore := sourceScoreQuadratic_coercivity μ h.overlap_range.1 z.1 z.2
    have hh := mul_le_mul_of_nonneg_left hscore (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)
    nlinarith
  obtain ⟨B,c,a,hB,hc,ha,hbound⟩ := combined_intensity_envelope R theta S hB1 hB2 hκ hη hρ
    hSharp' hCrude' hTheta
  let T := polynomialAbsorptionThreshold (B*(Real.pi/a)) 1 (c/2)
  have hDim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hbound,hDim.eventually_ge_atTop T] with n hn hN
  rw [sourceMarkedOriginalCountMass_eq_plane_integral n μ h.overlap_range.1 hnp K hK]
  apply (intensity_lintegral_envelope (R n) S hB.le (by positivity) ha hn).trans
  apply ENNReal.ofReal_le_ofReal
  have hpoly := polynomial_le_exp_of_threshold (B := B*(Real.pi/a)) 1 (by positivity)
    (show 0 < c/2 by positivity) hN
  simp only [pow_one] at hpoly
  calc
    B*(n+2 : ℕ)*(Real.pi/a)*Real.exp (-c*(n+2 : ℕ))=
      (B*(Real.pi/a)*(n+2 : ℕ))*Real.exp (-c*(n+2 : ℕ)) := by ring
    _ ≤ Real.exp (c/2*(n+2 : ℕ))*Real.exp (-c*(n+2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

def sourceRadialClearance (μ : FiniteMixture) (β Q : ℝ) (U : Set ℝ) : ℝ :=
  Metric.infDist (markK μ β Q) Uᶜ

theorem sourceRadialClearance_pos (μ : FiniteMixture) {β Q L R : ℝ}
    (hm : markK μ β Q ∈ Ioo L R) : 0 < sourceRadialClearance μ β Q (Ioo L R) := by
  apply (isOpen_Ioo.isClosed_compl.notMem_iff_infDist_pos ?_).mp
  · simpa only [mem_compl_iff,not_not] using hm
  · refine ⟨L,?_⟩
    simp

/-- The source A3 condition gives an exponentially small literal expected
count of all critical points above the lower energy threshold and outside U. -/
theorem sourceHighExcludedCountMass_exponential (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hm : markK μ β Q ∈ Ioo L R)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*(sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ n : ℕ in atTop,
      sourceHighExcludedCountMass n μ Q (markE μ β x Q-δ) (Ioo L R) ≤
        ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ))) := by
  let u := sourceRadialClearance μ β Q (Ioo L R)
  have hu : 0 < u := sourceRadialClearance_pos μ hm
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  let K := sourceHighExcludedScoreWindow (markE μ β x Q-δ) (Ioo L R)
  have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _ measurableSet_Ici measurableSet_Ioo.compl
  have hgap : ∀ z ∈ K,markedComplexity μ Q z ≤ -(3*sourceMarkedLeastCurvature μ Q*u^2/8) := by
    intro z hz
    have hk : u ≤ |z 1-markK μ β Q| := by
      have hh := Metric.infDist_le_dist_of_mem (x := markK μ β Q) hz.2
      change Metric.infDist (markK μ β Q) (Ioo L R)ᶜ ≤ |z 1-markK μ β Q|
      simpa only [Real.dist_eq,abs_sub_comm] using hh
    have hLoss := sourceMarkedComplexity_excluded_radial_loss μ h hnp hA3 hz.1 hk hu.le
    have hzEq : scorePairEquiv (z 0,z 1)=z := by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    change markedComplexity μ Q (scorePairEquiv (z 0,z 1)) ≤ _ at hLoss
    rw [hzEq] at hLoss
    calc
      markedComplexity μ Q z ≤ -3*sourceMarkedLeastCurvature μ Q*
        (sourceRadialClearance μ β Q (Ioo L R))^2/8 := hLoss
      _=-(3*sourceMarkedLeastCurvature μ Q*u^2/8) := by dsimp [u]; ring
  obtain ⟨c,hc,hcount⟩ := sourceMarkedOriginalCountMass_exponential_of_gap μ h hnp K hK
    (show 0 < 3*sourceMarkedLeastCurvature μ Q*u^2/8 by positivity) hgap
  refine ⟨c,hc,?_⟩
  filter_upwards [hcount] with n hn
  rwa [sourceMarkedOriginalCountMass_def,←sourceHighExcludedCountMass_def] at hn

/-- The same actual count calculation excludes a fixed high energy above
the literal source contact, over the entire unrestricted radial line. -/
theorem sourceAboveContactCountMass_exponential (μ : FiniteMixture) {β x Q t : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (ht : 0 < t) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ n : ℕ in atTop,
      sourceMarkedOriginalCountMass n μ Q (rectangularScoreWindow (Ici (markE μ β x Q+t)) univ) ≤
        ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ))) := by
  have hβx := mul_pos h.beta_pos h.weight_range.1
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree; omega) hnp
  apply sourceMarkedOriginalCountMass_exponential_of_gap μ h hnp _
    (rectangularScoreWindow_measurable _ _ measurableSet_Ici MeasurableSet.univ) (mul_pos hβx ht)
  intro z hz
  have hLoss := sourceMarkedComplexity_global_loss μ h hnp (z 0) (z 1)
  have henergy : -(β*x)*(z 0-markE μ β x Q) ≤ -(β*x)*t := by
    have hh := mul_le_mul_of_nonneg_left hz.1 hβx.le
    nlinarith
  have hpen : 0 ≤ sourceMarkedLeastCurvature μ Q*((z 0-markE μ β x Q)^2+(z 1-markK μ β Q)^2)/2 :=
    by positivity
  have hzEq : scorePairEquiv (z 0,z 1)=z := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  change markedComplexity μ Q (scorePairEquiv (z 0,z 1)) ≤ _ at hLoss
  rw [hzEq] at hLoss
  nlinarith

end SlowEquilibration.SphericalMarkedWindows
