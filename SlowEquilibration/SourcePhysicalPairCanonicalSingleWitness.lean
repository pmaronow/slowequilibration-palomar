-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalSecondMoment

/-! Source 11.13 and 11.14 with one common center, radial interval, and
retained-point selection. The conclusions of 11.14 are derived from the
11.13 second-moment witness itself. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 2200000

private theorem source_single_witness_limsup_of_eventual_bound
    (p q : ℕ → ℝ) (A : ℝ)
    (hp : ∀ n, 0 ≤ p n) (hq : Tendsto q atTop (𝓝 A))
    (hbound : ∀ᶠ n : ℕ in atTop, p n ≤ q n) :
    Filter.limsup p atTop ≤ A := by
  have hLow : IsCoboundedUnder (· ≤ ·) atTop p :=
    isCoboundedUnder_le_of_le atTop (fun n => hp n)
  exact (limsup_le_limsup hbound hLow hq.isBoundedUnder_le).trans_eq hq.limsup_eq

/-- A single unconditional mixed-model witness provides the printed
source 11.13 moments and the source 11.14 zero-count and lower-half
probability bounds, bounded ordinary critical-point counts, and the joint
ground-event iterated limit. -/
theorem source_mixed_actual_canonical_single_witness_11_13_11_14
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
        (∀ {α : ℝ}, 1/4 < α → α < 1/2 →
          ∃ D : ℝ, 0 < D ∧
          ∀ a b : ℝ, a < b →
            let G := gap μ Q (markY β Q) (markZ x Q) ε η
            let K n := physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)+a) (d.center (n+1)+b)) (Ioo L R)
            let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
              (g/2) C ε η E G
            let X n J := (sourceRetainedScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (g/2) C ε η E G J).toReal
            Tendsto aN atTop
              (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) ∧
              ∀ᶠ n : ℕ in atTop,
                (∫ J, (X n J)^2 ∂disorderLaw (n+3) μ.maxDegree) ≤
                  (1+D*sourcePrintedPairError α n)*(aN n)^2+
                    (1+(1-ε)/(cut^2-ε))*aN n ∧
                ProbabilityTheory.variance (X n)
                  (disorderLaw (n+3) μ.maxDegree) ≤
                  D*sourcePrintedPairError α n*(aN n)^2+
                    (1+(1-ε)/(cut^2-ε))*aN n ∧
                MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree)) ∧
        (∀ {α : ℝ}, 1/4 < α → α < 1/2 →
          ∃ D : ℝ, 0 < D ∧
          ∀ t : ℝ, 0 < t →
            let G := gap μ Q (markY β Q) (markZ x Q) ε η
            let K n := physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)-t) (d.center (n+1)+t)) (Ioo L R)
            let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
              (g/2) C ε η E G
            let X n J := (sourceRetainedScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (g/2) C ε η E G J).toReal
            Filter.limsup (fun n => (disorderLaw (n+3) μ.maxDegree).real
              {J | X n J = 0}) atTop ≤
              (1+(1-ε)/(cut^2-ε)) /
                (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)) ∧
            Filter.limsup (fun n => (disorderLaw (n+3) μ.maxDegree).real
              {J | X n J < aN n/2}) atTop ≤
              4*(1+(1-ε)/(cut^2-ε)) /
                (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))) ∧
        (∀ t : ℝ, 0 < t →
          ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
            sourceCriticalPhysicalWindowCardMean n μ Q
              (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) ≤ B) ∧
        Tendsto (fun t : ℝ => Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | (sourceCriticalPhysicalWindowSet n μ Q
              (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
              sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop)
          atTop (𝓝 1) := by
  dsimp only
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hMoments⟩ :=
    source_mixed_actual_retained_canonical_window_second_moment μ h hnp hd hδMax
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hProb : ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
      ∃ D : ℝ, 0 < D ∧
      ∀ t : ℝ, 0 < t →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        let K n := physicalEnergyWindow (n+3)
          (Icc (d.center (n+1)-t) (d.center (n+1)+t)) (Ioo L R)
        let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
          (g/2) C ε η E G
        let X n J := (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (K n)
          (g/2) C ε η E G J).toReal
        Filter.limsup (fun n => (disorderLaw (n+3) μ.maxDegree).real
          {J | X n J = 0}) atTop ≤
          (1+(1-ε)/(cut^2-ε)) /
            (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)) ∧
        Filter.limsup (fun n => (disorderLaw (n+3) μ.maxDegree).real
          {J | X n J < aN n/2}) atTop ≤
          4*(1+(1-ε)/(cut^2-ε)) /
            (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)) := by
    intro α hα hHalf
    obtain ⟨D,hD,hwindow⟩ := hMoments hα hHalf
    refine ⟨D,hD,?_⟩
    intro t ht
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    let K (n : ℕ) := physicalEnergyWindow (n+3)
      (Icc (d.center (n+1)+ -t) (d.center (n+1)+t)) (Ioo L R)
    let aN (n : ℕ) := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
      (g/2) C ε η E G
    let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
      (sourceRetainedScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) (K n)
        (g/2) C ε η E G J).toReal
    let A := Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)
    let k := 1+(1-ε)/(cut^2-ε)
    have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
    have hA : 0 < A := by
      dsimp [A]
      exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [hc0,ht]))
    have hden : 0 < cut^2-ε := by nlinarith [hεCut]
    have hnum : 0 ≤ 1-ε := by
      nlinarith [hεCut,hcutOne,mul_nonneg hcut.le (sub_nonneg.mpr hcutOne)]
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hmean : Tendsto aN atTop (𝓝 A) := by
      simpa only [aN,K,A,G,E,g,neg_mul,mul_neg,neg_neg] using
        (hwindow (-t) t (by linarith)).1
    have ha : ∀ᶠ n : ℕ in atTop, 0 < aN n :=
      hmean.eventually (eventually_gt_nhds hA)
    have hbounds : ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance (X n) (disorderLaw (n+3) μ.maxDegree) ≤
          D*sourcePrintedPairError α n*(aN n)^2+k*aN n ∧
        MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree) := by
      filter_upwards [(hwindow (-t) t (by linarith)).2] with n hn
      simpa only [aN,K,X,G,E,g,k] using And.intro hn.2.1 hn.2.2
    have hrat : Tendsto (fun n => D*sourcePrintedPairError α n+k/aN n)
        atTop (𝓝 (k/A)) := by
      have hErr : Tendsto (fun n => D*sourcePrintedPairError α n)
          atTop (𝓝 (0:ℝ)) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul
          (sourcePrintedPairError_tendsto hα hHalf) :
            Tendsto (fun n => D*sourcePrintedPairError α n) atTop (𝓝 (D*0)))
      have hInv : Tendsto (fun n => k/aN n) atTop (𝓝 (k/A)) :=
        tendsto_const_nhds.div hmean hA.ne'
      simpa only [zero_add] using hErr.add hInv
    have hPzero : ∀ᶠ n : ℕ in atTop,
        (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0} ≤
          D*sourcePrintedPairError α n+k/aN n := by
      filter_upwards [ha,hbounds] with n han hn
      have hMean := source_actual_retained_count_expectation_eq_mean
        (n+2) (by omega) μ h.overlap_range.1 hnp (K n)
        (rectangularScoreWindow_measurable _ _
          (measurableSet_Icc.preimage (measurable_const_mul ((n+3:ℕ):ℝ))) measurableSet_Ioo)
        (g/2) C ε η E G
      have hCheb := source_zero_probability_of_variance_bound
        (disorderLaw (n+3) μ.maxDegree) (X n) (aN n)
        (D*sourcePrintedPairError α n*(aN n)^2+k*aN n)
        hn.2 han hMean hn.1
      have hv : 0 ≤ D*sourcePrintedPairError α n*(aN n)^2+k*aN n := by
        exact add_nonneg (mul_nonneg (mul_nonneg hD.le
          (sourcePrintedPairError_nonneg α n)) (sq_nonneg _)) (mul_nonneg hk han.le)
      have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCheb
      rw [ENNReal.toReal_ofReal (div_nonneg hv (sq_nonneg _))] at hReal
      have hEq : (D*sourcePrintedPairError α n*(aN n)^2+k*aN n)/(aN n)^2 =
          D*sourcePrintedPairError α n+k/aN n := by
        field_simp
      exact hReal.trans_eq hEq
    have hPhalf : ∀ᶠ n : ℕ in atTop,
        (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2} ≤
          4*(D*sourcePrintedPairError α n+k/aN n) := by
      filter_upwards [ha,hbounds] with n han hn
      have hMean := source_actual_retained_count_expectation_eq_mean
        (n+2) (by omega) μ h.overlap_range.1 hnp (K n)
        (rectangularScoreWindow_measurable _ _
          (measurableSet_Icc.preimage (measurable_const_mul ((n+3:ℕ):ℝ))) measurableSet_Ioo)
        (g/2) C ε η E G
      have hCheb := source_below_half_probability_of_variance_bound
        (disorderLaw (n+3) μ.maxDegree) (X n) (aN n)
        (D*sourcePrintedPairError α n*(aN n)^2+k*aN n)
        hn.2 han hMean hn.1
      have hv : 0 ≤ D*sourcePrintedPairError α n*(aN n)^2+k*aN n := by
        exact add_nonneg (mul_nonneg (mul_nonneg hD.le
          (sourcePrintedPairError_nonneg α n)) (sq_nonneg _)) (mul_nonneg hk han.le)
      have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCheb
      rw [ENNReal.toReal_ofReal (div_nonneg hv (sq_nonneg _))] at hReal
      have hEq : (D*sourcePrintedPairError α n*(aN n)^2+k*aN n)/(aN n/2)^2 =
          4*(D*sourcePrintedPairError α n+k/aN n) := by
        field_simp
        ring
      exact hReal.trans_eq hEq
    constructor
    · have hLimit := source_single_witness_limsup_of_eventual_bound
        (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0})
        (fun n => D*sourcePrintedPairError α n+k/aN n) (k/A)
        (fun n => measureReal_nonneg) hrat hPzero
      simpa only [X,K,G,E,g,k,A,sub_eq_add_neg] using hLimit
    · have hLimit := source_single_witness_limsup_of_eventual_bound
        (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2})
        (fun n => 4*(D*sourcePrintedPairError α n+k/aN n)) (4*(k/A))
        (fun n => measureReal_nonneg) (tendsto_const_nhds.mul hrat) hPhalf
      simpa only [X,aN,K,G,E,g,k,A,sub_eq_add_neg,mul_div_assoc] using hLimit
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hMoments,hProb,?_,?_⟩
  · intro t ht
    obtain ⟨B,hB,hbound⟩ := d.uniform_window_bound (-t) t (by linarith)
    refine ⟨B,hB,?_⟩
    intro n
    rw [sourceCriticalPhysicalWindowCardMean_eq_sourceCriticalWindowMean
      n μ h.overlap_range.1]
    simpa only [sub_eq_add_neg] using (hbound (n+1)).2
  · obtain ⟨D,_hD,hwin⟩ := hProb (α := (3:ℝ)/8) (by norm_num) (by norm_num)
    let k := 1+(1-ε)/(cut^2-ε)
    let p (t : ℝ) := Filter.liminf (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceCriticalPhysicalWindowSet n μ Q
          (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
          sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop
    have hm : markK μ β Q ∈ Ioo L R := ⟨hL,hR⟩
    have hκ : 0 < sourceMarkedLeastCurvature μ Q :=
      sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by omega) hnp
    have hu : 0 < sourceRadialClearance μ β Q (Ioo L R) :=
      sourceRadialClearance_pos μ hm
    let δ := sourceMarkedLeastCurvature μ Q *
      (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
    have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hfixed : ∀ t : ℝ, 0 < t →
        1-(Real.exp (-(β*x)*t)+k/
          (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))) ≤ p t := by
      intro t ht
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      let a := k/(Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))
      have hZero := (hwin t ht).1
      have hUpper := sourceSphereMaximum_centered_probability_limsup_shift
        μ h hnp hEdge hm hδ (le_refl _) d t
      have hJoint := source_retained_window_joint_probability_of_limsup
        μ Q (fun n => d.center (n+1)) (Ioo L R)
        (g/2) C ε η E G t a (Real.exp (-(β*x)*t)) hZero hUpper
      let pRet (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3)
            (Icc (d.center (n+1)-t) (d.center (n+1)+t)) (Ioo L R))
          (g/2) C ε η E G J).toReal ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}
      let pCrit (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceCriticalPhysicalWindowSet n μ Q
          (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
          sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}
      have hpoint : ∀ n, pRet n ≤ pCrit n := by
        intro n
        apply measureReal_mono
        · intro J hJ
          refine ⟨?_,hJ.2⟩
          change (Set.Nonempty {u : Vector (n+3) |
            ‖u‖^2=(n+3:ℕ) ∧
            surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
            field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
              Icc (d.center (n+1)-t) (d.center (n+1)+t) ∧
            actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R})
          exact source_retained_nonzero_critical_window_nonempty n μ Q
            (d.center (n+1)-t) (d.center (n+1)+t) (g/2) C ε η E G
            (Ioo L R) J hJ.1
        · finiteness
      have hRetBound : IsBoundedUnder (· ≥ ·) atTop pRet :=
        isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
      have hCritCob : IsCoboundedUnder (· ≥ ·) atTop pCrit :=
        (isBoundedUnder_of ⟨(1:ℝ),fun n => measureReal_le_one⟩ :
          IsBoundedUnder (· ≤ ·) atTop pCrit).isCoboundedUnder_ge
      have hTransfer := Filter.liminf_le_liminf (Eventually.of_forall hpoint)
        hRetBound hCritCob
      have hLow := hJoint.trans hTransfer
      simpa only [p,pCrit,a,G,E,g,k] using hLow
    have hLower : Tendsto (fun t : ℝ =>
        1-(Real.exp (-(β*x)*t)+k/
          (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)))) atTop (𝓝 1) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub (source_canonical_ground_error_tendsto_zero
          (β*x) k hc0) : Tendsto (fun t : ℝ =>
          (1:ℝ)-(Real.exp (-(β*x)*t)+k/
            (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)))) atTop (𝓝 (1-0)))
    have hUpper : ∀ t : ℝ, p t ≤ 1 := by
      intro t
      have hBound : IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | (sourceCriticalPhysicalWindowSet n μ Q
            (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
            sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) :=
        isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
      apply Filter.liminf_le_of_le hBound
      intro b hb
      obtain ⟨n,hn⟩ := hb.exists
      exact hn.trans measureReal_le_one
    have hResult : Tendsto p atTop (𝓝 1) := by
      apply hLower.squeeze' tendsto_const_nhds
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
        exact hfixed t ht
      · exact Eventually.of_forall hUpper
    simpa only [p] using hResult

end
end SlowEquilibration.PairConditionalDeterminantMoments
