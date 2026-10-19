-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedCenterFirstMoment
public import SlowEquilibration.SourcePhysicalPairCanonicalCountProbabilityLimits

/-! Chebyshev limsup bounds for the literal selected proper-pure critical
count in symmetric physical-energy windows at the constructed center. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open LatitudeGroundTrial
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem pure_probability_limsup_of_eventual_bound
    (p q : ℕ → ℝ) (A : ℝ)
    (hp : ∀ n, 0 ≤ p n) (hq : Tendsto q atTop (𝓝 A))
    (hbound : ∀ᶠ n : ℕ in atTop, p n ≤ q n) :
    Filter.limsup p atTop ≤ A := by
  have hLow : IsCoboundedUnder (· ≤ ·) atTop p :=
    isCoboundedUnder_le_of_le atTop (fun n => hp n)
  exact (limsup_le_limsup hbound hLow hq.isBoundedUnder_le).trans_eq hq.limsup_eq

theorem source_pure_actual_retained_center_probability_limsup
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ m : ℕ → ℝ, ∃ C cut η ε δ : ℝ, 0 < δ ∧
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      ∀ L : ℝ, 0 < L →
        let I n := sourcePureCenteredNormalizedWindow n m E δ (-L) L
        let aN n := sourceRetainedValueWindowMean (n+2) μ Q (I n)
          (g/2) C ε η E G
        let X n J := (sourceRetainedValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (I n)
          (g/2) C ε η E G J).toReal
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | X n J = 0}) atTop ≤
          (1+(1-ε)/(cut^2-ε)) /
            (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)) ∧
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | X n J < aN n/2}) atTop ≤
          4*(1+(1-ε)/(cut^2-ε)) /
            (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨n₀,m,M,C,cut,η,ε,δ,C₂,D,hM,hδ,hC,hcut,hη,hε,hC₂,hD,
    hFallback,hCenter,hUnfiltered,hMean,hMoments⟩ :=
    source_pure_actual_retained_center_first_moment p hp a ha h
  refine ⟨m,C,cut,η,ε,δ,hδ,?_⟩
  intro L hL
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let I (n : ℕ) := sourcePureCenteredNormalizedWindow n m E δ (-L) L
  let aN (n : ℕ) := sourceRetainedValueWindowMean (n+2) μ Q (I n)
    (g/2) C ε η E G
  let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
    (sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (g/2) C ε η E G J).toReal
  let A := Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)
  let k := 1+(1-ε)/(cut^2-ε)
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hA : 0 < A := by
    dsimp [A]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [hc0,hL]))
  have hmean : Tendsto aN atTop (𝓝 A) := by
    simpa only [aN,I,A,G,E,g,neg_mul, mul_neg,neg_neg] using
      (hMean (-L) L (by linarith))
  have ha : ∀ᶠ n : ℕ in atTop, 0 < aN n :=
    hmean.eventually (eventually_gt_nhds hA)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.variance (X n) (disorderLaw (n+3) μ.maxDegree) ≤
        D*sourcePrintedPairError (3/8 : ℝ) n*(aN n)^2+k*aN n ∧
      MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree) ∧
      (∫ J, X n J ∂disorderLaw (n+3) μ.maxDegree) = aN n := by
    filter_upwards [hMoments] with n hn
    have hi := hn (I n) (sourcePureCenteredNormalizedWindow_measurable n m E δ (-L) L)
      (sourcePureCenteredNormalizedWindow_subset_value_box n m E δ (-L) L)
    exact ⟨hi.2.2.2.2,hi.2.2.1,hi.2.1⟩
  have hrat : Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n)
      atTop (𝓝 (k/A)) := by
    have hErr : Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul
        (sourcePrintedPairError_tendsto (by norm_num : (1/4 : ℝ) < 3/8)
          (by norm_num : (3/8 : ℝ) < 1/2)) :
          Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n) atTop (𝓝 (D*0)))
    have hInv : Tendsto (fun n => k/aN n) atTop (𝓝 (k/A)) :=
      tendsto_const_nhds.div hmean hA.ne'
    simpa only [zero_add] using hErr.add hInv
  have hPzero : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0} ≤
        D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n := by
    filter_upwards [ha,hbounds] with n han hn
    let v := D*sourcePrintedPairError (3/8 : ℝ) n*(aN n)^2+k*aN n
    have hCheb := source_zero_probability_of_variance_bound
      (disorderLaw (n+3) μ.maxDegree) (X n) (aN n) v
      hn.2.1 han hn.2.2 hn.1
    have hv : 0 ≤ v := (ProbabilityTheory.variance_nonneg (X n)
      (disorderLaw (n+3) μ.maxDegree)).trans hn.1
    have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCheb
    rw [ENNReal.toReal_ofReal (div_nonneg hv (sq_nonneg _))] at hReal
    have hEq : v/(aN n)^2 =
        D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n := by
      dsimp [v]
      field_simp
    exact hReal.trans_eq hEq
  have hPhalf : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2} ≤
        4*(D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n) := by
    filter_upwards [ha,hbounds] with n han hn
    let v := D*sourcePrintedPairError (3/8 : ℝ) n*(aN n)^2+k*aN n
    have hCheb := source_below_half_probability_of_variance_bound
      (disorderLaw (n+3) μ.maxDegree) (X n) (aN n) v
      hn.2.1 han hn.2.2 hn.1
    have hv : 0 ≤ v := (ProbabilityTheory.variance_nonneg (X n)
      (disorderLaw (n+3) μ.maxDegree)).trans hn.1
    have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCheb
    rw [ENNReal.toReal_ofReal (div_nonneg hv (sq_nonneg _))] at hReal
    have hEq : v/(aN n/2)^2 =
        4*(D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n) := by
      dsimp [v]
      field_simp
      ring
    exact hReal.trans_eq hEq
  constructor
  · have hLimit := pure_probability_limsup_of_eventual_bound
      (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0})
      (fun n => D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n) (k/A)
      (fun n => measureReal_nonneg) hrat hPzero
    simpa only [X,I,G,E,g,k,A,sub_eq_add_neg] using hLimit
  · have hLimit := pure_probability_limsup_of_eventual_bound
      (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2})
      (fun n => 4*(D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n)) (4*(k/A))
      (fun n => measureReal_nonneg) (tendsto_const_nhds.mul hrat) hPhalf
    simpa only [X,aN,I,G,E,g,k,A,sub_eq_add_neg,mul_div_assoc] using hLimit

end SlowEquilibration.PairConditionalDeterminantMoments
