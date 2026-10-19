-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalCountProbability
public import SlowEquilibration.SphericalMaximumGlobalTail

/-! Fixed-window probability consequences for the literal mixed retained count.
The common centering, radial interval, filter, and disorder law are those
constructed by the canonical source 11.13 second-moment theorem. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The zero-count event is a full-mean deviation. -/
theorem source_zero_probability_of_variance_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (a v : ℝ)
    (hX : MemLp X 2 ν) (ha : 0 < a)
    (hMean : (∫ ω, X ω ∂ν) = a)
    (hVar : ProbabilityTheory.variance X ν ≤ v) :
    ν {ω | X ω = 0} ≤ ENNReal.ofReal (v/a^2) := by
  have hsubset : {ω | X ω = 0} ⊆
      {ω | a ≤ |X ω-(∫ x, X x ∂ν)|} := by
    intro ω hw
    change X ω = 0 at hw
    change a ≤ |X ω-(∫ x, X x ∂ν)|
    rw [hMean, hw]
    simpa only [zero_sub, abs_neg, abs_of_pos ha] using le_refl a
  have hCheb := ProbabilityTheory.meas_ge_le_variance_div_sq hX ha
  have hDiv : ProbabilityTheory.variance X ν/a^2 ≤ v/a^2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg _)
  calc
    ν {ω | X ω = 0} ≤
        ν {ω | a ≤ |X ω-(∫ x, X x ∂ν)|} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (ProbabilityTheory.variance X ν/a^2) := by
      simpa only using hCheb
    _ ≤ ENNReal.ofReal (v/a^2) := ENNReal.ofReal_le_ofReal hDiv

private theorem source_probability_limsup_of_eventual_bound
    (p q : ℕ → ℝ) (A : ℝ)
    (hp : ∀ n, 0 ≤ p n) (hq : Tendsto q atTop (𝓝 A))
    (hbound : ∀ᶠ n : ℕ in atTop, p n ≤ q n) :
    Filter.limsup p atTop ≤ A := by
  have hLow : IsCoboundedUnder (· ≤ ·) atTop p :=
    isCoboundedUnder_le_of_le atTop (fun n => hp n)
  exact (limsup_le_limsup hbound hLow hq.isBoundedUnder_le).trans_eq hq.limsup_eq

/-- The actual centered retained count obeys both precise source 11.14
Chebyshev limsup bounds, with one filter chosen independently of the fixed
window width. -/
theorem source_mixed_actual_retained_canonical_probability_limsup
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
  dsimp only
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hall⟩ :=
    source_mixed_actual_retained_canonical_window_variance μ h hnp hd hδMax
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hwindow⟩ := hall hα hHalf
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
    simpa only [aN,K,A,G,E,g,neg_mul, mul_neg,neg_neg] using
      (hwindow (-t) t (by linarith)).1
  have ha : ∀ᶠ n : ℕ in atTop, 0 < aN n :=
    hmean.eventually (eventually_gt_nhds hA)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.variance (X n) (disorderLaw (n+3) μ.maxDegree) ≤
        D*sourcePrintedPairError α n*(aN n)^2+k*aN n ∧
      MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree) := by
    filter_upwards [(hwindow (-t) t (by linarith)).2] with n hn
    simpa only [aN,K,X,G,E,g,k] using hn
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
  · have hLimit := source_probability_limsup_of_eventual_bound
      (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0})
      (fun n => D*sourcePrintedPairError α n+k/aN n) (k/A)
      (fun n => measureReal_nonneg) hrat hPzero
    simpa only [X,K,G,E,g,k,A,sub_eq_add_neg] using hLimit
  · have hLimit := source_probability_limsup_of_eventual_bound
      (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2})
      (fun n => 4*(D*sourcePrintedPairError α n+k/aN n)) (4*(k/A))
      (fun n => measureReal_nonneg) (tendsto_const_nhds.mul hrat) hPhalf
    simpa only [X,aN,K,G,E,g,k,A,sub_eq_add_neg,mul_div_assoc] using hLimit

end
end SlowEquilibration.PairConditionalDeterminantMoments
