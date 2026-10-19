-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedMaximumTransfer
public import SlowEquilibration.SourcePureRetainedCenterNarrowRadial
public import SlowEquilibration.SourcePureCenteredGlobalMaximumSharp

/-! Proper-pure source 11.14 probability inputs at one and the same
constructed center: literal selected-count zero probability, original
global-maximum upper tail, and pathwise lower-tail implication. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open LatitudeGroundTrial ExpectedTailCentering
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 900000

private theorem pure_same_center_limsup_of_eventual_bound
    (p q : ℕ → ℝ) (A : ℝ)
    (hp : ∀ n, 0 ≤ p n) (hq : Tendsto q atTop (𝓝 A))
    (hbound : ∀ᶠ n : ℕ in atTop, p n ≤ q n) :
    Filter.limsup p atTop ≤ A := by
  have hLow : IsCoboundedUnder (· ≤ ·) atTop p :=
    isCoboundedUnder_le_of_le atTop (fun n => hp n)
  exact (limsup_le_limsup hbound hLow hq.isBoundedUnder_le).trans_eq hq.limsup_eq

theorem source_pure_actual_retained_same_center_probability_with_unit
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ m : ℕ → ℝ, ∃ M C cut η ε δ D : ℝ,
      0 < M ∧ 0 < δ ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p : ℝ)*(E-δ) ∧
      (p : ℝ)*δ < 1 ∧
      (∀ᶠ n : ℕ in atTop,
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      (∀ᶠ n : ℕ in atTop,
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      0 < cut ∧ cut ≤ 1 ∧ 0 < ε ∧ ε < cut^2/2 ∧
      ε < 1-η ∧ 0 < D ∧
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R))
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourceRetainedValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R)
          (g/2) C ε η E G)
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ᶠ n : ℕ in atTop, ∀ I : Set ℝ,
        MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
          let aN := sourceRetainedValueWindowMean (n+2) μ Q I
            (g/2) C ε η E G
          let X := fun J => (sourceRetainedValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q) I
            (g/2) C ε η E G J).toReal
          sourceRetainedValueWindowSecondMoment (n+2) μ Q I
            (g/2) C ε η E G ≤
              (1+D*sourcePrintedPairError (3/8 : ℝ) n)*aN^2+
                (1+(1-ε)/(cut^2-ε))*aN ∧
          ProbabilityTheory.variance X (disorderLaw (n+3) μ.maxDegree) ≤
            D*sourcePrintedPairError (3/8 : ℝ) n*aN^2+
              (1+(1-ε)/(cut^2-ε))*aN) ∧
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
              (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)) ∧
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | m (n+1)+L ≤ sourceSphereMaximum (n+1) μ Q J}) atTop ≤
            Real.exp (-(β*x)*L) ∧
        (∀ n : ℕ, ∀ J : Disorder (n+3) μ.maxDegree,
          sourceSphereMaximum (n+1) μ Q J < m (n+1)-L → X n J=0) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨n₀,m,M,C,cut,η,ε,δ,C₂,D,hM,hδ,hpδ,hLeft,hC,hcut,hcutOne,
    hη,hε,hεCut,hεη,hC₂,hD,
    hFallback,hCenter,hUnfiltered,hMean,hMoments⟩ :=
    source_pure_actual_retained_center_narrow_radial p hp a ha h
  have hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (hCenter n hn).2.2
  have hcenterSharp : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact ⟨(hCenter n hn).1,(hCenter n hn).2.2⟩
  have hUpper := sourcePure_centered_global_maximum_limsup_sharp_shift
    p hp a ha h hδ (by
      have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
        simpa only [markB] using h.edge_margin.2.2
      exact div_pos hedge (by norm_num)) hLeft m hM hcenterSharp
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hMomentsSharp : ∀ᶠ n : ℕ in atTop, ∀ I : Set ℝ,
      MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
        let aN := sourceRetainedValueWindowMean (n+2) μ Q I
          (g/2) C ε η E G
        let X := fun J => (sourceRetainedValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) I
          (g/2) C ε η E G J).toReal
        sourceRetainedValueWindowSecondMoment (n+2) μ Q I
          (g/2) C ε η E G ≤
            (1+D*sourcePrintedPairError (3/8 : ℝ) n)*aN^2+
              (1+(1-ε)/(cut^2-ε))*aN ∧
        ProbabilityTheory.variance X (disorderLaw (n+3) μ.maxDegree) ≤
          D*sourcePrintedPairError (3/8 : ℝ) n*aN^2+
            (1+(1-ε)/(cut^2-ε))*aN := by
    filter_upwards [hMoments] with n hn
    intro I hI hsub
    exact ⟨(hn I hI hsub).2.2.2.1,(hn I hI hsub).2.2.2.2⟩
  refine ⟨m,M,C,cut,η,ε,δ,D,hM,hδ,hLeft,hpδ,hcenter,
    hcenterSharp,hcut,hcutOne,hε,hεCut,hεη,hD,
    hUnfiltered,hMean,hMomentsSharp,?_⟩
  intro L hL
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let I (n : ℕ) := sourcePureCenteredNormalizedWindow n m E δ (-L) L
  let aN (n : ℕ) := sourceRetainedValueWindowMean (n+2) μ Q (I n)
    (g/2) C ε η E G
  let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
    (sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (g/2) C ε η E G J).toReal
  let W := Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)
  let k := 1+(1-ε)/(cut^2-ε)
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hW : 0 < W := by
    dsimp [W]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [hb,hL]))
  have hmean : Tendsto aN atTop (𝓝 W) := by
    simpa only [aN,I,W,G,E,g,neg_mul,mul_neg,neg_neg] using
      (hMean (-L) L (by linarith))
  have ha : ∀ᶠ n : ℕ in atTop, 0 < aN n :=
    hmean.eventually (eventually_gt_nhds hW)
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
      atTop (𝓝 (k/W)) := by
    have hErr : Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul
        (sourcePrintedPairError_tendsto (by norm_num : (1/4 : ℝ) < 3/8)
          (by norm_num : (3/8 : ℝ) < 1/2)) :
          Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n) atTop (𝓝 (D*0)))
    have hInv : Tendsto (fun n => k/aN n) atTop (𝓝 (k/W)) :=
      tendsto_const_nhds.div hmean hW.ne'
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
  have hZero : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0}) atTop ≤ k/W :=
    pure_same_center_limsup_of_eventual_bound
      (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J = 0})
      (fun n => D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n) (k/W)
      (fun _ => measureReal_nonneg) hrat hPzero
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
  have hHalf : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2}) atTop ≤
      4*k/W := by
    have hLimit := pure_same_center_limsup_of_eventual_bound
      (fun n => (disorderLaw (n+3) μ.maxDegree).real {J | X n J < aN n/2})
      (fun n => 4*(D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n)) (4*(k/W))
      (fun _ => measureReal_nonneg) (tendsto_const_nhds.mul hrat) hPhalf
    simpa only [mul_div_assoc] using hLimit
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [X,I,G,E,g,k,W,sub_eq_add_neg] using hZero
  · simpa only [X,aN,I,G,E,g,k,W,sub_eq_add_neg,mul_div_assoc] using hHalf
  · simpa only [E] using hUpper L
  · intro n J hbelow
    rw [sourcePure_retained_centered_window_zero_of_max_below n μ Q E δ L m
      (g/2) C ε η G J hbelow]
    rfl

end SlowEquilibration.PairConditionalDeterminantMoments
