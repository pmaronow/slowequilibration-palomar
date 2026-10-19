-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedJointProbabilityWithUnit

/-! Exact source 11.14 sequential fixed-window ground event for the original
proper-pure Gaussian field, retaining one selected center and cutoff. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalMarkedWindows
open TwoAtomStationarity SphericalTAPCertificate LatitudeGroundTrial ExpectedTailCentering
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem source_pure_actual_retained_joint_ground_limit_with_unit
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
      (∀ L : ℝ, 0 < L →
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
          sourceSphereMaximum (n+1) μ Q J < m (n+1)-L → X n J=0)) ∧
      (∀ L : ℝ, 0 < L → ∃ B : ℝ, ∀ n : ℕ,
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L) ≤ B) ∧
      ∀ z : ℝ, 0 < z → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
        let I n := sourcePureCenteredNormalizedWindow n m E δ (-L) L
        let X n J := (sourceRetainedValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (I n)
          (g/2) C ε η E G J).toReal
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L}) atTop ≤ z ∧
        1-z ≤ Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | X n J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop ∧
        1-z ≤ Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | actualValueWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (I n)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨m,M,C,cut,η,ε,δ,D,hM,hδ,hLeft,hpδ,hcenter,hUnit,hUnfiltered,hMean,hMoments,hInputs,hCount,hJoint⟩ :=
    source_pure_actual_retained_joint_ground_tightness_with_unit p hp a ha h
  refine ⟨m,M,C,cut,η,ε,δ,D,hM,hδ,hLeft,hpδ,hcenter,hUnit,hUnfiltered,hMean,hMoments,hInputs,hCount,?_⟩
  let b := β*x
  let k := 1+(1-ε)/(cut^2-ε)
  let W : ℝ → ℝ := fun L => Real.exp (b*L)-Real.exp (-b*L)
  let e : ℝ → ℝ := fun L => Real.exp (-b*L)+k/W L
  have hb : 0 < b := mul_pos h.beta_pos h.weight_range.1
  have hExp : Tendsto (fun L : ℝ => Real.exp (b*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  have hExpSub : Tendsto (fun L : ℝ => Real.exp (b*L)-1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-1 : ℝ) hExp using 1
  have hW : Tendsto W atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hExpSub
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have hExpSmall : Real.exp (-b*L) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hb,hL]
    dsimp [W]
    linarith
  have hNeg : Tendsto (fun L : ℝ => Real.exp (-b*L)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    have hi : Tendsto (fun L => k/W L) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv,mul_zero] using
        (tendsto_const_nhds.mul hW.inv_tendsto_atTop :
          Tendsto (fun L => k*(W L)⁻¹) atTop (𝓝 (k*0)))
    simpa only [e,zero_add] using hNeg.add hi
  intro z hz
  have hsmall : ∀ᶠ L : ℝ in atTop, e L ≤ z :=
    (he.eventually (Iio_mem_nhds hz)).mono (fun _ hh => hh.le)
  obtain ⟨L₁,hL₁⟩ := eventually_atTop.mp hsmall
  refine ⟨max L₁ 1,by positivity,?_⟩
  intro L hL
  have hLpos : 0 < L := (by norm_num : (0:ℝ)<1).trans_le
    ((le_max_right L₁ 1).trans hL)
  have hError : e L ≤ z := hL₁ L ((le_max_left L₁ 1).trans hL)
  obtain ⟨hDev,hGood⟩ := hJoint L hLpos
  dsimp [e,W,b,k] at hError
  have hRet : 1-z ≤ Filter.liminf (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceRetainedValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (g/2) C ε η E (gap μ Q (markY β Q) (markZ x Q) ε η) J).toReal ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop :=
    (sub_le_sub_left hError 1).trans hGood
  refine ⟨hDev.trans hError,hRet,?_⟩
  let I (n : ℕ) := sourcePureCenteredNormalizedWindow n m E δ (-L) L
  let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
    (sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (g/2) C ε η E (gap μ Q (markY β Q) (markZ x Q) ε η) J).toReal
  let Pcrit (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | actualValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (fun _ _ => 1) J ≠ 0 ∧
      sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}
  let Pret (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | X n J ≠ 0 ∧ sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}
  have hMon : ∀ n : ℕ, Pret n ≤ Pcrit n := by
    intro n
    apply measureReal_mono _ (measure_ne_top _ _)
    intro J hJ
    refine ⟨?_,hJ.2⟩
    have hCount : sourceRetainedValueWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q) (I n)
        (g/2) C ε η E (gap μ Q (markY β Q) (markZ x Q) ε η) J ≠ 0 := by
      intro hz
      apply hJ.1
      simp only [X,hz,ENNReal.toReal_zero]
    have hLe := sourceRetainedValueWindowCount_le_unfiltered (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (g/2) C ε η E (gap μ Q (markY β Q) (markZ x Q) ε η) J
    intro hz
    rw [hz] at hLe
    exact hCount (le_antisymm hLe bot_le)
  have hRetLow : IsBoundedUnder (· ≥ ·) atTop Pret :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hCritHigh : IsCoboundedUnder (· ≥ ·) atTop Pcrit :=
    (isBoundedUnder_of ⟨(1:ℝ),fun n => measureReal_le_one⟩ :
      IsBoundedUnder (· ≤ ·) atTop Pcrit).isCoboundedUnder_ge
  have hLiminf := liminf_le_liminf (Eventually.of_forall hMon) hRetLow hCritHigh
  simpa only [Pret,Pcrit,X,I] using hRet.trans hLiminf

end SlowEquilibration.PairConditionalDeterminantMoments
