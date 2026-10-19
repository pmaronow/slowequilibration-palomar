-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureNarrowRadialAdmissible
public import SlowEquilibration.SourcePureRetainedJointGroundLimitWithUnit
public import SlowEquilibration.SourcePureRetainedRawRadialBridge
public import SlowEquilibration.SourcePureCriticalRawRadialGroundLimit

/-! Literal pure source §11.14 with the same centered witness and an
admissible radial interval whose closure lies in the source mark band. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate LatitudeGroundTrial ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false

/-- Source §11.14 for a proper-pure original field with the literal raw
energy window and one fixed open radial interval selected before all
window widths. The critical count is an ordinary unsigned set count. -/
theorem source_pure_actual_raw_score_all_results_with_unit
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    ∃ m : ℕ → ℝ, ∃ M C cut η ε δ D : ℝ, ∃ U : Set ℝ,
      0 < M ∧ 0 < δ ∧ U = Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ)) ∧
      IsOpen U ∧ markK μ β Q ∈ U ∧
      closure U ⊆ Icc
        (2*Real.sqrt (Q^2*μ.xi2 Q)+
          (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2)
        (markK μ β Q+1) ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      (∀ᶠ n : ℕ in atTop,
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+
        (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2 ≤ (p : ℝ)*(E-δ) ∧
      (p : ℝ)*δ < 1 ∧
      let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
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
      (∀ n : ℕ, ∀ L R : ℝ,
        ∀ J : Disorder (n+3) μ.maxDegree,
          sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredRawNormalizedWindow n m L R ∧ b 1 ∈ U}
            (g/2) C ε η E G J =
          sourceRetainedValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            (sourcePureCenteredNormalizedWindow n m E δ L R)
            (g/2) C ε η E G J) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          {b : EuclideanSpace ℝ (Fin 2) |
            b 0 ∈ sourcePureCenteredRawNormalizedWindow n m L R ∧ b 1 ∈ U}
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal)
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ L : ℝ, 0 < L → ∃ B : ℝ, ∀ n : ℕ,
        let V := sourcePureCenteredRawNormalizedWindow n m (-L) L
        let K := {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V ∧ b 1 ∈ U}
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B) ∧
      ∀ z : ℝ, 0 < z → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
        let V n := sourcePureCenteredRawNormalizedWindow n m (-L) L
        let K n := {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V n ∧ b 1 ∈ U}
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L}) Filter.atTop ≤ z ∧
        1-z ≤ Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) Filter.atTop := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  obtain ⟨m,M,C,cut,η,ε,δ,D,hM,hδ,hLeft,hpδ,hcenter,hUnit,hUnfiltered,hMean,hMoments,hInputs,hCount,hJoint⟩ :=
    source_pure_actual_retained_joint_ground_limit_with_unit p hp a ha h
  let U : Set ℝ := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
  have hAdmissible := source_pure_narrow_radial_interval_admissible
    p hp a ha h hδ hLeft hpδ
  refine ⟨m,M,C,cut,η,ε,δ,D,U,hM,hδ,rfl,hAdmissible.1,hAdmissible.2.1,
    hAdmissible.2.2,hcenter,hUnit,hLeft,hpδ,hUnfiltered,hMean,hMoments,hInputs,?_,?_,?_,?_⟩
  · intro n L R J
    exact sourcePureRetainedRawScoreWindow_eq_clippedValueWindow
      n p hp a ha Q E δ m L R
      ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2/2) C ε η
      (gap μ Q (markY β Q) (markZ x Q) ε η) J
  · intro L R hLR
    have hbase := hUnfiltered L R hLR
    have heq (n : ℕ) :
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          {b : EuclideanSpace ℝ (Fin 2) |
            b 0 ∈ sourcePureCenteredRawNormalizedWindow n m L R ∧ b 1 ∈ U}
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal =
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R) := by
      unfold sourceUnfilteredValueWindowMean
      congr 1
      apply lintegral_congr
      intro J
      exact sourcePureCenteredRawScoreWindow_eq_clippedValueWindow
        n p hp a ha Q E δ m L R J
    apply hbase.congr'
    exact Filter.Eventually.of_forall (fun n => (heq n).symm)
  · intro L hL
    obtain ⟨B,hB⟩ := hCount L hL
    refine ⟨B,?_⟩
    intro n
    have heq : (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          {b : EuclideanSpace ℝ (Fin 2) |
            b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧ b 1 ∈ U}
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) =
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) := by
      apply lintegral_congr
      intro J
      exact sourcePureCenteredRawScoreWindow_eq_clippedValueWindow
        n p hp a ha Q E δ m (-L) L J
    dsimp only [U]
    constructor
    · rw [heq]
      exact (hB n).1
    · rw [heq]
      simpa only [sourceUnfilteredValueWindowMean] using (hB n).2
  · intro z hz
    obtain ⟨L₀,hL₀,hForall⟩ := hJoint z hz
    refine ⟨L₀,hL₀,?_⟩
    intro L hL
    obtain ⟨hDev,hRet,hValue⟩ := hForall L hL
    refine ⟨hDev,?_⟩
    have hfun : (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | actualScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧ b 1 ∈ U}
            (fun _ _ => 1) J ≠ 0 ∧
            sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) =
        (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | actualValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
            (fun _ _ => 1) J ≠ 0 ∧
            sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) := by
      funext n
      congr 1
      ext J
      have hpoint := sourcePureCenteredRawScoreWindow_eq_clippedValueWindow
        n p hp a ha Q E δ m (-L) L J
      dsimp only [μ,E,U] at hpoint ⊢
      simp only [Set.mem_ofPred_eq,hpoint]
    dsimp only [μ,E,U] at hfun ⊢
    simpa only [hfun] using hValue

end SlowEquilibration.SphericalMarkedWindows
