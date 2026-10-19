-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRawRadialAllResultsWithUnit
public import SlowEquilibration.SourcePureUpperTailSourceComplete

/-! One selected proper-pure center, radial interval, and retained-count data
serve both the source §11.14 joint-ground conclusion and all four literal
original-field upper-tail expected-count limits. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate LatitudeGroundTrial ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_pure_actual_raw_score_and_upper_tail_same_witness
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
      (∀ t : ℝ,
        Tendsto (fun n : ℕ =>
          sourcePureTruncatedLocalMaxTailMean (n+1) p hp a ha Q
            (E-δ) (E+δ) (m (n+1)+t))
          atTop (𝓝 (Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ =>
          (∫⁻ J, actualScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧ b 1 ∈ U}
            (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal)
          atTop (𝓝 (Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ =>
          sourceRetainedValueWindowMean (n+2) μ Q
            (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
            (g/2) C ε η E G)
          atTop (𝓝 (Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ =>
          (∫⁻ J, sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧ b 1 ∈ U}
            (g/2) C ε η E G J ∂disorderLaw (n+3) μ.maxDegree).toReal)
          atTop (𝓝 (Real.exp (-(β*x)*t)))) ∧
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
  obtain ⟨m,M,C,cut,η,ε,δ,D,U,hM,hδ,hU,hOpen,hMark,hClosure,
    hcenter,hUnit,hLeft,hpδ,hUnfiltered,hMean,hMoments,hInputs,hRetEq,hCritMean,hCount,hJoint⟩ :=
    source_pure_actual_raw_score_all_results_with_unit p hp a ha h
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  refine ⟨m,M,C,cut,η,ε,δ,D,U,hM,hδ,hU,hOpen,hMark,hClosure,
    hcenter,hUnit,hLeft,hpδ,hUnfiltered,hMean,hMoments,hInputs,hRetEq,hCritMean,hCount,?_,hJoint⟩
  have hg : 0 < g := by
    have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
      simpa only [markB] using h.edge_margin.2.2
    exact div_pos hedge (by norm_num)
  have hm : E ∈ Ioo (E-δ) (E+δ) := by
    constructor <;> dsimp [E] <;> linarith
  intro t
  have hMaxDensity :=
    (sourcePure_truncatedLocalMax_normalized_limits_of_center p hp a ha h
      hm hg hLeft le_rfl m hM hUnit).2 t
  have hMaxShift := hMaxDensity.comp (tendsto_add_atTop_nat 1)
  have hMaxActual : Tendsto (fun n : ℕ =>
      sourcePureTruncatedLocalMaxTailMean (n+1) p hp a ha Q
        (E-δ) (E+δ) (m (n+1)+t))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    apply hMaxShift.congr'
    exact Filter.Eventually.of_forall fun n => by
      change tail (pureTruncatedLocalMaxDensity (n+1) p hp a ha Q
        ((n+1+2 : ℕ)*(E-δ)) ((n+1+2 : ℕ)*(E+δ))) (m (n+1)+t) = _
      exact (sourcePureTruncatedLocalMaxTailMean_eq_tail (n+1) p hp a ha
        h.overlap_range.1 (E-δ) (E+δ) (m (n+1)+t)).symm
  have hRaw := sourcePure_actual_raw_score_upper_tail_mean_limit_of_center
    p hp a ha h hδ hg hLeft m hM hUnit t
  have hRet := source_pure_actual_retained_upper_tail_mean_limit_of_center
    p hp a ha h hδ hg hLeft m hM hUnit (g/2) C ε η G hMean t
  have hRetRaw := sourcePureRetainedRawScoreUpperTail_mean_tendsto
    p hp a ha Q E δ m t (g/2) C ε η G
    (Real.exp (-(β*x)*t)) hRet
  exact ⟨hMaxActual,hU ▸ hRaw,hRet,hU ▸ hRetRaw⟩

end SlowEquilibration.SphericalMarkedWindows
