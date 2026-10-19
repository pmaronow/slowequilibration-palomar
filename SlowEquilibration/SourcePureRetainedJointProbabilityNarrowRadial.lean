-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureSameCenterProbabilityNarrowRadial
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Source 11.14 joint probability and centered maximum tightness for the
literal selected proper-pure critical count and original global maximum. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open LatitudeGroundTrial
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1100000

private theorem pure_value_joint_probability_of_limsup
    (μ : FiniteMixture) (Q : ℝ) (m : ℕ → ℝ)
    (X : (n : ℕ) → Disorder (n+3) μ.maxDegree → ℝ)
    (L a b : ℝ)
    (hzero : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J=0}) atTop ≤ a)
    (hupper : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | m (n+1)+L ≤ sourceSphereMaximum (n+1) μ Q J}) atTop ≤ b)
    (hbelow : ∀ n : ℕ, ∀ J : Disorder (n+3) μ.maxDegree,
      sourceSphereMaximum (n+1) μ Q J < m (n+1)-L → X n J=0) :
    Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L}) atTop ≤ b+a ∧
    1-(b+a) ≤ Filter.liminf (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | X n J ≠ 0 ∧ sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop := by
  let pzero (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real {J | X n J=0}
  let pupper (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | m (n+1)+L ≤ sourceSphereMaximum (n+1) μ Q J}
  let pdev (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L}
  let pgood (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | X n J ≠ 0 ∧ sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}
  have hpointDev : ∀ n, pdev n ≤ pupper n+pzero n := by
    intro n
    have hsubset : {J : Disorder (n+3) μ.maxDegree |
        |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L} ⊆
      {J | m (n+1)+L ≤ sourceSphereMaximum (n+1) μ Q J} ∪
      {J | X n J=0} := by
      intro J hJ
      change L < |sourceSphereMaximum (n+1) μ Q J-m (n+1)| at hJ
      change m (n+1)+L ≤ sourceSphereMaximum (n+1) μ Q J ∨ X n J=0
      rcases (lt_abs.mp hJ) with hhigh | hlow
      · exact Or.inl (by linarith)
      · exact Or.inr (hbelow n J (by linarith))
    exact (measureReal_mono hsubset (measure_ne_top _ _)).trans
      (measureReal_union_le _ _)
  have huB : IsBoundedUnder (· ≤ ·) atTop pupper :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have huL : IsBoundedUnder (· ≥ ·) atTop pupper :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hzB : IsBoundedUnder (· ≤ ·) atTop pzero :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hzL : IsCoboundedUnder (· ≤ ·) atTop pzero :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  have hSumB : IsBoundedUnder (· ≤ ·) atTop (fun n => pupper n+pzero n) :=
    isBoundedUnder_of ⟨2,fun n => by
      have h1 : pupper n ≤ 1 := measureReal_le_one
      have h2 : pzero n ≤ 1 := measureReal_le_one
      linarith⟩
  have hSumL : IsCoboundedUnder (· ≤ ·) atTop (fun n => pupper n+pzero n) :=
    isCoboundedUnder_le_of_le atTop (fun n => add_nonneg measureReal_nonneg measureReal_nonneg)
  have hSum : Filter.limsup (fun n => pupper n+pzero n) atTop ≤ b+a :=
    (limsup_add_le huL huB hzL hzB).trans (add_le_add hupper hzero)
  have hDev : Filter.limsup pdev atTop ≤ b+a := by
    have hLo : IsCoboundedUnder (· ≤ ·) atTop pdev :=
      isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
    exact (limsup_le_limsup (Eventually.of_forall hpointDev) hLo hSumB).trans hSum
  have hpointGood : ∀ n, 1-(pupper n+pzero n) ≤ pgood n := by
    intro n
    let good : Set (Disorder (n+3) μ.maxDegree) :=
      {J | X n J ≠ 0 ∧ sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}
    let bad : Set (Disorder (n+3) μ.maxDegree) :=
      {J | m (n+1)+L ≤ sourceSphereMaximum (n+1) μ Q J} ∪
      {J | X n J=0}
    have huniv : good ∪ bad = Set.univ := by
      ext J
      simp only [good,bad,Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      by_cases hX : X n J=0
      · exact Or.inr (Or.inr hX)
      · by_cases hM : sourceSphereMaximum (n+1) μ Q J < m (n+1)+L
        · exact Or.inl ⟨hX,hM⟩
        · exact Or.inr (Or.inl (le_of_not_gt hM))
    have hone : (1 : ℝ) ≤ pgood n+(pupper n+pzero n) := by
      calc
        (1 : ℝ) = (disorderLaw (n+3) μ.maxDegree).real Set.univ := by simp
        _ = (disorderLaw (n+3) μ.maxDegree).real (good ∪ bad) := by rw [huniv]
        _ ≤ (disorderLaw (n+3) μ.maxDegree).real good+
          (disorderLaw (n+3) μ.maxDegree).real bad := measureReal_union_le _ _
        _ ≤ pgood n+(pupper n+pzero n) := by
          exact add_le_add_right (measureReal_union_le _ _) _
    linarith
  have hLow : IsBoundedUnder (· ≥ ·) atTop
      (fun n => 1-(pupper n+pzero n)) :=
    isBoundedUnder_of ⟨-1,fun n => by
      have h1 : pupper n ≤ 1 := measureReal_le_one
      have h2 : pzero n ≤ 1 := measureReal_le_one
      linarith⟩
  have hGoodB : IsCoboundedUnder (· ≥ ·) atTop pgood :=
    (isBoundedUnder_of ⟨(1 : ℝ),fun n => measureReal_le_one⟩ :
      IsBoundedUnder (· ≤ ·) atTop pgood).isCoboundedUnder_ge
  have hinf := Filter.liminf_le_liminf (Eventually.of_forall hpointGood)
    hLow hGoodB
  have hEq := liminf_const_sub atTop (fun n => pupper n+pzero n) (1 : ℝ)
    hSumB hSumL
  rw [hEq] at hinf
  exact ⟨hDev,(sub_le_sub_left hSum 1).trans hinf⟩

theorem source_pure_actual_retained_joint_ground_tightness_narrow_radial
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ m : ℕ → ℝ, ∃ M C cut η ε δ : ℝ,
      0 < M ∧ 0 < δ ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p : ℝ)*(E-δ) ∧
      (p : ℝ)*δ < 1 ∧
      (∀ᶠ n : ℕ in atTop,
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      (∀ L : ℝ, 0 < L → ∃ B : ℝ, ∀ n : ℕ,
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L) ≤ B) ∧
      ∀ L : ℝ, 0 < L →
        let I n := sourcePureCenteredNormalizedWindow n m E δ (-L) L
        let X n J := (sourceRetainedValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (I n)
          (g/2) C ε η E G J).toReal
        let k := 1+(1-ε)/(cut^2-ε)
        let W := Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L}) atTop ≤
            Real.exp (-(β*x)*L)+k/W ∧
        1-(Real.exp (-(β*x)*L)+k/W) ≤
          Filter.liminf (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
            {J | X n J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨m,M,C,cut,η,ε,δ,D,hM,hδ,hLeft,hpδ,hcenter,
    hcut,hcutOne,hε,hεCut,hεη,hD,
    hUnfiltered,hMean,hMoments,hInputs⟩ :=
    source_pure_actual_retained_same_center_probability_narrow_radial p hp a ha h
  refine ⟨m,M,C,cut,η,ε,δ,hM,hδ,hLeft,hpδ,hcenter,?_,?_⟩
  · intro L hL
    obtain ⟨B,hB⟩ := (hUnfiltered (-L) L (by linarith)).bddAbove_range
    refine ⟨B,?_⟩
    intro n
    constructor
    · exact sourceUnfilteredValueWindowCount_lintegral_lt_top (n+2) (by omega)
        μ h.overlap_range.1 (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
    · exact hB (mem_range_self n)
  intro L hL
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let I (n : ℕ) := sourcePureCenteredNormalizedWindow n m E δ (-L) L
  let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
    (sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (g/2) C ε η E G J).toReal
  let k := 1+(1-ε)/(cut^2-ε)
  let W := Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)
  obtain ⟨hZero,hHalf,hUpper,hBelow⟩ := hInputs L hL
  have hJoint := pure_value_joint_probability_of_limsup μ Q m X L
    (k/W) (Real.exp (-(β*x)*L)) hZero hUpper hBelow
  simpa only [X,I,G,E,g,k,W,add_comm] using hJoint

end SlowEquilibration.PairConditionalDeterminantMoments
