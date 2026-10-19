-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedMaximumGeometry
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The source 11.14 upper-tail statement is transferred to the same
dimension index as the literal retained count. The fixed-window joint
probability then follows from the two actual original-disorder events. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem sourceSphereMaximum_centered_probability_limsup_shift
    (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q *
      (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x)))
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) (t : ℝ) :
    Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
      {J | d.center (n+1)+t ≤ sourceSphereMaximum (n+1) μ Q J}) atTop ≤
        Real.exp (-(β*x)*t) := by
  obtain ⟨c,hc,hbound⟩ := sourceSphereMaximum_probability_le_tail_and_error
    μ h hnp hL hm hA3
  have hAbove := normalized_source_center_above_lower_energy
    (mul_pos h.beta_pos h.weight_range.1) d.log_constant_pos.le hδ
    d.center d.logarithmic_correction t
  have hDim : Tendsto (fun n : ℕ => ((n+3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c*(n+3 : ℕ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (hDim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hUpper : Tendsto (fun n : ℕ =>
      sourceMaximumEnergyTail (n+1) μ Q (Ioo L R) (d.center (n+1)+t)+
        Real.exp (-c*(n+3 : ℕ))) atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    simpa only [add_zero,Function.comp_def] using
      ((d.tail_limit t).comp (tendsto_add_atTop_nat 1)).add hExp
  have hProb : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+3) μ.maxDegree).real
        {J | d.center (n+1)+t ≤ sourceSphereMaximum (n+1) μ Q J} ≤
      sourceMaximumEnergyTail (n+1) μ Q (Ioo L R) (d.center (n+1)+t)+
        Real.exp (-c*(n+3 : ℕ)) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hbound,
      (tendsto_add_atTop_nat 1).eventually hAbove] with n hn hhigh
    exact hn _ hhigh
  have hCobounded := isCoboundedUnder_le_of_le atTop
    (fun n : ℕ => measureReal_nonneg (μ := disorderLaw (n+3) μ.maxDegree)
      (s := {J | d.center (n+1)+t ≤ sourceSphereMaximum (n+1) μ Q J}))
  exact (limsup_le_limsup hProb hCobounded hUpper.isBoundedUnder_le).trans_eq
    hUpper.limsup_eq

/-- Fixed-window maximum tightness from the *actual* zero-count and upper
tail probabilities. The only probabilistic premises are the two limsup
estimates, while the lower-tail event implication is proved above from the
literal score window. -/
theorem source_retained_window_maximum_tightness_of_limsup
    (μ : FiniteMixture) (Q : ℝ) (m : ℕ → ℝ) (U : Set ℝ)
    (κ C ε η E G t a b : ℝ)
    (hzero : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
          κ C ε η E G J).toReal = 0}) atTop ≤ a)
    (hupper : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | m n+t ≤ sourceSphereMaximum (n+1) μ Q J}) atTop ≤ b) :
    Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | |sourceSphereMaximum (n+1) μ Q J-m n| > t}) atTop ≤ b+a := by
  let pzero (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | (sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
      κ C ε η E G J).toReal = 0}
  let pupper (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | m n+t ≤ sourceSphereMaximum (n+1) μ Q J}
  let pdev (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | |sourceSphereMaximum (n+1) μ Q J-m n| > t}
  have hpoint : ∀ n, pdev n ≤ pupper n+pzero n := by
    intro n
    have hsubset : {J : Disorder (n+3) μ.maxDegree |
        |sourceSphereMaximum (n+1) μ Q J-m n| > t} ⊆
      {J | m n+t ≤ sourceSphereMaximum (n+1) μ Q J} ∪
      {J | (sourceRetainedScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
        κ C ε η E G J).toReal = 0} := by
      intro J hJ
      change t < |sourceSphereMaximum (n+1) μ Q J-m n| at hJ
      rcases (lt_abs.mp hJ) with hhigh | hlow
      · left
        change m n+t ≤ sourceSphereMaximum (n+1) μ Q J
        linarith
      · right
        have hbelow : sourceSphereMaximum (n+1) μ Q J < m n-t := by linarith
        change (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
          κ C ε η E G J).toReal = 0
        rw [source_retained_window_zero_of_max_below n μ Q (m n-t) (m n+t)
          κ C ε η E G U J hbelow]
        rfl
    exact (measureReal_mono hsubset (by finiteness)).trans
      (measureReal_union_le _ _)
  have hLo : IsCoboundedUnder (· ≤ ·) atTop pdev :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
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
  have hSum : Filter.limsup (fun n => pupper n+pzero n) atTop ≤
      Filter.limsup pupper atTop+Filter.limsup pzero atTop :=
    limsup_add_le huL huB hzL hzB
  have hDev : Filter.limsup pdev atTop ≤
      Filter.limsup (fun n => pupper n+pzero n) atTop :=
    limsup_le_limsup (Eventually.of_forall hpoint) hLo hSumB
  exact (hDev.trans hSum).trans (add_le_add hupper hzero)

/-- Retained-point existence jointly with an upper-bounded global maximum.
The real measure argument avoids any extra measurability hypothesis on the
critical-set enumeration. -/
theorem source_retained_window_joint_probability_of_limsup
    (μ : FiniteMixture) (Q : ℝ) (m : ℕ → ℝ) (U : Set ℝ)
    (κ C ε η E G t a b : ℝ)
    (hzero : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
          κ C ε η E G J).toReal = 0}) atTop ≤ a)
    (hupper : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | m n+t ≤ sourceSphereMaximum (n+1) μ Q J}) atTop ≤ b) :
    1-(b+a) ≤ Filter.liminf (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
          κ C ε η E G J).toReal ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J < m n+t}) atTop := by
  let pzero (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | (sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
      κ C ε η E G J).toReal = 0}
  let pupper (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | m n+t ≤ sourceSphereMaximum (n+1) μ Q J}
  let pgood (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | (sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
      κ C ε η E G J).toReal ≠ 0 ∧
      sourceSphereMaximum (n+1) μ Q J < m n+t}
  have hpoint : ∀ n, 1-(pupper n+pzero n) ≤ pgood n := by
    intro n
    let good : Set (Disorder (n+3) μ.maxDegree) :=
      {J | (sourceRetainedScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
        κ C ε η E G J).toReal ≠ 0 ∧
        sourceSphereMaximum (n+1) μ Q J < m n+t}
    let bad : Set (Disorder (n+3) μ.maxDegree) :=
      {J | m n+t ≤ sourceSphereMaximum (n+1) μ Q J} ∪
      {J | (sourceRetainedScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
        κ C ε η E G J).toReal = 0}
    have huniv : good ∪ bad = Set.univ := by
      ext J
      simp only [good,bad,Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      by_cases hX : (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3) (Icc (m n-t) (m n+t)) U)
          κ C ε η E G J).toReal = 0
      · exact Or.inr (Or.inr hX)
      · by_cases hM : sourceSphereMaximum (n+1) μ Q J < m n+t
        · exact Or.inl ⟨hX,hM⟩
        · exact Or.inr (Or.inl (le_of_not_gt hM))
    have hone : (1:ℝ) ≤ pgood n+(pupper n+pzero n) := by
      calc
        (1:ℝ) = (disorderLaw (n+3) μ.maxDegree).real Set.univ := by simp
        _ = (disorderLaw (n+3) μ.maxDegree).real (good ∪ bad) := by rw [huniv]
        _ ≤ (disorderLaw (n+3) μ.maxDegree).real good+
          (disorderLaw (n+3) μ.maxDegree).real bad := measureReal_union_le _ _
        _ ≤ pgood n+(pupper n+pzero n) := by
          exact add_le_add_right (measureReal_union_le _ _) _
    linarith
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
  have hLow : IsBoundedUnder (· ≥ ·) atTop
      (fun n => 1-(pupper n+pzero n)) :=
    isBoundedUnder_of ⟨-1,fun n => by
      have h1 : pupper n ≤ 1 := measureReal_le_one
      have h2 : pzero n ≤ 1 := measureReal_le_one
      linarith⟩
  have hGoodB : IsCoboundedUnder (· ≥ ·) atTop pgood :=
    (isBoundedUnder_of ⟨(1:ℝ),fun n => measureReal_le_one⟩ :
      IsBoundedUnder (· ≤ ·) atTop pgood).isCoboundedUnder_ge
  have hinf := Filter.liminf_le_liminf (Eventually.of_forall hpoint)
    hLow hGoodB
  have hEq := liminf_const_sub atTop (fun n => pupper n+pzero n) (1:ℝ)
    hSumB hSumL
  rw [hEq] at hinf
  exact (sub_le_sub_left hSum 1).trans hinf

/-- Source 11.14's centered global-maximum tightness for the original
mixed tensor field, with its center and selection chosen internally. -/
theorem source_mixed_actual_canonical_ground_tightness
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
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
            Filter.limsup (fun n : ℕ =>
              (disorderLaw (n+3) μ.maxDegree).real
                {J | |sourceSphereMaximum (n+1) μ Q J-d.center (n+1)| > t}) atTop ≤
              Real.exp (-(β*x)*t)+
                (1+(1-ε)/(cut^2-ε))/
                  (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t)) := by
  dsimp only
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hall⟩ :=
    source_mixed_actual_retained_canonical_probability_limsup μ h hnp hd hδMax
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hm : markK μ β Q ∈ Ioo L R := ⟨hL,hR⟩
  have hκ : 0 < sourceMarkedLeastCurvature μ Q :=
    sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by omega) hnp
  have hu : 0 < sourceRadialClearance μ β Q (Ioo L R) :=
    sourceRadialClearance_pos μ hm
  let δ := sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
  have hδ : 0 < δ := by
    dsimp [δ]
    have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
    positivity
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hwin⟩ := hall hα hHalf
  refine ⟨D,hD,?_⟩
  intro t ht
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let a := (1+(1-ε)/(cut^2-ε))/
    (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))
  have hZero := (hwin t ht).1
  have hUpper := sourceSphereMaximum_centered_probability_limsup_shift
    μ h hnp hEdge hm hδ (le_refl _) d t
  have hTight := source_retained_window_maximum_tightness_of_limsup
    μ Q (fun n => d.center (n+1)) (Ioo L R)
    (g/2) C ε η E G t a (Real.exp (-(β*x)*t)) hZero hUpper
  simpa only [a,G,E,g] using hTight

/-- Source 11.14's joint fixed-window existence/upper-ground bound for the
literal ordinary set of critical points, including both antipodal points
when the model is even. -/
theorem source_mixed_actual_canonical_joint_ground_probability
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
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
            1-(Real.exp (-(β*x)*t)+
              (1+(1-ε)/(cut^2-ε))/
                (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))) ≤
              Filter.liminf (fun n : ℕ =>
                (disorderLaw (n+3) μ.maxDegree).real
                  {J | (Set.Nonempty {u : Vector (n+3) |
                    ‖u‖^2=(n+3:ℕ) ∧
                    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
                    field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
                      Icc (d.center (n+1)-t) (d.center (n+1)+t) ∧
                    actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R}) ∧
                    sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop := by
  dsimp only
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hall⟩ :=
    source_mixed_actual_retained_canonical_probability_limsup μ h hnp hd hδMax
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hm : markK μ β Q ∈ Ioo L R := ⟨hL,hR⟩
  have hκ : 0 < sourceMarkedLeastCurvature μ Q :=
    sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by omega) hnp
  have hu : 0 < sourceRadialClearance μ β Q (Ioo L R) :=
    sourceRadialClearance_pos μ hm
  let δ := sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
  have hδ : 0 < δ := by
    dsimp [δ]
    have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
    positivity
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hwin⟩ := hall hα hHalf
  refine ⟨D,hD,?_⟩
  intro t ht
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let a := (1+(1-ε)/(cut^2-ε))/
    (Real.exp ((β*x)*t)-Real.exp (-(β*x)*t))
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
    {J | (Set.Nonempty {u : Vector (n+3) |
      ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
        Icc (d.center (n+1)-t) (d.center (n+1)+t) ∧
      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R}) ∧
      sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}
  have hpoint : ∀ n, pRet n ≤ pCrit n := by
    intro n
    apply measureReal_mono
    · intro J hJ
      refine ⟨source_retained_nonzero_critical_window_nonempty n μ Q
        (d.center (n+1)-t) (d.center (n+1)+t) (g/2) C ε η E G
        (Ioo L R) J hJ.1,hJ.2⟩
    · finiteness
  have hRetBound : IsBoundedUnder (· ≥ ·) atTop pRet :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hCritCob : IsCoboundedUnder (· ≥ ·) atTop pCrit :=
    (isBoundedUnder_of ⟨(1:ℝ),fun n => measureReal_le_one⟩ :
      IsBoundedUnder (· ≤ ·) atTop pCrit).isCoboundedUnder_ge
  have hTransfer := Filter.liminf_le_liminf (Eventually.of_forall hpoint)
    hRetBound hCritCob
  have hLow := hJoint.trans hTransfer
  simpa only [a,G,E,g] using hLow

end
end SlowEquilibration.PairConditionalDeterminantMoments
