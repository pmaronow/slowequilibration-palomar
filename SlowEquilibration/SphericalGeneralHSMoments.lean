-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSubcriticalCentralMoment
public import SlowEquilibration.SphericalHSFeatureSecondMoment
public import SlowEquilibration.SphericalGeneralHSTypicality
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Uniform genuine HS mass and feature moments for every finite mixed
spherical model strictly below its actual static threshold, including degree
two and arbitrary odd components. No tightness or likelihood premise appears. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem centralOverlapMoment_mono {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    centralOverlapMoment N c β δ₁ ≤ centralOverlapMoment N c β δ₂ := by
  have hf : Continuous (fun p : Vector N×Vector N =>
      Real.exp ((N:ℝ)*β^2*covariancePolynomial c (overlap p.1 p.2))) := by
    unfold covariancePolynomial overlap
    fun_prop
  unfold centralOverlapMoment
  apply integral_mono_of_nonneg (.of_forall fun p => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) p)
    (((memLp_spherePair_continuous hN hf 1).integrable le_rfl).indicator (smallOverlap_measurable δ₂))
  exact .of_forall fun p => by
    dsimp only
    by_cases hp : p∈smallOverlap δ₁
    · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (show p∈smallOverlap δ₂ from hp.trans_le hδ)]
    · rw [Set.indicator_of_notMem hp]
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) p

theorem weightedCentralOverlapMoment_mono {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    weightedCentralOverlapMoment N c β δ₁ ≤ weightedCentralOverlapMoment N c β δ₂ := by
  have hf : Continuous (fun p : Vector N×Vector N =>
      (N:ℝ)*|covariancePolynomial c (overlap p.1 p.2)| * 
        Real.exp ((N:ℝ)*β^2*covariancePolynomial c (overlap p.1 p.2))) := by
    unfold covariancePolynomial overlap
    fun_prop
  unfold weightedCentralOverlapMoment
  apply integral_mono_of_nonneg (.of_forall fun p => Set.indicator_nonneg (fun _ _ => by positivity) p)
    (((memLp_spherePair_continuous hN hf 1).integrable le_rfl).indicator (smallOverlap_measurable δ₂))
  exact .of_forall fun p => by
    dsimp only
    by_cases hp : p∈smallOverlap δ₁
    · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (show p∈smallOverlap δ₂ from hp.trans_le hδ)]
    · rw [Set.indicator_of_notMem hp]
      exact Set.indicator_nonneg (fun _ _ => by positivity) p

/-- All probabilistic inputs to the degree-two lower-tail argument are
literal proved moments of the physical HS truncation and tensor feature. -/
theorem general_hs_normalized_moments (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    ∃δ η B D : ℝ,δ∈Ioo (0:ℝ) 1 ∧ 0<η ∧ 0<B ∧ 0 ≤ D ∧
      ∀ᶠ n : ℕ in atTop,
        let N := n+1
        let c := mixtureCoefficients μ
        let A := annealedExponent N c β
        let T := hsTruncation (N:=N) c β δ (A-(N:ℝ)*η)
        (1/2:ℝ) ≤ (∫J,Real.exp (-A)*truncatedPartition c β T J ∂disorderLaw N μ.maxDegree) ∧
        (∫J,(Real.exp (-A)*truncatedPartition c β T J)^2 ∂disorderLaw N μ.maxDegree) ≤ B ∧
        (∫J,‖Real.exp (-A) • truncatedFeatureMean c β T J‖^2 ∂disorderLaw N μ.maxDegree) ≤ D := by
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hcentral⟩ := centralOverlapMoment_eventually_bounded μ hβ hβs
  obtain ⟨δ₂,hδ₂,C₂,hC₂,hweighted⟩ := weightedCentralOverlapMoment_eventually_bounded μ hβ hβs
  let δ := min δ₁ δ₂
  have hδ : δ∈Ioo (0:ℝ) 1 := ⟨lt_min hδ₁.1 hδ₂.1,(min_le_left _ _).trans_lt hδ₁.2⟩
  obtain ⟨η,hη,hhalf⟩ := general_hs_planted_half_eventually μ hβ hβs hδ
  have hNlim : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htail : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)*Real.exp (-((n+1:ℕ):ℝ)*η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) η hη).comp hNlim using 1
    ext n
    simp only [Function.comp_apply,Real.rpow_one,mul_comm,mul_neg]
  refine ⟨δ,η,C₁+1,β^2*C₂+β^2*μ.xi 1,hδ,hη,by positivity,
    add_nonneg (mul_nonneg (sq_nonneg β) hC₂.le) (mul_nonneg (sq_nonneg β) (μ.xi_pos zero_lt_one).le),?_⟩
  have hcentral' := (tendsto_add_atTop_nat 1).eventually hcentral
  have hweighted' := (tendsto_add_atTop_nat 1).eventually hweighted
  filter_upwards [hhalf,hcentral',hweighted',htail.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with n hhalf hcN hwN htN
  let N := n+1
  let c := mixtureCoefficients μ
  let A := annealedExponent N c β
  let T := hsTruncation (N:=N) c β δ (A-(N:ℝ)*η)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hc := mixtureCoefficients_nonnegative μ
  have hT := hsTruncation_measurable (N:=N) c β δ (A-(N:ℝ)*η)
  have hcBound : centralOverlapMoment N c β δ ≤ C₁ :=
    (centralOverlapMoment_mono hN c β (min_le_left _ _)).trans hcN
  have hwBound : weightedCentralOverlapMoment N c β δ ≤ C₂ := by
    have hh : weightedCentralOverlapMoment N c β δ₂ ≤ C₂ := by
      simpa only [N,c,weightedCentralOverlapMoment,covariancePolynomial_mixture] using hwN
    exact (weightedCentralOverlapMoment_mono hN c β (min_le_right _ _)).trans hh
  have hmean : (∫J,Real.exp (-A)*truncatedPartition c β T J ∂disorderLaw N μ.maxDegree)=
      (plantedLaw (N:=N) c β).real T := by
    rw [integral_const_mul,expected_truncatedPartition hN c hc β hT]
    change Real.exp (-A)*(Real.exp A*(plantedLaw (N:=N) c β).real T)=_
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  have hsecond := normalized_hsTruncatedPartition_second_moment_le hN c hc β δ η
  have hfeature := normalized_hsTruncatedFeatureMean_second_moment_le hN c hc hβ.le δ η
  have hexp : Real.exp (-(N:ℝ)*η) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) hη.le)
  have hfeatureTail : β^2*(N:ℝ)*covariancePolynomial c 1*Real.exp (-(N:ℝ)*η) ≤ β^2*μ.xi 1 := by
    rw [covariancePolynomial_mixture]
    have hh := mul_le_mul_of_nonneg_left htN.le
      (mul_nonneg (sq_nonneg β) (μ.xi_pos zero_lt_one).le)
    convert hh using 1 <;> ring
  change (1/2:ℝ) ≤ _ ∧ _ ≤ C₁+1 ∧ _ ≤ β^2*C₂+β^2*μ.xi 1
  refine ⟨?_,?_,?_⟩
  · rw [hmean]
    exact hhalf
  · exact hsecond.trans (add_le_add hcBound hexp)
  · exact hfeature.trans (add_le_add (mul_le_mul_of_nonneg_left hwBound (sq_nonneg β)) hfeatureTail)

end SlowEquilibration.SphericalModel
