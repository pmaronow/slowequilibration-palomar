-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureHolder
public import SlowEquilibration.SourceMixedGeneralCPTransfer
public import SlowEquilibration.ConditionedEntrancePureTruePosteriorLaw

/-! The pure branch of source CP transfer. Its remaining analytical input
is stated explicitly as the ordinary whole-field, value-and-gradient
posterior entrance rate on one compact normalized energy interval. All
determinant weighting and original-window count transfer are proved here. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureRate

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open ConditionedEntrance ConditionedDeterminantMoments
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open SourceConditionedCPTransferPureHolder SourceCriticalEntranceRateNumeric
open SourceMixedGeneralCPTransfer SourceMixedGeneralCPTransferMarks
open SourceMixedCenteredTrueEntranceTransfer SourceReductionWeightedScoreMarkedCount
open SourceReductionWeightedCenterScore SourceReductionConsumerAsymptoticCounts
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Explicit unresolved ordinary pure entrance input. Conditioning is on
the whole original disorder at value `N*e` and zero tangent gradient. The
cap and horizon precede the dimension and every later fixed window. -/
def PureOrdinaryEntranceRate (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q β E : ℝ) : Prop :=
  let μ := FiniteMixture.pure p hp c hc
  ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
    ∃ (γ decay C : ℝ), 0 < γ ∧ 0 < decay ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ)) (e : ℝ),
          |e| ≤ |E|+2 →
          (∫ J, originalTrueCapHitProbability μ β
            (exponentialGridHorizon γ (n+2)) a u J
            ∂pureLaw p hp c hc Q u hu e) ≤
          C*(((n+2:ℕ):ℝ)^(1-(μ.minDegree:ℝ)/2)+
            ((n+2:ℕ):ℝ)^(3-(μ.minDegree:ℝ)))+
            Real.exp (-decay*((n+2:ℕ):ℝ))

theorem source_pure_general_cp_weighted_rate_of_ordinary
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q β E b : ℝ} (hd : 4 ≤ (FiniteMixture.pure p hp c hc).minDegree)
    (hQ : 0 < Q) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp c hc).xi2 Q) < k)
    (hordinary : PureOrdinaryEntranceRate p hp c hc Q β E) :
    let μ := FiniteMixture.pure p hp c hc
    ∃ (a γ : ℝ), 0 < a ∧ a < Real.sqrt Q-b ∧ 0 < γ ∧
      ∀ (m : ℕ → ℝ),
        Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E) →
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) →
      ∀ (M r : ℝ), 0 < M → 1 < r → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          (∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U
            (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
            ENNReal.ofReal (C*((n+2:ℕ):ℝ)^
              (-(((μ.minDegree:ℝ)-2)/2)*(1-1/r))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  obtain ⟨g,hg,hgU⟩ := compact_strict_gap_uniform hU _ hgap
  obtain ⟨Z,hZ,hUZ⟩ := hU.isBounded.exists_pos_norm_le
  obtain ⟨aStar,hStar,hScales⟩ := hordinary
  let a := min aStar ((Real.sqrt Q-b)/2)
  have ha : 0 < a := by dsimp [a]; exact lt_min hStar (by linarith)
  have haStar : a ≤ aStar := min_le_left _ _
  have haGap : a < Real.sqrt Q-b := by
    have hh : a ≤ (Real.sqrt Q-b)/2 := min_le_right _ _
    linarith
  obtain ⟨γ,decay,C,hγ,hdecay,hC,hRate⟩ := hScales ha haStar
  refine ⟨a,γ,ha,haGap,hγ,?_⟩
  intro m hm hcount M r hM hr
  obtain ⟨B,hB,hBound⟩ := eventually_bounded_of_limsup_lt_top _ (hcount M hM)
  obtain ⟨Cdet,hCdet,hTransfer⟩ := pure_critical_entrance_holder_transfer_uniform
    p hp c hc hQ (Z := Z) (r := r) hg hr
  let K (n : ℕ) := physicalEnergyWindow (n+2) (Icc (m n-M) (m n+M)) U
  let ψ (n : ℕ) (J : Disorder (n+2) μ.maxDegree) (u : Vector (n+2)) :=
    originalTrueCapHitProbability μ β (exponentialGridHorizon γ (n+2)) a u J
  have hK (n : ℕ) : MeasurableSet (K n) :=
    rectangularScoreWindow_measurable _ _
      (measurableSet_Icc.preimage (measurable_const_mul _)) hU.isClosed.measurableSet
  have hψ (n : ℕ) : Measurable (fun z : Disorder (n+2) μ.maxDegree × Vector (n+2) =>
      ψ n z.1 z.2) :=
    SourceMixedCenteredTrueEntranceTransfer.originalTrueCapHitProbability_joint_measurable
      μ β (exponentialGridHorizon γ (n+2)) a
  have hψ01 (n : ℕ) (J : Disorder (n+2) μ.maxDegree) (u : Vector (n+2)) :
      0 ≤ ψ n J u ∧ ψ n J u ≤ 1 :=
    originalTrueCapHitProbability_mem_unit μ β (exponentialGridHorizon γ (n+2)) a u J
  have hgapK (n : ℕ) (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ K n) :
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 ∧ z 1 ≤ Z :=
    ⟨hgU (z 1) hz.2,(le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hUZ (z 1) hz.2)⟩
  have hdReal : (4:ℝ) ≤ (μ.minDegree:ℝ) := by exact_mod_cast hd
  have hPower := (tendsto_add_atTop_nat 1).eventually
    (entrance_source_rate_le_single_power_eventually hdReal hdecay hC.le)
  refine ⟨Cdet^(1/r)*(2*C+1)^(1-1/r)*B,by positivity,?_⟩
  filter_upwards [hRate,hBound,normalized_center_window_bounds m E hm M,hPower]
    with n hRateN hBoundN hWindow hPowerN
  let x : ℝ := ((n+2:ℕ):ℝ)
  let α : ℝ := ((μ.minDegree:ℝ)-2)/2
  let s : ℝ := 1-1/r
  let q : ℝ := (2*C+1)*x^(-α)
  have hx : 0 < x := by dsimp [x]; positivity
  have hC1 : 0 ≤ 2*C+1 := by linarith
  have hq : 0 ≤ q := mul_nonneg hC1 (Real.rpow_nonneg hx.le _)
  have hNum : C*(x^(1-(μ.minDegree:ℝ)/2)+x^(3-(μ.minDegree:ℝ)))+
      Real.exp (-decay*x) ≤ q := by
    simpa only [x,q,α,show n+1+1=n+2 by omega,
      show -((μ.minDegree:ℝ)-2)/2 = -(((μ.minDegree:ℝ)-2)/2) by ring] using hPowerN
  have hOrd (u : Vector (n+2)) (hu : ‖u‖^2=((n+2:ℕ):ℝ))
      (e : ℝ) (he : pureScoreLine p e ∈ K n) :
      (∫ J, ψ n J u ∂pureLaw p hp c hc Q u hu e) ≤ q := by
    have heWindow : x*e ∈ Icc (m n-M) (m n+M) := by
      simpa [K,physicalEnergyWindow,rectangularScoreWindow,pureScoreLine,x] using he.1
    have hWindow' : x*(E-1) ≤ m n-M ∧ m n+M ≤ x*(E+1) := hWindow
    have heLo : E-1 ≤ e := by nlinarith [hWindow'.1,heWindow.1]
    have heHi : e ≤ E+1 := by nlinarith [hWindow'.2,heWindow.2]
    have heAbs : |e| ≤ |E|+2 := by
      apply abs_le.mpr
      constructor <;> nlinarith [neg_le_abs E,le_abs_self E]
    exact (hRateN u hu e heAbs).trans hNum
  have hMark := hTransfer n (K n) (hK n) (ψ n) (hψ n)
    (hψ01 n) q hq (hgapK n) hOrd
  have hFactor : 0 ≤ Cdet^(1/r)*q^s :=
    mul_nonneg (Real.rpow_nonneg hCdet.le _) (Real.rpow_nonneg hq _)
  have hbound := hMark.trans
    (mul_le_mul_right hBoundN (ENNReal.ofReal (Cdet^(1/r)*q^s)))
  rw [← ENNReal.ofReal_mul hFactor] at hbound
  have hidentity : (Cdet^(1/r)*q^s)*B =
      (Cdet^(1/r)*(2*C+1)^s*B)*x^(-α*s) := by
    dsimp only [q]
    rw [Real.mul_rpow hC1 (Real.rpow_nonneg hx.le _),Real.rpow_mul hx.le]
    ring
  rw [hidentity] at hbound
  rw [lintegral_congr_ae
    (actualWindowCenterWeightedHitSum_ae_eq_actualScoreWindowCount
      n μ hQ (m n) M a β U (exponentialGridHorizon γ (n+2)))]
  simpa only [x,α,s,K] using hbound

end SlowEquilibration.SourceConditionedCPTransferPureRate
