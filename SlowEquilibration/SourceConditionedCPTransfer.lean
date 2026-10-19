-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureRate
public import SlowEquilibration.SourceMixedGeneralCPTransferTimeSup

/-! Pure/non-pure dispatch for the complete source CP transfer. The pure
ordinary posterior entrance estimate remains an explicit premise; there
is no assumption of the desired determinant-weighted transfer or final
separation. The non-pure branch has no additional premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransfer

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalOverlapExponential
open SourceConditionedCPTransferPureRate SourceMixedGeneralCPTransfer
open SourceMixedGeneralCPTransferTimeSup SourceReductionConsumerAsymptotic
open SourceReductionConsumerAsymptoticCounts SourceReductionWeightedCenterScore
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A finite nonnegative mixture with one extreme degree is literally a
positive pure mixture; the conclusion identifies all physical data. -/
theorem pure_representation_of_not_nonpure (μ : FiniteMixture)
    (hnp : ¬ μ.minDegree < μ.maxDegree) :
    ∃ (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c),
      μ = FiniteMixture.pure p hp c hc := by
  have hmin : μ.minDegree ∈ μ.coeff.support := Finset.min'_mem _ _
  have hbounds := μ.degree_bounds hmin
  have hdeg : μ.minDegree = μ.maxDegree := by omega
  let p := μ.minDegree
  have hp : 2 ≤ p := μ.minDegree_ge_two
  have hc : 0 < μ.coeff p := μ.coeff_pos hmin
  have hcoeff : μ.coeff = Finsupp.single p (μ.coeff p) := by
    ext q
    by_cases hq : q = p
    · subst q
      simp
    · have hzero : μ.coeff q = 0 := by
        by_contra hne
        have hh := μ.degree_bounds (Finsupp.mem_support_iff.mpr hne)
        dsimp only [p] at hq
        omega
      simp [hq,hzero]
  refine ⟨p,hp,μ.coeff p,hc,?_⟩
  have hinj : Function.Injective FiniteMixture.coeff := by
    intro ν₁ ν₂ heq
    cases ν₁
    cases ν₂
    cases heq
    rfl
  apply hinj
  exact hcoeff

/-- Only the pure ordinary posterior estimate remains as an explicit
branch premise. This uses genuine value-and-gradient conditioning. -/
def PureBranchEntrance (μ : FiniteMixture) (Q β E : ℝ) : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c),
    μ = FiniteMixture.pure p hp c hc → PureOrdinaryEntranceRate p hp c hc Q β E

/-- A non-pure model requires no pure analytic input. -/
theorem pureBranchEntrance_of_nonpure (μ : FiniteMixture) (Q β E : ℝ)
    (hnp : μ.minDegree < μ.maxDegree) : PureBranchEntrance μ Q β E := by
  intro p hp c hc hμ
  subst μ
  have hmin : (FiniteMixture.pure p hp c hc).minDegree = p := by
    simp [FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p hc.ne']
  have hmax : (FiniteMixture.pure p hp c hc).maxDegree = p := by
    simp [FiniteMixture.maxDegree,FiniteMixture.pure,Finsupp.support_single p hc.ne']
  rw [hmin,hmax] at hnp
  exact False.elim (lt_irrefl p hnp)

/-- The source quantifier order, made reusable without selecting constants
again when assembling the displayed inequality and separation. -/
def UniformCenterCPRate (μ : FiniteMixture) (Q β E b : ℝ) (U : Set ℝ) : Prop :=
  ∃ (a γ : ℝ), 0 < a ∧ a < Real.sqrt Q-b ∧ 0 < γ ∧
    ∀ (m : ℕ → ℝ),
      Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E) →
      (∀ M : ℝ, 0 < M →
        limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) →
    ∀ (M r : ℝ), 0 < M → 1 < r → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U
          (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
          ENNReal.ofReal (C*((n+2:ℕ):ℝ)^(-(((μ.minDegree:ℝ)-2)/2)*(1-1/r)))

theorem source_conditioned_cp_weighted_rate
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k)
    (hpure : PureBranchEntrance μ Q β E) : UniformCenterCPRate μ Q β E b U := by
  by_cases hnp : μ.minDegree < μ.maxDegree
  · exact source_mixed_general_cp_weighted_rate_uniform_center
      μ hd hQ hQ1 hnp hβ hb U hU hgap
  · obtain ⟨p,hp,c,hc,hμ⟩ := pure_representation_of_not_nonpure μ hnp
    have hOrd := hpure p hp c hc hμ
    subst μ
    exact source_pure_general_cp_weighted_rate_of_ordinary
      p hp c hc hd hQ hb U hU hgap hOrd

/-- The entire source proposition, including its common-horizon capture
consequence, for both model classes. The remaining pure analytical premise
is visible in the theorem statement. -/
theorem source_conditioned_cp_transfer
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree) {Q β E b : ℝ}
    (hQ : 0 < Q) (hQ1 : Q ≤ 1) (hβ : 0 ≤ β) (hb : b < Real.sqrt Q)
    (U : Set ℝ) (hU : IsCompact U)
    (hgap : ∀ k ∈ U, 2*Real.sqrt (Q^2*μ.xi2 Q) < k)
    (hpure : PureBranchEntrance μ Q β E) :
    ∃ (a γ : ℝ), 0 < a ∧ a < Real.sqrt Q-b ∧ 0 < γ ∧
      ∀ (m : ℕ → ℝ),
        Tendsto (fun n : ℕ => m n/((n+2:ℕ):ℝ)) atTop (𝓝 E) →
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) →
      (∀ (M r : ℝ), 0 < M → 1 < r → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          (∫ J, originalBandTimeSup μ Q (m n) M b β U
            (exponentialGridHorizon γ (n+2)) J ∂disorderLaw (n+2) μ.maxDegree) ≤
            (∫ J, (actualWindowCenterWeightedHitSum μ Q (m n) M a β U
              (exponentialGridHorizon γ (n+2)) J).toReal ∂disorderLaw (n+2) μ.maxDegree) ∧
          (∫ J, (actualWindowCenterWeightedHitSum μ Q (m n) M a β U
            (exponentialGridHorizon γ (n+2)) J).toReal ∂disorderLaw (n+2) μ.maxDegree) ≤
            C*((n+2:ℕ):ℝ)^(-(((μ.minDegree:ℝ)-2)/2)*(1-1/r))) ∧
      (Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
        ∫ J, originalBandComplementMass μ Q (m n) M b β U J
          ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) →
        VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
          (fun n => originalUniformIntervalDistance μ β
            (exponentialGridHorizon γ (n+2))) (fun _ _ => 1)) := by
  obtain ⟨a,γ,ha,hag,hγ,hRate⟩ := source_conditioned_cp_weighted_rate
    μ hd hQ hQ1 hβ hb U hU hgap hpure
  refine ⟨a,γ,ha,hag,hγ,?_⟩
  intro m hm hcount
  constructor
  · intro M r hM hr
    obtain ⟨C,hC,hRateM⟩ := hRate m hm hcount M r hM hr
    refine ⟨C,hC,?_⟩
    filter_upwards [hRateM] with n hn
    exact (original_real_mean_comparison (by omega) μ Q (m n) M b a β
      hU.isClosed (exponentialGridHorizon γ (n+2)) hag
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) hn).2
  · intro hcapture
    apply source_red_consumer_of_expected_score_tendsto_zero μ Q b a β hU.isClosed
      m (fun n => exponentialGridHorizon γ (n+2)) hag hcapture
    intro M hM
    obtain ⟨C,hC,hRateM⟩ := hRate m hm hcount M 2 hM (by norm_num)
    let α : ℝ := ((μ.minDegree:ℝ)-2)/4
    have hα : 0 < α := by
      have hh : (4:ℝ) ≤ (μ.minDegree:ℝ) := by exact_mod_cast hd
      dsimp [α]
      linarith
    have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    have hreal : Tendsto (fun n : ℕ => C*((n+2:ℕ):ℝ)^(-α)) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop hα).comp hN).const_mul C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using ENNReal.tendsto_ofReal hreal) (.of_forall fun _ => zero_le)
    filter_upwards [hRateM] with n hn
    have hexp : -α = -(((μ.minDegree:ℝ)-2)/2)*(1-1/(2:ℝ)) := by dsimp [α]; ring
    simpa only [hexp,Nat.cast_add,Nat.cast_ofNat] using hn

end SlowEquilibration.SourceConditionedCPTransfer
