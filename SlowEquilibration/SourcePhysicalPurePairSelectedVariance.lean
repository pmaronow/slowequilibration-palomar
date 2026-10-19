-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPureIntegratedSelectedSecondMoment
public import SlowEquilibration.SourcePhysicalPairSelectedVariance
public import SlowEquilibration.SourcePhysicalPurePairRetainedSharpBounds

/-! Literal proper-pure retained value-window second moment and variance.
The selected count is the actual finite critical-point cardinality, and
the pair mean is the actual ordered-pair integral on the original sphere. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalPairMarkedWindows
open scoped ENNReal ProbabilityTheory Topology
set_option autoImplicit false
set_option maxHeartbeats 900000

def sourceRetainedValueWindowSecondMoment (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (I : Set ℝ) (κ C ε η E G : ℝ) : ℝ :=
  (∫⁻ J, (sourceRetainedValueWindowCount n
    (centerCoefficients (mixtureCoefficients μ) Q) I κ C ε η E G J)^2
    ∂disorderLaw (n+1) μ.maxDegree).toReal

/-- A raw value-window pair bound makes the retained pair integral finite;
this must be established before converting its mean to a real number. -/
theorem source_retained_pure_pair_lintegral_lt_top_of_unfiltered_bound
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (ρ cut : ℝ) (I : Set ℝ) (κ C ε η E G A : ℝ)
    (hpair : let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J, actualSpherePairCount n c ρ
        (actualValuePairWindowMark c I cut (fun _ _ => 1)) J
        ∂disorderLaw (n+1) μ.maxDegree) ≤
        ENNReal.ofReal A *
          (∫⁻ J, actualValueWindowCount n c I (fun _ _ => 1) J
            ∂disorderLaw (n+1) μ.maxDegree)^2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J
      ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
  dsimp only at hpair ⊢
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hB := sourceUnfilteredValueWindowCount_lintegral_lt_top n hn μ hQ I
  have hR : ENNReal.ofReal A *
      (∫⁻ J, actualValueWindowCount n c I (fun _ _ => 1) J
        ∂disorderLaw (n+1) μ.maxDegree)^2 < ⊤ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB.ne))
  calc
    _ ≤ ∫⁻ J, actualSpherePairCount n c ρ
        (actualValuePairWindowMark c I cut (fun _ _ => 1)) J
        ∂disorderLaw (n+1) μ.maxDegree :=
      source_pure_actual_pair_filter_count_le n c ρ cut I
        (sourceSelectionPairMark c κ C ε η E G)
        (sourceSelectionPairMark_le_one c κ C ε η E G)
    _ ≤ ENNReal.ofReal A *
        (∫⁻ J, actualValueWindowCount n c I (fun _ _ => 1) J
          ∂disorderLaw (n+1) μ.maxDegree)^2 := hpair
    _ < ⊤ := hR

/-- The exact proper-pure Kac--Rice mean and selected second-moment
decomposition imply the printed real variance bound, provided the
unfiltered local pair estimate supplies pair-integral finiteness. -/
theorem source_actual_retained_pure_count_moments_of_pair_bound
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {κ C ε η E G ω cut ρ err : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hcut : 0 < cut) (hcutOne : cut ≤ 1) (hε : ε < cut^2)
    (hcutρ : cut ≤ ρ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hwindow : ∀ z ∈ I, E-ω ≤ z)
    (hpairFinite :
      (∫⁻ J, sourceRetainedPurePairCount n
        (centerCoefficients (mixtureCoefficients μ) Q) ρ cut I κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤)
    (hpairBound : sourceRetainedPurePairMean n μ Q ρ cut I κ C ε η E G ≤
      (1+err)*(sourceRetainedValueWindowMean n μ Q I κ C ε η E G)^2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := sourceRetainedValueWindowMean n μ Q I κ C ε η E G
    let X := fun J => (sourceRetainedValueWindowCount n c I κ C ε η E G J).toReal
    (∫ J, X J ∂disorderLaw (n+1) μ.maxDegree) = a ∧
      MemLp X 2 (disorderLaw (n+1) μ.maxDegree) ∧
      sourceRetainedValueWindowSecondMoment n μ Q I κ C ε η E G ≤
        (1+err)*a^2+(1+(1-ε)/(cut^2-ε))*a ∧
      ProbabilityTheory.variance X (disorderLaw (n+1) μ.maxDegree) ≤
        err*a^2+(1+(1-ε)/(cut^2-ε))*a := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let k := 1+(1-ε)/(cut^2-ε)
  have hcutSq : cut^2 ≤ 1 := by
    nlinarith [mul_nonneg hcut.le (sub_nonneg.mpr hcutOne)]
  have hnum : 0 ≤ 1-ε := by linarith
  have hden : 0 < cut^2-ε := sub_pos.mpr hε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hMeas :=
    (sourceRetainedValueWindowCount_kacRice n hn μ hQ I hI κ C ε η E G).1
  have hCountFiniteAe : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      sourceRetainedValueWindowCount n c I κ C ε η E G J < ⊤ := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
    rw [sourceRetainedValueWindowCount_eq_selected_set_card
      c J I κ C ε η E G hfinite]
    simp
  have hCountFinite :
      (∫⁻ J, sourceRetainedValueWindowCount n c I κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
    apply lt_of_le_of_lt _
      (sourceUnfilteredValueWindowCount_lintegral_lt_top n hn μ hQ I)
    exact lintegral_mono (sourceRetainedValueWindowCount_le_unfiltered
      n c I κ C ε η E G)
  have hLinearFinite : ENNReal.ofReal k *
      (∫⁻ J, sourceRetainedValueWindowCount n c I κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCountFinite.ne)
  have hSecondBound :=
    source_actual_retained_pure_count_integrated_second_moment_bound
      n hn μ hQ hκ hC hη hωG hcut hcutOne hε hcutρ I hI hwindow
  have hSecondFinite :
      (∫⁻ J, (sourceRetainedValueWindowCount n c I κ C ε η E G J)^2
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_of_le_of_lt hSecondBound
      (ENNReal.add_lt_top.mpr ⟨hpairFinite,hLinearFinite⟩)
  have hMean : (∫ J, (sourceRetainedValueWindowCount n c I κ C ε η E G J).toReal
      ∂disorderLaw (n+1) μ.maxDegree) =
      sourceRetainedValueWindowMean n μ Q I κ C ε η E G := by
    simpa only [sourceRetainedValueWindowMean] using
      (integral_toReal hMeas hCountFiniteAe)
  have hLp := source_memLp_two_of_finite_ennreal_second_lintegral
    (disorderLaw (n+1) μ.maxDegree)
    (sourceRetainedValueWindowCount n c I κ C ε η E G)
    hMeas hCountFiniteAe hSecondFinite
  have hReal := ENNReal.toReal_mono
    (ENNReal.add_lt_top.mpr ⟨hpairFinite,hLinearFinite⟩).ne hSecondBound
  change _ ≤ (_ + ENNReal.ofReal k * _).toReal at hReal
  rw [ENNReal.toReal_add hpairFinite.ne hLinearFinite.ne,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hk] at hReal
  change sourceRetainedValueWindowSecondMoment n μ Q I κ C ε η E G ≤
    sourceRetainedPurePairMean n μ Q ρ cut I κ C ε η E G+
      k*sourceRetainedValueWindowMean n μ Q I κ C ε η E G at hReal
  have hSecond : sourceRetainedValueWindowSecondMoment n μ Q I κ C ε η E G ≤
      (1+err)*(sourceRetainedValueWindowMean n μ Q I κ C ε η E G)^2+
      k*sourceRetainedValueWindowMean n μ Q I κ C ε η E G :=
    hReal.trans (add_le_add_left hpairBound _)
  have hVarEq := source_variance_of_finite_ennreal_count
    (disorderLaw (n+1) μ.maxDegree)
    (sourceRetainedValueWindowCount n c I κ C ε η E G)
    hMeas hCountFiniteAe hSecondFinite
  have hVar : ProbabilityTheory.variance
      (fun J => (sourceRetainedValueWindowCount n c I κ C ε η E G J).toReal)
      (disorderLaw (n+1) μ.maxDegree) =
      sourceRetainedValueWindowSecondMoment n μ Q I κ C ε η E G-
        (sourceRetainedValueWindowMean n μ Q I κ C ε η E G)^2 := by
    simpa only [sourceRetainedValueWindowSecondMoment,
      sourceRetainedValueWindowMean] using hVarEq
  refine ⟨hMean,hLp,hSecond,?_⟩
  rw [hVar]
  nlinarith [hSecond]

end
end SlowEquilibration.PairConditionalDeterminantMoments
