-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedHighEnergyAllHigh
public import SlowEquilibration.SourcePhysicalPairPosteriorSphereRegularity
public import SlowEquilibration.SourcePhysicalPairSphereCriticalCollar

/-! All clauses of manuscript `prop:mo-all-high` for a certified non-pure
finite mixture. The base interval fixes the manuscript margin, a single full
covariant regularity constant, and the exact overlap collar before the smaller
radial interval and energy width are chosen. The original-disorder event
exports the upper energy cutoff as well as the radial mark, Hessian margin,
full D_N bound, and exclusion of every other critical point in the collar. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.MixedAllHighComplete

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet SphericalForm SphereHessian
open PairConditionalDeterminantMoments ConditionedDeterminantMoments
open SphericalHessianMarginEvents SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalLightBandMark SphericalTAPCriticalLightCountTransfer
open scoped ENNReal Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual determinant-weighted posterior failure probability, uniformly
over every energy and a compact radial interval above the spectral edge. -/
private lemma posterior_bad_margin_weight
    (μ : FiniteMixture) {Q κ Z : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hκ : 0 < κ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let d := (κ / Real.sqrt (Q^2 * μ.xi2 Q))^2 / (16 * Real.pi^2)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2 = (n+2 : ℕ))
        (z : EuclideanSpace ℝ (Fin 2)),
        2 * Real.sqrt (Q^2 * μ.xi2 Q) + 2*κ ≤ z 1 → z 1 ≤ Z →
        (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
          hessianMarginFailureMark c κ J u ∂mixedConditionedLaw c u hu z) ≤
        ENNReal.ofReal (C * Real.exp (-d*(n+1 : ℕ)/2)) *
          (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det|
            ∂mixedConditionedLaw c u hu z) := by
  classical
  intro c d
  obtain ⟨K, hK, hMom⟩ := mixed_conditioned_determinant_moments μ hQ hnp
    (g := 2*κ) (Z := Z) (r := 2) (by positivity) (by norm_num)
  refine ⟨K^(1/(2 : ℝ)), Real.rpow_pos_of_pos hK _, ?_⟩
  have hPost := source_mixed_physical_posterior_hessian_margin μ hQ hnp
    (g := 2*κ) (by positivity)
  simp only [show 2*κ/2 = κ by ring] at hPost
  filter_upwards [hPost] with n hn
  intro u hu z hk hZ
  let ν := mixedLaw μ Q u hu z
  let D := intrinsicDet μ Q u
  let A := {J : Disorder (n+2) μ.maxDegree | ¬ sourceHessianMargin c κ J u}
  let φ := A.indicator (fun _ => (1 : ℝ))
  have hM := hMom n u hu z hk hZ
  have hD0 : ∀ J, 0 ≤ D J := fun _ => abs_nonneg _
  have hA : MeasurableSet A :=
    ((sourceHessianMargin_closed c κ).measurableSet.preimage
      (measurable_id.prodMk (measurable_const (a := u)))).compl
  have hφ : Measurable φ := measurable_const.indicator hA
  have hφ0 : ∀ J, 0 ≤ φ J ∧ φ J ≤ 1 := by
    intro J
    by_cases hJ : J ∈ A <;> simp [φ, hJ]
  have hφmean : (∫ J, φ J ∂ν) ≤ Real.exp (-d*(n+1 : ℕ)) := by
    have heq : (∫ J, φ J ∂ν) = ν.real A := by
      rw [show φ = A.indicator (fun _ => (1 : ℝ)) from rfl, integral_indicator hA]
      simp
    rw [heq]
    have h := hn u hu (z 0) (z 1) hk
    have hz : WithLp.toLp 2 ![z 0, z 1] = z := by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    rw [hz] at h
    change ν.real A ≤ _ at h
    exact h.trans_eq (by
      congr 1
      dsimp [d]
      push_cast
      ring)
  let : IsProbabilityMeasure ν := by unfold ν mixedLaw; infer_instance
  have hHolder := determinant_weighted_holder ν D φ hM.1
    (.of_forall hD0) hM.2.2.1 hφ.aestronglyMeasurable (.of_forall hφ0)
    (by norm_num : (1 : ℝ) < 2) hM.2.2.2.1 hM.2.2.2.2 hφmean
  have hRatio : (∫ J in A, D J ∂ν) / (∫ J, D J ∂ν) ≤
      K^(1/(2 : ℝ)) * Real.exp (-d*(n+1 : ℕ)/2) := by
    have heq : (∫ J, D J * φ J ∂ν) = ∫ J in A, D J ∂ν := by
      rw [← integral_indicator hA]
      congr 1
      funext J
      by_cases hJ : J ∈ A <;> simp [φ, hJ]
    rw [heq, show (1 : ℝ)-1/2 = 1/2 by norm_num, ← Real.exp_mul] at hHolder
    exact hHolder.trans_eq (by congr 2; ring)
  have hBound := palm_ratio_to_lintegral_bound ν D hM.1 hD0 A hA
    (by positivity) hM.2.2.1 hRatio
  have hmark : ∀ J : Disorder (n+2) μ.maxDegree,
      hessianMarginFailureMark c κ J u = if J ∈ A then 1 else 0 := by
    intro J
    by_cases hJ : sourceHessianMargin c κ J u <;>
      simp [hessianMarginFailureMark, A, hJ]
  change (∫⁻ J, ENNReal.ofReal (D J) * hessianMarginFailureMark c κ J u ∂ν) ≤
    ENNReal.ofReal (K^(1/(2 : ℝ)) * Real.exp (-d*(n+1 : ℕ)/2)) *
      (∫⁻ J, ENNReal.ofReal (D J) ∂ν)
  calc
    _ = ∫⁻ J, ENNReal.ofReal (D J) *
        @ite ℝ≥0∞ (J ∈ A) (Classical.propDecidable _) 1 0 ∂ν := by
      apply lintegral_congr
      intro J
      rw [hmark J]
      split_ifs <;> rfl
    _ ≤ _ := hBound

/-- The bad-Hessian first moment with a prescribed margin, so the base
choice κ = g₀/4 is retained when the radial interval is later narrowed. -/
private theorem fixed_margin_bad_count
    (μ : FiniteMixture) {β x Q L R κ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hκ : 0 < κ)
    (hGap : 2 * Real.sqrt (Q^2 * μ.xi2 Q) + 2*κ ≤ L)
    (hLR : L < R) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (rectangularScoreWindow
            (Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) (Ioo L R))
          (hessianMarginFailureMark (centerCoefficients (mixtureCoefficients μ) Q) κ) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * Real.exp (-c*(n+2 : ℕ))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hGap
  have hR0 : 0 < R := hL0.trans hLR
  let d := (κ / Real.sqrt (Q^2 * μ.xi2 Q))^2 / (16 * Real.pi^2)
  have hd : 0 < d := by
    exact div_pos (sq_pos_of_pos (div_pos hκ
      (Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos h.overlap_range.1)
        (μ.xi2_pos h.overlap_range.1))))) (by positivity)
  let c₀ := β*x
  have hc₀ : 0 < c₀ := mul_pos h.beta_pos h.weight_range.1
  let δ := d/(16*c₀)
  have hδ : 0 < δ := by positivity
  have hδeq : c₀*δ = d/16 := by dsimp [δ]; field_simp
  obtain ⟨B, hB, hIntensity⟩ := sourceMixedIntensity_compact_upper μ h.overlap_range.1 hnp
  obtain ⟨D, hD, hPost⟩ := posterior_bad_margin_weight μ h.overlap_range.1 hnp
    (Z := R) hκ
  let A := 2*δ*(R-L)*B*D
  have hA : 0 < A := by dsimp [A]; positivity
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hAbsorb : ∀ᶠ n : ℕ in atTop,
      A*(n+2 : ℕ)*Real.exp (-(d/16)*(n+2 : ℕ)) ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (hN.const_mul_atTop (show 0 < d/16 by positivity))
    have ht' : Tendsto (fun n : ℕ => A*(n+2 : ℕ)*Real.exp (-(d/16)*(n+2 : ℕ)))
        atTop (𝓝 (0 : ℝ)) := by
      convert ht.const_mul (A/(d/16)) using 1
      · funext n
        simp only [Function.comp_def, pow_one, neg_mul]
        field_simp
      · simp
    exact (ht'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hn => hn.le)
  refine ⟨δ, d/16, 1, hδ, by positivity, by norm_num, ?_⟩
  filter_upwards [hPost, hIntensity hR0.le (show 0 < d/16 by positivity), hAbsorb]
    with n hn hI habs
  let W := Icc (markE μ β x Q-δ) (markE μ β x Q+δ)
  let K := rectangularScoreWindow W (Ioo L R)
  let w := ENNReal.ofReal (D * Real.exp (-d*(n+1 : ℕ)/2))
  have hKR :
      (∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K
        (hessianMarginFailureMark (centerCoefficients (mixtureCoefficients μ) Q) κ) J
        ∂disorderLaw (n+2) μ.maxDegree) ≤
      w * (∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
        ∂disorderLaw (n+2) μ.maxDegree) := by
    apply actual_mixed_marked_count_le_of_uniform_palm n μ h.overlap_range.1 hnp K
      (rectangularScoreWindow_measurable W (Ioo L R) measurableSet_Icc measurableSet_Ioo)
      _ (hessianMarginFailureMark_measurable _ _) ENNReal.ofReal_ne_top
    intro u hu z hz
    exact hn u hu z (hGap.trans hz.2.1.le) hz.2.2.le
  have hDensity : ∀ e ∈ W, ∀ k ∈ Ioo L R,
      mixedCriticalIntensity n μ Q (WithLp.toLp 2 ![e,k]) ≤
        ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((d/8)*(n+2 : ℕ))) := by
    intro e he k hk
    have hkAbs : |k| ≤ R := abs_le.mpr ⟨by linarith [hk.1], hk.2.le⟩
    have hComp := sourceMarkedComplexity_global_loss μ h hnp e k
    have hCurv := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
      (by have hdeg := h.min_degree; omega) hnp
    have hPenalty : 0 ≤ sourceMarkedLeastCurvature μ Q *
        ((e-markE μ β x Q)^2+(k-markK μ β Q)^2)/2 := by positivity
    have hEnergy := mul_le_mul_of_nonneg_left he.1 hc₀.le
    have hCompδ : sourceRadialProfile μ Q e k ≤ c₀*δ := by
      dsimp [c₀] at *
      linarith
    apply (hI e k hkAbs).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [hδeq] at hCompδ
    have hmul := mul_le_mul_of_nonneg_left hCompδ
      (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
    nlinarith
  have hCount :
      (∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
        ∂disorderLaw (n+2) μ.maxDegree) ≤
      ENNReal.ofReal (2*δ*(R-L)*B*(n+2 : ℕ)*Real.exp ((d/8)*(n+2 : ℕ))) := by
    rw [actual_mixed_rectangular_count n μ h.overlap_range.1 hnp W (Ioo L R)
      measurableSet_Icc measurableSet_Ioo]
    calc
      _ ≤ ∫⁻ _e in W, ∫⁻ _k in Ioo L R,
          ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((d/8)*(n+2 : ℕ))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with e he
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
        exact hDensity e he k hk
      _ = _ := by
        simp only [lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Ioo, W, Real.volume_Icc]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hWeighted := mul_le_mul' (le_refl w) hCount
  have hProduct : w * ENNReal.ofReal
      (2*δ*(R-L)*B*(n+2 : ℕ)*Real.exp ((d/8)*(n+2 : ℕ))) =
      ENNReal.ofReal (A*(n+2 : ℕ)*
        Real.exp ((d/8)*(n+2 : ℕ)-d*(n+1 : ℕ)/2)) := by
    dsimp [w]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = (A*(n+2 : ℕ)) *
          (Real.exp ((d/8)*(n+2 : ℕ)) * Real.exp (-d*(n+1 : ℕ)/2)) := by
        dsimp [A]
        ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [hProduct] at hWeighted
  have hRate : (d/8)*(n+2 : ℕ)-d*(n+1 : ℕ)/2 ≤
      -(d/16)*(n+2 : ℕ) + -(d/16)*(n+2 : ℕ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hFinal : A*(n+2 : ℕ)*Real.exp ((d/8)*(n+2 : ℕ)-d*(n+1 : ℕ)/2) ≤
      Real.exp (-(d/16)*(n+2 : ℕ)) := by
    calc
      _ ≤ A*(n+2 : ℕ)*Real.exp (-(d/16)*(n+2 : ℕ) + -(d/16)*(n+2 : ℕ)) := by
        gcongr
      _ = (A*(n+2 : ℕ)*Real.exp (-(d/16)*(n+2 : ℕ))) *
          Real.exp (-(d/16)*(n+2 : ℕ)) := by rw [Real.exp_add]; ring
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
  simpa only [one_mul] using
    hKR.trans (hWeighted.trans (ENNReal.ofReal_le_ofReal hFinal))


/-- The above-contact first moment also controls the actual global maximum. -/
private theorem maximum_upper_tail_exponential
    (μ : FiniteMixture) {β x Q ε : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real
        {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} ≤
          Real.exp (-c*(n+2 : ℕ)) := by
  obtain ⟨c, hc, hMean⟩ := sourceAboveContactCountMass_exponential μ h hnp hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [hMean] with n hn
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let K := rectangularScoreWindow (Ici (markE μ β x Q+ε)) univ
  let B := actualScoreWindowCount (n+1) cQ K (fun _ _ => 1)
  have hB : AEMeasurable B (disorderLaw (n+2) μ.maxDegree) :=
    actualScoreWindowCount_aemeasurable (n+1) (by omega) μ h.overlap_range.1 K
      (rectangularScoreWindow_measurable _ _ measurableSet_Ici MeasurableSet.univ)
      _ measurable_const
  have hSub : {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} ⊆
      {J | 1 ≤ B J} := by
    intro J hJ
    change (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J at hJ
    obtain ⟨u, hu, hCrit, _, hValue⟩ := sourceSphereMaximum_attained n μ Q J
    have hWindow : actualScore cQ J u ∈ K := by
      refine ⟨?_, mem_univ _⟩
      rw [actualScore_value_eq]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+2 : ℕ))).mpr
      rw [hValue] at hJ
      simpa only [mul_comm] using hJ
    exact ENNReal.le_tsum
      (f := fun _z : {z : Vector (n+2) | ‖z‖^2 = (n+2 : ℕ) ∧
        surfaceGradient (field cQ J) z = 0 ∧ actualScore cQ J z ∈ K} => (1 : ℝ≥0∞))
      ⟨u, hu, hCrit, hWindow⟩
  have hMass : disorderLaw (n+2) μ.maxDegree
      {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} ≤
        ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ))) := by
    apply (measure_mono hSub).trans
    calc
      _ ≤ ∫⁻ J, B J ∂disorderLaw (n+2) μ.maxDegree := by
        simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hB 1
      _ ≤ _ := by
        simpa only [sourceMarkedOriginalCountMass_def] using hn
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMass).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)


private theorem scalar_derivative_upper_bound
    (f f' : ℝ → ℝ) (b M : ℝ) (hb : 0 ≤ b)
    (hderiv : ∀ r ∈ Set.Icc (0 : ℝ) b, HasDerivAt f (f' r) r)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) b, f' r ≤ M) :
    f b - f 0 ≤ M*b := by
  rcases hb.eq_or_lt with rfl | hbpos
  · simp
  have hc : ContinuousOn f (Set.Icc (0 : ℝ) b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  obtain ⟨r,hr,hslope⟩ := exists_hasDerivAt_eq_slope f f' hbpos hc
    (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx))
  have hrI : r ∈ Set.Icc (0 : ℝ) b := Set.Ioo_subset_Icc_self hr
  have hle : (f b - f 0)/b ≤ M := by
    have heq : f' r = (f b - f 0)/b := by simpa using hslope
    rw [← heq]
    exact hbound r hrI
  exact (div_le_iff₀ hbpos).mp hle


/-- The closed angle endpoint in `lem:mo-geodesic` still leaves half of
the strictly negative initial curvature. -/
private theorem scalar_collar_closed
    (N C κ θ : ℝ) (hN : 0 < N) (hC : 0 < C) (hκ : 0 < κ)
    (hθ : 0 < θ) (hθsmall : θ ≤ κ/(2*C))
    (s h t : ℝ → ℝ) (hs0 : s 0 = 0) (hh0 : h 0 ≤ -κ*N)
    (hs : ∀ r ∈ Icc (0 : ℝ) θ, HasDerivAt s (h r) r)
    (hh : ∀ r ∈ Icc (0 : ℝ) θ, HasDerivAt h (t r) r)
    (ht : ∀ r ∈ Icc (0 : ℝ) θ, |t r| ≤ C*N) :
    s θ < 0 := by
  have hCN : 0 ≤ C*N := mul_nonneg hC.le hN.le
  have hct : C*θ ≤ κ/2 := by
    calc
      _ ≤ C*(κ/(2*C)) := mul_le_mul_of_nonneg_left hθsmall hC.le
      _ = κ/2 := by field_simp
  have hctN : (C*N)*θ ≤ (κ*N)/2 := by
    nlinarith [mul_le_mul_of_nonneg_right hct hN.le]
  have hneg : ∀ r ∈ Icc (0 : ℝ) θ, h r < 0 := by
    intro r hr
    have hdiff := scalar_derivative_upper_bound h t r (C*N) hr.1
      (fun z hz => hh z (Icc_subset_Icc_right hr.2 hz))
      (fun z hz => (le_abs_self _).trans (ht z (Icc_subset_Icc_right hr.2 hz)))
    have hmul := mul_le_mul_of_nonneg_left hr.2 hCN
    nlinarith [mul_pos hκ hN]
  have hcont : ContinuousOn s (Icc (0 : ℝ) θ) := by
    intro r hr
    exact (hs r hr).continuousAt.continuousWithinAt
  obtain ⟨r, hr, hslope⟩ := exists_hasDerivAt_eq_slope s h hθ hcont
    (fun r hr => hs r (Ioo_subset_Icc_self hr))
  have hdiv : (s θ-s 0)/θ < 0 := by
    have heq : h r = (s θ-s 0)/θ := by simpa only [sub_zero] using hslope
    rw [← heq]
    exact hneg r (Ioo_subset_Icc_self hr)
  have hmul := (div_lt_iff₀ hθ).mp hdiv
  simpa only [hs0, sub_zero, zero_mul] using hmul

/-- The exact manuscript collar `1 - cos (min (π/4) (κ/(2C)))`, including
its boundary. The existing actual-sphere collar first rules out overlap one. -/
private theorem exact_critical_collar {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) (u w : Vector (n+1))
    (hu : ‖u‖^2 = (n+1 : ℕ)) (hw : ‖w‖^2 = (n+1 : ℕ)) (huw : u ≠ w)
    (huc : surfaceGradient (field c J) u = 0)
    (hwc : surfaceGradient (field c J) w = 0)
    (hMargin : sourceHessianMargin c κ J u) (hReg : sourceSphereRegularity c J ≤ C) :
    overlap u w < 1 - (1 - Real.cos (min (Real.pi/4) (κ/(2*C)))) := by
  have hShort := source_actual_sphere_critical_collar_exclusion c J hκ hC
    u w hu hw huw huc hwc hMargin hReg
  have hLoss := (sourceCriticalCollar_parameters hκ hC).1
  have hrLt : overlap u w < 1 := by linarith
  let θ := min (Real.pi/4) (κ/(2*C))
  have hθ : 0 < θ := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ : θ ≤ Real.pi := (min_le_left _ _).trans (by linarith [Real.pi_pos])
  have hCos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by have := min_le_left (Real.pi/4) (κ/(2*C)); dsimp [θ]; linarith [Real.pi_pos]⟩
  by_contra hbad
  have hrLower : Real.cos θ ≤ overlap u w := by
    change ¬ overlap u w < 1 - (1 - Real.cos θ) at hbad
    linarith
  have hrPos : 0 < overlap u w := hCos.trans_le hrLower
  have hAngle : Real.arccos (overlap u w) ≤ θ := by
    have H := Real.arccos_le_arccos hrLower
    rwa [Real.arccos_cos hθ.le hθπ] at H
  obtain ⟨v, hv, huv, hEnd⟩ := sourceSphereGeodesic_reconstruction u w hu hw ⟨hrPos, hrLt⟩
  have hs0 : sourceSphereGeodesicSlope c J u v 0 = 0 := by
    unfold sourceSphereGeodesicSlope
    rw [sourceSphereGeodesicVelocity_zero, sourceSphereGeodesic_zero, huc, inner_zero_right]
  have hh0 : sourceSphereGeodesicCurvature c J u v 0 ≤ -κ*(n+1 : ℕ) := by
    unfold sourceSphereGeodesicCurvature
    rw [sourceSphereGeodesicVelocity_zero, sourceSphereGeodesic_zero]
    have H := hMargin v
    rwa [source_tangentProjection_fixed u v huv, hv] at H
  have H := scalar_collar_closed (n+1 : ℕ) C κ (Real.arccos (overlap u w))
    (by positivity) hC hκ (Real.arccos_pos.mpr hrLt)
    (hAngle.trans (min_le_right _ _))
    (sourceSphereGeodesicSlope c J u v) (sourceSphereGeodesicCurvature c J u v)
    (sourceSphereGeodesicCubic c J u v) hs0 hh0
    (fun t _ => sourceSphereGeodesicSlope_hasDerivAt (by omega) c J u v hu hv huv t)
    (fun t _ => sourceSphereGeodesicCurvature_hasDerivAt (by omega) c J u v hu hv huv t)
    (fun t _ => sourceSphereGeodesicCubic_abs_le (by omega) c J u v hu hv huv hReg t)
  have hsEnd : sourceSphereGeodesicSlope c J u v (Real.arccos (overlap u w)) = 0 := by
    unfold sourceSphereGeodesicSlope
    rw [hEnd, hwc, inner_zero_right]
  rw [hsEnd] at H
  exact (lt_irrefl (0 : ℝ)) H

/-- Original tensor regularity bounds the full covariant norm D_N,
including all four suprema in `eq:mo-regnorm`. -/
private theorem original_full_regularity (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ J : Disorder (n+2) μ.maxDegree,
      J ∈ regularDisorder →
        sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J ≤ C := by
  let K := ∑ q : Degree μ.maxDegree, blockThreshold q
  have hK : 0 ≤ K := Finset.sum_nonneg (fun q _ => (blockThreshold_pos q).le)
  refine ⟨13 * sourcePosteriorDerivativeConstant
    (centerCoefficients (mixtureCoefficients μ) Q) K,
    mul_pos (by norm_num) (sourcePosteriorDerivativeConstant_pos _ hK), ?_⟩
  intro n J hJ
  have hOrdered : J ∈ sourcePosteriorOrderedRegularity K := by
    intro q
    have hq : blockThreshold q ≤ K :=
      Finset.single_le_sum (fun r _ => (blockThreshold_pos r).le) (Finset.mem_univ q)
    have hq0 : 0 ≤ (q.val.val : ℝ) := Nat.cast_nonneg _
    exact (hJ q).trans (by linarith)
  exact source_ordered_sphere_regularity_bound (by omega) _ hK J hOrdered

/-- All of manuscript `prop:mo-all-high`. The base interval U₀ = (L₀,R₀)
fixes κ = g₀/4 and C_reg before U = (L,R) and δ are chosen. The overlap
loss is exactly `eq:mo-eta`, and the probability bound holds for every N ≥ 2. -/
theorem mixed_all_high_complete
    (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < L₀)
    (hL₀ : L₀ < markK μ β Q) (hR₀ : markK μ β Q < R₀) :
    let κ := (L₀ - 2 * Real.sqrt (Q^2 * μ.xi2 Q))/4
    ∃ C_reg : ℝ, 0 < κ ∧ 0 < C_reg ∧
      let η := 1 - Real.cos (min (Real.pi/4) (κ/(2*C_reg)))
      0 < η ∧ η < 1 ∧
      ∀ L R : ℝ, L₀ < L → R < R₀ → L < markK μ β Q → markK μ β Q < R →
        ∃ δ_U : ℝ, 0 < δ_U ∧ δ_U ≤ 1 ∧
          ∀ δ : ℝ, 0 < δ → δ ≤ δ_U →
            ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
              ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
                (∀ n, MeasurableSet (Ω n)) ∧
                (∀ n, ∀ J ∈ Ω n,
                  sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J ≤ C_reg ∧
                  (∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
                    ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖ ≤
                      C_reg / Real.sqrt (n+2 : ℕ)) ∧
                  sSup ((fun u : Vector (n+2) =>
                    ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖) ''
                      {u | ‖u‖^2 = (n+2 : ℕ)}) ≤ C_reg / Real.sqrt (n+2 : ℕ) ∧
                  ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
                    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 →
                    (n+2 : ℕ)*(markE μ β x Q-δ) ≤
                      field (centerCoefficients (mixtureCoefficients μ) Q) J u →
                    field (centerCoefficients (mixtureCoefficients μ) Q) J u ≤
                        (n+2 : ℕ)*(markE μ β x Q+δ) ∧
                      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R ∧
                      sourceHessianMargin (centerCoefficients (mixtureCoefficients μ) Q) κ J u ∧
                      ∀ v : Vector (n+2), ‖v‖^2 = (n+2 : ℕ) →
                        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) v = 0 →
                        v ≠ u → overlap u v < 1-η) ∧
                (∀ n : ℕ, (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤
                  C * Real.exp (-c*(n+2 : ℕ))) := by
  classical
  let κ := (L₀ - 2 * Real.sqrt (Q^2 * μ.xi2 Q))/4
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hGap : 2 * Real.sqrt (Q^2 * μ.xi2 Q) + 2*κ ≤ L₀ := by
    dsimp [κ]
    linarith
  obtain ⟨s, b, B, hs, hb, hB, hBadMean⟩ :=
    fixed_margin_bad_count μ h hnp hκ hGap (hL₀.trans hR₀)
  obtain ⟨C_reg, hCreg, hRegularity⟩ := original_full_regularity μ Q
  let θ := min (Real.pi/4) (κ/(2*C_reg))
  have hθ : 0 < θ := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hθπ4 : θ ≤ Real.pi/4 := min_le_left _ _
  have hCos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hCosOne : Real.cos θ < 1 := by
    have H := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ)
      (by norm_num) (by linarith [Real.pi_pos]) hθ
    simpa only [Real.cos_zero] using H
  refine ⟨C_reg, hκ, hCreg, sub_pos.mpr hCosOne, by linarith, ?_⟩
  intro L R hLbase hRbase hL hR
  obtain ⟨t, κ', A, a, ht, _, hA, ha, Ω₀, hΩ₀meas, hΩ₀good, hΩ₀prob⟩ :=
    MixedHighEnergyAllHigh.mixed_all_high_critical_event μ h hnp (hEdge.trans hLbase) hL hR
  let δ_U := min t (min s 1)
  have hδU : 0 < δ_U := lt_min ht (lt_min hs (by norm_num))
  refine ⟨δ_U, hδU, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro δ hδ hδUle
  have hδt : δ ≤ t := hδUle.trans (min_le_left _ _)
  have hδs : δ ≤ s := hδUle.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨e, he, hMaximum⟩ := maximum_upper_tail_exponential μ h hnp hδ
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let W := rectangularScoreWindow
    (Icc (markE μ β x Q-s) (markE μ β x Q+s)) (Ioo L₀ R₀)
  let badCount (n : ℕ) := actualScoreWindowCount (n+1) cQ W (hessianMarginFailureMark cQ κ)
  let bad (n : ℕ) := toMeasurable (disorderLaw (n+2) μ.maxDegree) {J | 1 ≤ badCount n J}
  let cutoff (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    {J | sourceSphereMaximum n μ Q J ≤ (n+2 : ℕ)*(markE μ β x Q+δ)}
  let Ω (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    ((Ω₀ n ∩ regularDisorder) ∩ (bad n)ᶜ) ∩ cutoff n
  have hMeas (n : ℕ) : MeasurableSet (Ω n) :=
    (((hΩ₀meas n).inter (regularDisorder_measurable _ _)).inter
      (measurableSet_toMeasurable _ _).compl).inter
      (isClosed_le (sourceSphereMaximum_continuous n μ Q) continuous_const).measurableSet
  have hGood : ∀ n, ∀ J ∈ Ω n,
      sourceSphereRegularity cQ J ≤ C_reg ∧
      (∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        ‖sourceSphereThirdExtension cQ J u‖ ≤ C_reg / Real.sqrt (n+2 : ℕ)) ∧
      sSup ((fun u : Vector (n+2) => ‖sourceSphereThirdExtension cQ J u‖) ''
        {u | ‖u‖^2 = (n+2 : ℕ)}) ≤ C_reg / Real.sqrt (n+2 : ℕ) ∧
      ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        surfaceGradient (field cQ J) u = 0 →
        (n+2 : ℕ)*(markE μ β x Q-δ) ≤ field cQ J u →
        field cQ J u ≤ (n+2 : ℕ)*(markE μ β x Q+δ) ∧
        actualScore cQ J u 1 ∈ Ioo L R ∧ sourceHessianMargin cQ κ J u ∧
        ∀ v : Vector (n+2), ‖v‖^2 = (n+2 : ℕ) →
          surfaceGradient (field cQ J) v = 0 → v ≠ u →
          overlap u v < 1-(1-Real.cos θ) := by
    intro n J hJ
    obtain ⟨⟨⟨hOld, hReg⟩, hNotBad⟩, hCut⟩ := hJ
    have hRegBound := hRegularity n J hReg
    have hThird : ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        ‖sourceSphereThirdExtension cQ J u‖ ≤ C_reg / Real.sqrt (n+2 : ℕ) :=
      fun u hu => sourceSphereRegularity_third_point_bound (by omega) cQ J hRegBound u hu
    refine ⟨hRegBound, hThird, ?_, ?_⟩
    · refine csSup_le ((sourceSphere_nonempty (by omega : 0 < n+2)).image _) ?_
      rintro _ ⟨u, hu, rfl⟩
      exact hThird u hu
    · intro u hu hCrit hHigh
      have hNr : (0 : ℝ) < (n+2 : ℕ) := by positivity
      have hHighOld : (n+2 : ℕ)*(markE μ β x Q-t) ≤ field cQ J u :=
        (mul_le_mul_of_nonneg_left (by linarith) hNr.le).trans hHigh
      have hMark := ((hΩ₀good n J hOld).1 u hu hCrit hHighOld).1
      have hUpper : field cQ J u ≤ (n+2 : ℕ)*(markE μ β x Q+δ) := by
        obtain ⟨v, _, _, hMax, hValue⟩ := sourceSphereMaximum_attained n μ Q J
        exact (show field cQ J u ≤ sourceSphereMaximum n μ Q J by
          rw [hValue]; exact hMax hu).trans hCut
      have hMargin : sourceHessianMargin cQ κ J u := by
        by_contra hBadMargin
        apply hNotBad
        apply subset_toMeasurable _ _
        have hWindow : actualScore cQ J u ∈ W := by
          refine ⟨⟨?_, ?_⟩, ⟨hLbase.trans hMark.1, hMark.2.trans hRbase⟩⟩
          · rw [actualScore_value_eq]
            have hLow : markE μ β x Q-δ ≤ field cQ J u / (n+2 : ℕ) :=
              (le_div_iff₀ hNr).mpr (by simpa only [mul_comm] using hHigh)
            exact (by linarith : markE μ β x Q-s ≤ markE μ β x Q-δ).trans hLow
          · rw [actualScore_value_eq]
            have hUp : field cQ J u / (n+2 : ℕ) ≤ markE μ β x Q+δ :=
              (div_le_iff₀ hNr).mpr (by simpa only [mul_comm] using hUpper)
            exact hUp.trans (by linarith)
        have hOne := ENNReal.le_tsum
          (f := fun z : {z : Vector (n+2) | ‖z‖^2 = (n+2 : ℕ) ∧
            surfaceGradient (field cQ J) z = 0 ∧ actualScore cQ J z ∈ W} =>
              hessianMarginFailureMark cQ κ J z) ⟨u, hu, hCrit, hWindow⟩
        simpa only [hessianMarginFailureMark, ite_eq_right hBadMargin,
          badCount, actualScoreWindowCount, mem_ofPred_eq] using hOne
      refine ⟨hUpper, hMark, hMargin, ?_⟩
      intro v hv hvc hvu
      exact exact_critical_collar cQ J hκ hCreg u v hu hv hvu.symm hCrit hvc hMargin hRegBound
  let c := min a (min 1 (min b e))
  have hc : 0 < c := lt_min ha (lt_min (by norm_num) (lt_min hb he))
  have hca : c ≤ a := min_le_left _ _
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hce : c ≤ e := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hProb : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤ (A+B+2)*Real.exp (-c*(n+2 : ℕ)) := by
    filter_upwards [hΩ₀prob, hBadMean, hMaximum] with n hOld hn hMax
    have hCountAE : AEMeasurable (badCount n) (disorderLaw (n+2) μ.maxDegree) :=
      actualScoreWindowCount_aemeasurable (n+1) (by omega) μ h.overlap_range.1 W
        (rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Ioo)
        _ (hessianMarginFailureMark_measurable cQ κ)
    have hBadMass : disorderLaw (n+2) μ.maxDegree (bad n) ≤
        ENNReal.ofReal (B*Real.exp (-b*(n+2 : ℕ))) := by
      rw [show bad n = toMeasurable (disorderLaw (n+2) μ.maxDegree)
        {J | 1 ≤ badCount n J} from rfl, measure_toMeasurable]
      calc
        _ ≤ ∫⁻ J, badCount n J ∂disorderLaw (n+2) μ.maxDegree := by
          simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hCountAE 1
        _ ≤ _ := hn
    have hBadReal : (disorderLaw (n+2) μ.maxDegree).real (bad n) ≤
        B*Real.exp (-b*(n+2 : ℕ)) :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBadMass).trans_eq
        (ENNReal.toReal_ofReal (by positivity))
    have hCutReal : (disorderLaw (n+2) μ.maxDegree).real (cutoff n)ᶜ ≤
        Real.exp (-e*(n+2 : ℕ)) := by
      apply (measureReal_mono (show (cutoff n)ᶜ ⊆
        {J | (n+2 : ℕ)*(markE μ β x Q+δ) ≤ sourceSphereMaximum n μ Q J} by
          intro J hJ
          change ¬ sourceSphereMaximum n μ Q J ≤ (n+2 : ℕ)*(markE μ β x Q+δ) at hJ
          exact (lt_of_not_ge hJ).le) (measure_ne_top _ _)).trans hMax
    have hUnion : (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤
        A*Real.exp (-a*(n+2 : ℕ)) + Real.exp (-(n+2 : ℕ)) +
          B*Real.exp (-b*(n+2 : ℕ)) + Real.exp (-e*(n+2 : ℕ)) := by
      have hSub : (Ω n)ᶜ ⊆ ((Ω₀ n)ᶜ ∪ regularDisorderᶜ) ∪ bad n ∪ (cutoff n)ᶜ := by
        simp only [Ω, compl_inter, compl_compl]
        exact Subset.rfl
      exact (measureReal_mono hSub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add
          ((measureReal_union_le _ _).trans (add_le_add
            ((measureReal_union_le _ _).trans (add_le_add hOld
              (regularDisorder_failure_probability (by omega)))) hBadReal)) hCutReal))
    have hRate {r : ℝ} (hcr : c ≤ r) :
        Real.exp (-r*(n+2 : ℕ)) ≤ Real.exp (-c*(n+2 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcr (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)]
    apply hUnion.trans
    calc
      _ ≤ A*Real.exp (-c*(n+2 : ℕ)) + Real.exp (-c*(n+2 : ℕ)) +
          B*Real.exp (-c*(n+2 : ℕ)) + Real.exp (-c*(n+2 : ℕ)) :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hRate hca) hA.le)
          (by simpa using hRate hc1))
          (mul_le_mul_of_nonneg_left (hRate hcb) hB.le)) (hRate hce)
      _ = _ := by ring
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hProb
  let C := max (A+B+2) (Real.exp (c*(n₀+2 : ℕ))) + 1
  have hC : 0 < C := by
    have := le_max_right (A+B+2) (Real.exp (c*(n₀+2 : ℕ)))
    dsimp [C]
    linarith [Real.exp_pos (c*(n₀+2 : ℕ))]
  refine ⟨c, C, hc, hC, Ω, hMeas, hGood, ?_⟩
  intro n
  by_cases hn : n₀ ≤ n
  · exact (hn₀ n hn).trans (mul_le_mul_of_nonneg_right
      (by have := le_max_left (A+B+2) (Real.exp (c*(n₀+2 : ℕ))); dsimp [C]; linarith)
      (Real.exp_pos _).le)
  · apply measureReal_le_one.trans
    have hnn : (n+2 : ℝ) ≤ (n₀+2 : ℕ) := by exact_mod_cast (show n+2 ≤ n₀+2 by omega)
    have hExp : 1 ≤ Real.exp (c*(n₀+2 : ℕ))*Real.exp (-c*(n+2 : ℕ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      push_cast at hnn ⊢
      nlinarith
    exact hExp.trans (mul_le_mul_of_nonneg_right
      (by have := le_max_right (A+B+2) (Real.exp (c*(n₀+2 : ℕ))); dsimp [C]; linarith)
      (Real.exp_pos _).le)

end SlowEquilibration.MixedAllHighComplete
