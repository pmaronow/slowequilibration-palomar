-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalHessianMarginEvents
public import SlowEquilibration.SourcePhysicalPairHessianMarginProbability
public import SlowEquilibration.SphericalMarkedGlobalLoss
public import SlowEquilibration.SphericalMarkedWholeLineIntensityBounds
public import SlowEquilibration.SphericalTAPCriticalLightBandMark
public import SlowEquilibration.DeterminantHolder

/-! The determinant-weighted bad-Hessian count used in manuscript
`prop:mo-all-high`. For every prescribed exterior radial interval containing
the contact mark, the expected number of high critical points failing a
fixed positive Hessian margin is exponentially small. Hölder preserves the
dependence between the determinant and the bad-margin indicator; shrinking
the normalized energy window absorbs the growth of the mixed intensity.
All counts are under the original disorder law, for the center field. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.MixedHighEnergyBadHessianCount

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet SphericalForm SphereHessian
open PairConditionalDeterminantMoments ConditionedDeterminantMoments
open SphericalHessianMarginEvents SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalLightBandMark SphericalTAPCriticalLightCountTransfer
open scoped ENNReal Topology

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

/-- Manuscript `prop:mo-all-high`, its bad-Hessian first moment: for each
prescribed open radial interval above the spectral edge and containing the
contact mark, a fixed normalized energy window has exponentially few
critical points failing a fixed positive intrinsic Hessian margin. -/
theorem mixed_high_window_bad_margin_mean
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < L)
    (hL : L < markK μ β Q) (hR : markK μ β Q < R) :
    ∃ δ κ c C : ℝ, 0 < δ ∧ 0 < κ ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (rectangularScoreWindow
            (Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) (Ioo L R))
          (hessianMarginFailureMark (centerCoefficients (mixtureCoefficients μ) Q) κ) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * Real.exp (-c*(n+2 : ℕ))) := by
  have hLR : L < R := hL.trans hR
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hEdge
  have hR0 : 0 < R := hL0.trans hLR
  let κ := (L - 2*Real.sqrt (Q^2 * μ.xi2 Q))/2
  have hκ : 0 < κ := by dsimp [κ]; linarith
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
  refine ⟨δ, κ, d/16, 1, hδ, hκ, by positivity, by norm_num, ?_⟩
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
    exact hn u hu z (by dsimp [κ]; linarith [hz.2.1]) hz.2.2.le
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

end SlowEquilibration.MixedHighEnergyBadHessianCount
