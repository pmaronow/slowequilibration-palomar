-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureAboveStaticCertificate
public import SlowEquilibration.SourcePurePCCountsLiteral
public import SlowEquilibration.SphericalPureCapSourceScalars
public import SlowEquilibration.SphericalPureCenterFieldScale
public import SlowEquilibration.SphericalConcentration

/-! The maximum estimates in manuscript `lem:pc-regularity`, equation
`eq:pc-ground-conc`, for the original amplitude-one pure model. The joint
critical-count/maximum theorem identifies the limiting energy; Gaussian
concentration then identifies the mean and gives the stated exponential tail.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureHighEnergyMaximumConcentration

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PureStationarity
open SphericalGaussianJet SphericalForm
open SphericalPureCapSourceScalars SphericalPureCenterFieldScale
open PairConditionalDeterminantMoments
open scoped Topology ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma center_one (μ : FiniteMixture) :
    centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
  funext k
  simp [centerCoefficients]

private lemma maximum_scale (p : ℕ) (hp : 4 ≤ p) {Q : ℝ} (hQ : 0 < Q)
    (n : ℕ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) :
    sourceSphereMaximum n (FiniteMixture.pure p (by omega) 1 (by positivity)) Q J =
      (Real.sqrt Q)^p *
        sourceSphereMaximum n (FiniteMixture.pure p (by omega) 1 (by positivity)) 1 J := by
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity : (0 : ℝ) < 1)
  have hs : 0 < (Real.sqrt Q)^p := pow_pos (Real.sqrt_pos.mpr hQ) _
  obtain ⟨u,hu,_,hmaxu,hequ⟩ := sourceSphereMaximum_attained n μ Q J
  obtain ⟨v,hv,_,hmaxv,heqv⟩ := sourceSphereMaximum_attained n μ 1 J
  rw [center_one] at hmaxv heqv
  have hscale (z : Vector (n+2)) :=
    pure_center_field_eq_original_scale p (by omega) 1 (by positivity) hQ.le (n+2) J z
  rw [hequ,heqv,hscale]
  apply le_antisymm
  · exact mul_le_mul_of_nonneg_left (hmaxv hu) hs.le
  · have hh : field (centerCoefficients (mixtureCoefficients μ) Q) J v ≤
        field (centerCoefficients (mixtureCoefficients μ) Q) J u := hmaxu hv
    rw [hscale v, hscale u] at hh
    exact hh

private lemma maximum_lipschitz (p : ℕ) (hp : 4 ≤ p) (n : ℕ) :
    LipschitzWith (Real.sqrt (n+2 : ℕ)).toNNReal
      (fun g : EuclideanDisorder (n+2)
          (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree =>
        sourceSphereMaximum n (FiniteMixture.pure p (by omega) 1 (by positivity)) 1
          (unpackDisorder g)) := by
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity : (0 : ℝ) < 1)
  have hcov : covariancePolynomial (mixtureCoefficients μ) 1 = 1 := by
    rw [covariancePolynomial_mixture]
    simp [μ, FiniteMixture.pure_xi]
  apply LipschitzWith.of_le_add_mul
  intro g h
  obtain ⟨u,hu,_,_,hgu⟩ := sourceSphereMaximum_attained n μ 1 (unpackDisorder g)
  obtain ⟨v,_,_,hmv,hhv⟩ := sourceSphereMaximum_attained n μ 1 (unpackDisorder h)
  rw [center_one] at hgu hmv hhv
  have hd := field_euclidean_difference_bound (by omega : 1 ≤ n+2)
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) g h u hu
  rw [hcov,mul_one] at hd
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), hgu, hhv]
  have hb : field (mixtureCoefficients μ) (unpackDisorder h) u ≤
      field (mixtureCoefficients μ) (unpackDisorder h) v := hmv hu
  linarith [le_abs_self (field (mixtureCoefficients μ) (unpackDisorder g) u -
    field (mixtureCoefficients μ) (unpackDisorder h) u)]

private lemma maximum_centered_concentration (p : ℕ) (hp : 4 ≤ p)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    (disorderLaw (n+2) μ.maxDegree).real
      {J | |sourceSphereMaximum n μ 1 J / (n+2 : ℕ) -
        (∫ K, sourceSphereMaximum n μ 1 K ∂disorderLaw (n+2) μ.maxDegree) /
          (n+2 : ℕ)| > t} ≤
      2 * Real.exp (-(n+2 : ℕ)*t^2/2) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity : (0 : ℝ) < 1)
  let F := fun g : EuclideanDisorder (n+2) μ.maxDegree =>
    sourceSphereMaximum n μ 1 (unpackDisorder g)
  have hN : (0 : ℝ) < (n+2 : ℕ) := by positivity
  have hLip := maximum_lipschitz p hp n
  have hlaw := euclideanDisorder_hasLaw (n+2) μ.maxDegree
  have hmean : (∫ J, sourceSphereMaximum n μ 1 J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+2) μ.maxDegree) :=
    hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have h := SYK.euclidean_lipschitz_gaussian_concentration F
    (Real.sqrt (n+2 : ℕ)) ((n+2 : ℕ)*t) (Real.sqrt_pos.mpr hN) (mul_pos hN ht) hLip
  have hset : MeasurableSet {g : EuclideanDisorder (n+2) μ.maxDegree |
      |F g - ∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate (n+2) μ.maxDegree)| > (n+2 : ℕ)*t} :=
    (isOpen_lt continuous_const (hLip.continuous.sub continuous_const).abs).measurableSet
  nth_rw 1 [← hlaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at h
  have hrate : -((n+2 : ℕ)*t)^2 / (2*(Real.sqrt (n+2 : ℕ))^2) =
      -(n+2 : ℕ)*t^2/2 := by
    rw [Real.sq_sqrt hN.le]
    field_simp
  have hevent : {J : Disorder (n+2) μ.maxDegree |
      |sourceSphereMaximum n μ 1 J / (n+2 : ℕ) -
        (∫ K, sourceSphereMaximum n μ 1 K ∂disorderLaw (n+2) μ.maxDegree) /
          (n+2 : ℕ)| > t} =
      euclideanDisorder ⁻¹' {g | |F g - ∫ y, F y
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+2) μ.maxDegree)| >
          (n+2 : ℕ)*t} := by
    ext J
    simp only [mem_ofPred_eq, mem_preimage, F, unpack_euclideanDisorder, ← hmean]
    rw [← sub_div, abs_div, abs_of_pos hN, gt_iff_lt, lt_div_iff₀ hN]
    rw [mul_comm t]
  rw [hevent]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (by
    rw [ENNReal.toReal_ofReal (by positivity), hrate])

private lemma exponential_tail_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => 2 * Real.exp (-(n+2 : ℕ)*t^2/2)) atTop (𝓝 (0 : ℝ)) := by
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hN.atTop_mul_const (show 0 < t^2/2 by positivity))
  simpa only [Function.comp_def, mul_zero, mul_div_assoc, neg_div, neg_mul] using he.const_mul 2

private lemma maximum_near_energy (p : ℕ) (hp : 4 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
    ∀ᶠ n : ℕ in atTop,
      (3/4 : ℝ) < (disorderLaw (n+3) μ.maxDegree).real
        {J | |sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ) -
          pureEnergyConstant p (by omega)| ≤ δ} := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity : (0 : ℝ) < 1)
  let β := Thresholds.staticThreshold (fun r : ℝ => r^p) + 1
  obtain ⟨x,Q,hcert⟩ := pure_certificate_above_static p hp
    (show Thresholds.staticThreshold (fun r : ℝ => r^p) < β by dsimp [β]; linarith)
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  let K (N : ℕ) (R : ℝ) := physicalEnergyWindow N
    (Icc (sourcePureAnalyticCenter N E (β*x)-R)
      (sourcePureAnalyticCenter N E (β*x)+R)) univ
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr hcert.overlap_range.1) p
  have hE : E = pureEnergyConstant p (by omega)*s :=
    (sourcePure_certificate_scalar_coordinates p hp hcert).1
  have hground := (sourcePure_prop_pc_counts_literal p (by omega) 1 (by positivity)
    hcert univ MeasurableSet.univ (by simp)).2.1
  change Tendsto (fun R : ℝ => liminf
    (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
      {J | actualScoreWindowCount (n+2) c (K (n+3) R) (fun _ _ => 1) J ≠ 0 ∧
        sourceSphereMaximum (n+1) μ Q J ≤ sourcePureAnalyticCenter (n+3) E (β*x)+R})
    atTop) atTop (𝓝 (1 : ℝ)) at hground
  obtain ⟨R,hR⟩ := (hground.eventually
    (lt_mem_nhds (show (3/4 : ℝ) < 1 by norm_num))).exists
  have hmass := eventually_lt_of_lt_liminf hR
    (isBoundedUnder_of ⟨0,fun _ => measureReal_nonneg⟩)
  have hbox := (tendsto_add_atTop_nat 1).eventually
    (source_logarithmic_center_offset_bounds (E := E) (c := β*x)
      (mul_pos hcert.beta_pos hcert.weight_range.1)
      (le_refl (0 : ℝ)) (mul_pos hs hδ)
      (fun j => sourcePureAnalyticCenter (j+2) E (β*x))
      (.of_forall fun j => by simp [sourcePureAnalyticCenter]) (-R) R)
  filter_upwards [hmass,hbox] with n hn hboxn
  simp only [show n+1+2 = n+3 by omega] at hboxn
  apply hn.trans_le
  apply measureReal_mono
  · rintro J ⟨hcount,hmax⟩
    have hex : Nonempty {u : Vector (n+3) | ‖u‖^2 = (n+3 : ℕ) ∧
        surfaceGradient (field c J) u = 0 ∧ actualScore c J u ∈ K (n+3) R} := by
      by_contra hempty
      have := not_nonempty_iff.mp hempty
      apply hcount
      change (∑' u : {u : Vector (n+3) | ‖u‖^2 = (n+3 : ℕ) ∧
        surfaceGradient (field c J) u = 0 ∧ actualScore c J u ∈ K (n+3) R},
          (1 : ℝ≥0∞)) = 0
      exact tsum_empty
    obtain ⟨⟨u,hu,_,hwin⟩⟩ := hex
    have henergy := ((actualScore_mem_physicalEnergyWindow (by omega : n+3 ≠ 0)
      c J u _ univ).mp hwin).1
    obtain ⟨v,_,_,hv,hvalue⟩ := sourceSphereMaximum_attained (n+1) μ Q J
    have hlo : sourcePureAnalyticCenter (n+3) E (β*x)-R ≤
        sourceSphereMaximum (n+1) μ Q J := by
      rw [hvalue]
      exact henergy.1.trans (hv hu)
    have hscale := maximum_scale p hp hcert.overlap_range.1 (n+1) J
    have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
    have hlow : (n+3 : ℕ)*(E-s*δ) ≤ s*sourceSphereMaximum (n+1) μ 1 J := by
      rw [← hscale]
      exact hboxn.1.trans (by linarith)
    have hhigh : s*sourceSphereMaximum (n+1) μ 1 J ≤ (n+3 : ℕ)*(E+s*δ) := by
      rw [← hscale]
      exact hmax.trans hboxn.2
    rw [hE] at hlow hhigh
    have hlo' : (n+3 : ℕ)*(pureEnergyConstant p (by omega)-δ) ≤
        sourceSphereMaximum (n+1) μ 1 J := by
      apply (mul_le_mul_iff_right₀ hs).mp
      nlinarith [hlow]
    have hhi' : sourceSphereMaximum (n+1) μ 1 J ≤
        (n+3 : ℕ)*(pureEnergyConstant p (by omega)+δ) := by
      apply (mul_le_mul_iff_right₀ hs).mp
      nlinarith [hhigh]
    change |sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ) -
      pureEnergyConstant p (by omega)| ≤ δ
    apply abs_le.mpr
    constructor
    · have hh : pureEnergyConstant p (by omega)-δ ≤
          sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ) :=
        (le_div_iff₀ hN).mpr (by nlinarith [hlo'])
      linarith
    · have hh : sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ) ≤
          pureEnergyConstant p (by omega)+δ :=
        (div_le_iff₀ hN).mpr (by nlinarith [hhi'])
      linarith
  · exact measure_ne_top _ _

/-- Manuscript `lem:pc-regularity`: the original pure maximum has limiting
mean energy density equal to the explicit pure variational energy. -/
theorem pure_original_maximum_mean_limit (p : ℕ) (hp : 4 ≤ p) :
    Tendsto
      (fun n : ℕ =>
        (∫ J, sourceSphereMaximum n (FiniteMixture.pure p (by omega) 1 (by positivity)) 1 J
          ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) /
          (n+2 : ℕ))
      atTop (𝓝 (pureEnergyConstant p (by omega))) := by
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity : (0 : ℝ) < 1)
  let e := pureEnergyConstant p (by omega)
  let m (n : ℕ) :=
    (∫ J, sourceSphereMaximum n μ 1 J ∂disorderLaw (n+2) μ.maxDegree) / (n+2 : ℕ)
  change Tendsto m atTop (𝓝 e)
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hδ : 0 < ε/3 := by positivity
  have hnear := maximum_near_energy p hp hδ
  have hsmall := (tendsto_add_atTop_nat 1).eventually
    ((exponential_tail_limit hδ).eventually (gt_mem_nhds (show (0 : ℝ) < 1/4 by norm_num)))
  have hev : ∀ᶠ n : ℕ in atTop, dist (m (n+1)) e < ε := by
    filter_upwards [hnear,hsmall] with n hn hs
    have hc := maximum_centered_concentration p hp (n+1) hδ
    have hm : |m (n+1)-e| ≤ 2*(ε/3) := by
      by_contra hbad
      have hbad' : 2*(ε/3) < |m (n+1)-e| := lt_of_not_ge hbad
      have hsub : {J : Disorder (n+3) μ.maxDegree |
          |sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ)-e| ≤ ε/3} ⊆
          {J | |sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ)-m (n+1)| > ε/3} := by
        intro J hJ
        have htri := abs_sub_le (m (n+1))
          (sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ)) e
        rw [abs_sub_comm (m (n+1))
          (sourceSphereMaximum (n+1) μ 1 J / (n+3 : ℕ))] at htri
        change _ ≤ ε/3 at hJ
        change ε/3 < _
        linarith
      have hmono := measureReal_mono (μ := disorderLaw (n+3) μ.maxDegree)
        hsub (measure_ne_top _ _)
      change (disorderLaw (n+3) μ.maxDegree).real _ ≤
        2*Real.exp (-(n+1+2 : ℕ)*(ε/3)^2/2) at hc
      change (3/4 : ℝ) < (disorderLaw (n+3) μ.maxDegree).real _ at hn
      have hh := hn.trans_le (hmono.trans hc)
      linarith
    rw [Real.dist_eq]
    change |m (n+1)-e| < ε
    linarith
  exact eventually_atTop.1 hev

/-- Manuscript `eq:pc-ground-conc`: eventual two-sided concentration of the
original pure ground energy, with the printed constant `2 exp(-N r²/8)`. -/
theorem pure_original_ground_concentration (p : ℕ) (hp : 4 ≤ p)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | |sourceSphereMaximum n (FiniteMixture.pure p (by omega) 1 (by positivity)) 1 J /
          (n+2 : ℕ)-pureEnergyConstant p (by omega)| > r} ≤
        2*Real.exp (-(n+2 : ℕ)*r^2/8) := by
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity : (0 : ℝ) < 1)
  let e := pureEnergyConstant p (by omega)
  let m (n : ℕ) :=
    (∫ J, sourceSphereMaximum n μ 1 J ∂disorderLaw (n+2) μ.maxDegree) / (n+2 : ℕ)
  have hmean := (Metric.tendsto_nhds.1 (pure_original_maximum_mean_limit p hp)
    (r/2) (by positivity))
  filter_upwards [hmean] with n hn
  have hc := maximum_centered_concentration p hp n (half_pos hr)
  have hsub : {J : Disorder (n+2) μ.maxDegree |
      |sourceSphereMaximum n μ 1 J / (n+2 : ℕ)-e| > r} ⊆
      {J | |sourceSphereMaximum n μ 1 J / (n+2 : ℕ)-m n| > r/2} := by
    intro J hJ
    have htri := abs_sub_le (sourceSphereMaximum n μ 1 J / (n+2 : ℕ)) (m n) e
    change dist (m n) e < r/2 at hn
    rw [Real.dist_eq] at hn
    change r < _ at hJ
    change r/2 < _
    linarith
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hc.trans_eq (by
    congr 2
    ring))

end SlowEquilibration.PureHighEnergyMaximumConcentration
