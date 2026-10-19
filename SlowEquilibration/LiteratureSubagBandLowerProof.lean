-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerFinal
public import SlowEquilibration.LiteratureSubagBandUpperFinal
public import SlowEquilibration.SourceMainTheoremsReducedFinal

/-!
# Further steps in Subag's lower band argument

Rotational invariance reduces the exact lower approximation to one canonical
center in each dimension. The subsequent lemmas isolate the sequential
Gibbs-slab step and the Hamiltonian variation needed for thickening a
replicated latitude. The endpoint namespace removes the upper approximation
from every endpoint that uses only that half of the band estimates.

This file is a partial reduction. It does not assert the all-temperature
zero-overlap pressure limit, Lemma 22's arbitrary exponential lower tails,
or the full expected lower band approximation.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerProof

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof LiteratureSubagTheorem10Final
open LiteratureSubagTheorem10Proof
open SphericalGaussianJet PairConditionalDeterminantMoments SphericalTwoPointCovariance
open scoped Topology BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The reference center on the independently constructed spherical chart. -/
def canonicalBandCenter (n : ℕ) (q : ℝ) : Vector (n + 1) :=
  Real.sqrt q • latitudeChartPole n

theorem canonicalBandCenter_norm_sq (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    ‖canonicalBandCenter n q‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * q := by
  rw [canonicalBandCenter, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hq, latitudeChartPole_norm_sq]
  ring

/-- No uniformity over centers remains in the fixed-parameter lower bound:
the actual expected band pressure is rotationally invariant. -/
theorem expectedBandLowerApproximation_iff_canonicalFixedParameters
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) :
    ExpectedBandLowerApproximation D ↔
      ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 → ∀ ε : ℝ, 0 < ε →
        ∀ δ ρ : ℝ, 0 < δ → 0 < ρ → ∀ k : ℕ, 1 ≤ k →
          ∀ᶠ n : ℕ in atTop,
            Real.log (1 - q) / 2 + D.residual q - ε ≤
              expectedReplicatedBandPressure k μ β q δ ρ (canonicalBandCenter n q) := by
  rw [LiteratureSubagBandLowerFinal.expectedBandLowerApproximation_iff_fixedParameters]
  constructor
  · intro h q hq ε hε δ ρ hδ hρ k hk
    filter_upwards [(tendsto_add_atTop_nat 1).eventually
      (h q hq ε hε δ ρ hδ hρ k hk)] with n hn
    exact hn (canonicalBandCenter n q) (canonicalBandCenter_norm_sq n hq.1.le)
  · intro h q hq ε hε δ ρ hδ hρ k hk
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (h q hq ε hε δ ρ hδ hρ k hk)
    refine eventually_atTop.mpr ⟨n₀ + 1, ?_⟩
    intro N hN m hm
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
    have heq : ‖canonicalBandCenter n q‖ = ‖m‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [canonicalBandCenter_norm_sq n hq.1.le, hm]
    rw [← SourceMixedBandsLiteral.replicated_band_expected_center_independent
      k μ β q δ ρ (canonicalBandCenter n q) m heq]
    exact hn₀ n (by omega)

private theorem pi_const_smul {X : Type*} [MeasurableSpace X] {k : ℕ}
    (ν : Measure X) [IsFiniteMeasure ν] (a : ℝ≥0∞) (ha : a ≠ ⊤) :
    Measure.pi (fun _ : Fin k => a • ν) =
      a ^ k • Measure.pi (fun _ : Fin k => ν) := by
  let _ : IsFiniteMeasure (a • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ha.lt_top (measure_lt_top ν univ)⟩
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

/-- The exact entropy factor for independent latitude windows is the
`k`th power of their actual spherical mass. The transverse law remains a
product of uniform sphere laws, so transverse replica constraints are retained. -/
theorem replicatedRestrictedSphere_planeDirection_map {n k : ℕ} (hn : 2 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    ((Measure.pi (fun _ : Fin k => sphereLaw (n + 1))).restrict
      (Set.univ.pi (fun _ : Fin k => overlapRegion u A))).map
        (fun σ i => SphericalPairCommonFrame.planeDirection u (σ i)) =
      (sphereLaw (n + 1) (overlapRegion u A)) ^ k •
        (Measure.pi (fun _ : Fin k => sphereLaw n)).map
          (fun y i => (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u (y i)) := by
  have hd : Measurable (SphericalPairCommonFrame.planeDirection u) := by
    unfold SphericalPairCommonFrame.planeDirection SphericalPairCommonFrame.planeScale overlap
    fun_prop
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun _ => hd.aemeasurable)]
  simp_rw [LiteratureSubagBandUpperFinal.restrictedSphere_planeDirection_map hn u hu hA]
  rw [pi_const_smul _ _ (measure_ne_top _ _), Measure.pi_map_pi
    (fun _ => (by fun_prop : Measurable (fun x : Vector n =>
      (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u x)).aemeasurable)]

/-- The corresponding exact replicated integral identity; measurable angular
weights may include the full transverse overlap-block indicator. -/
theorem replicatedRestrictedSphere_direction_integral {n k : ℕ} (hn : 2 ≤ n)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A)
    (f : (Fin k → Vector (n + 1)) → ℝ) (hf : Measurable f) :
    (∫ σ in Set.univ.pi (fun _ : Fin k => overlapRegion u A),
      f (fun i => SphericalPairCommonFrame.planeDirection u (σ i))
        ∂Measure.pi (fun _ : Fin k => sphereLaw (n + 1))) =
      ((sphereLaw (n + 1)).real (overlapRegion u A)) ^ k *
        ∫ y, f (fun i => (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u (y i))
          ∂Measure.pi (fun _ : Fin k => sphereLaw n) := by
  have hd : Measurable (SphericalPairCommonFrame.planeDirection u) := by
    unfold SphericalPairCommonFrame.planeDirection SphericalPairCommonFrame.planeScale overlap
    fun_prop
  rw [← integral_map (by fun_prop : Measurable (fun σ : Fin k → Vector (n + 1) =>
      fun i => SphericalPairCommonFrame.planeDirection u (σ i))).aemeasurable
      hf.aestronglyMeasurable,
    replicatedRestrictedSphere_planeDirection_map hn u hu hA, integral_smul_measure,
    integral_map (by fun_prop : Measurable (fun y : Fin k → Vector n =>
      fun i => (Real.sqrt (n : ℝ))⁻¹ • latitudeFrameAt u (y i))).aemeasurable
      hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_pow, Measure.real, smul_eq_mul]

/-- Section 2.1's sequential integration, in real probability units. -/
theorem overlapBlock_real_lower_of_slab {N k : ℕ}
    (ν : Measure (Vector N)) [IsProbabilityMeasure ν] (ρ a : ℝ) (ha : 0 ≤ a)
    (hslab : ∀ j : ℕ, j < k →
      ∀ᵐ (σ : Fin j → Vector N) ∂Measure.pi (fun _ : Fin j => ν),
        σ ∈ overlapBlock 0 ρ →
          a ≤ ν.real {y | ∀ i, |overlap y (σ i)| < ρ}) :
    a ^ k ≤ (Measure.pi (fun _ : Fin k => ν)).real (overlapBlock 0 ρ) := by
  have h := LiteratureSubagBandLowerFinal.overlapBlock_pi_lower_of_slab ν ρ
    (fun _ => ENNReal.ofReal a) (by
      intro j hj
      filter_upwards [hslab j hj] with σ hσ
      intro hb
      exact ENNReal.ofReal_le_of_le_toReal (hσ hb))
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) h
  simpa only [Finset.prod_const, Finset.card_range, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ha, Measure.real] using hr

/-- The actual Gibbs slab failure event, before the orthogonal-frame net
and Lemma 22 are used. No measurability is assumed in this definition. -/
def uniformSlabLowerTailEvent (N j : ℕ) (μ : FiniteMixture)
    (β ρ t : ℝ) : Set (Disorder N μ.maxDegree) :=
  {J | ¬ ∀ σ : Fin j → Vector N, (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
    σ ∈ overlapBlock 0 ρ →
    Real.exp (-t * (N : ℝ)) ≤
      (gibbsLaw N β (fieldOfMixture μ J)).real
        {y | ∀ i, |overlap y (σ i)| < ρ}}

/-- Outer probability of the genuine uniform slab failure event. -/
def uniformSlabLowerTailProbability (N j : ℕ) (μ : FiniteMixture)
    (β ρ t : ℝ) : ℝ :=
  (disorderLaw N μ.maxDegree).real (uniformSlabLowerTailEvent N j μ β ρ t)

/-- The finite union bound implementing Subag (2.18)--(2.19), with the
replica normalization retained exactly. -/
theorem zero_blockLowerTailProbability_le_uniformSlabs {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) (μ : FiniteMixture) (β ρ ε : ℝ) :
    blockLowerTailProbability N k μ β 0 ρ ε ≤
      ∑ j : Fin k, uniformSlabLowerTailProbability N j.val μ β ρ (ε / (k : ℝ)) := by
  let B : Fin k → Set (Disorder N μ.maxDegree) :=
    fun j => uniformSlabLowerTailEvent N j.val μ β ρ (ε / (k : ℝ))
  have hsub : {J | conditionalBlockProbability N k μ β 0 ρ J <
      Real.exp (-ε * (N : ℝ))} ⊆ ⋃ j, B j := by
    intro J hJ
    by_contra hnot
    have hgood (j : Fin k) : J ∉ B j := fun hj => hnot (mem_iUnion.mpr ⟨j, hj⟩)
    let ν := gibbsLaw N β (fieldOfMixture μ J)
    let _ := gibbsLaw_probability hN β (fieldOfMixture_contDiff μ J).continuous
    have hsupp (j : ℕ) :
        ∀ᵐ σ : Fin j → Vector N ∂Measure.pi (fun _ : Fin j => ν),
          ∀ i, ‖σ i‖ ^ 2 = (N : ℝ) :=
      eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin j => ν) (i := i)).eventually
          (gibbsLaw_support hN β (fieldOfMixture μ J)))
    have hslab (j : ℕ) (hj : j < k) (σ : Fin j → Vector N)
        (hσsphere : ∀ i, ‖σ i‖ ^ 2 = (N : ℝ))
        (hσ : σ ∈ overlapBlock 0 ρ) :
        Real.exp (-(ε / (k : ℝ)) * (N : ℝ)) ≤
          ν.real {y | ∀ i, |overlap y (σ i)| < ρ} := by
      have h := hgood ⟨j, hj⟩
      simp only [B, uniformSlabLowerTailEvent, mem_ofPred_eq, not_not] at h
      exact h σ hσsphere hσ
    have hp := overlapBlock_real_lower_of_slab (k := k) ν ρ
      (Real.exp (-(ε / (k : ℝ)) * (N : ℝ))) (Real.exp_pos _).le
      (fun j hj => (hsupp j).mono fun σ hσsphere hσ => hslab j hj σ hσsphere hσ)
    have hexp : Real.exp (-(ε / (k : ℝ)) * (N : ℝ)) ^ k =
        Real.exp (-ε * (N : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have hcond : conditionalBlockProbability N k μ β 0 ρ J =
        (Measure.pi (fun _ : Fin k => ν)).real (overlapBlock 0 ρ) := by
      rw [conditionalBlockProbability, GaussianReplicaKernel.iid_apply,
        allDimensionGibbsKernel_apply]
      rfl
    rw [hexp, ← hcond] at hp
    exact (not_lt_of_ge hp) hJ
  exact (measureReal_mono (μ := disorderLaw N μ.maxDegree) hsub).trans
    (measureReal_iUnion_fintype_le B)

/-- Uniform one-replica slab lower tails suffice for the exact zero-overlap
block lower tail. This is the probability-level part of Lemma 20. -/
theorem zero_blockLowerTail_tendsto_of_uniformSlabs {k : ℕ} (hk : 1 ≤ k)
    (μ : FiniteMixture) (β ρ : ℝ)
    (hslab : ∀ j : ℕ, j < k → ∀ t : ℝ, 0 < t →
      Tendsto (fun N => uniformSlabLowerTailProbability N j μ β ρ t) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
    hslab j.val j.isLt (ε / (k : ℝ)) (div_pos hε hkR))
  simp only [Finset.sum_const_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact .of_forall fun _ => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact zero_blockLowerTailProbability_le_uniformSlabs hN hk μ β ρ ε

/-- Subag's uniform slab step yields the previously encoded bounded
quenched block rate, without a contact or temperature restriction. -/
theorem zero_truncatedQuenchedBlockRate_tendsto_of_uniformSlabs {k : ℕ}
    (hk : 1 ≤ k) (μ : FiniteMixture) (β ρ : ℝ)
    (hslab : ∀ j : ℕ, j < k → ∀ t : ℝ, 0 < t →
      Tendsto (fun N => uniformSlabLowerTailProbability N j μ β ρ t) atTop (𝓝 0)) :
    Tendsto (fun N => truncatedQuenchedBlockRate N k μ β 0 ρ) atTop (𝓝 0) :=
  truncatedQuenchedBlockRate_tendsto_of_lowerTail k μ β 0 ρ
    (fun _ hε => zero_blockLowerTail_tendsto_of_uniformSlabs hk μ β ρ hslab hε)

/-- The multisamplability conclusion in Lemma 20 follows from exactly the
same spherical slab tails, at every real temperature. -/
theorem zero_multiSamplable_of_uniformSlabs (μ : FiniteMixture) (β : ℝ)
    (hslab : ∀ j : ℕ, ∀ ρ t : ℝ, 0 < ρ → 0 < t →
      Tendsto (fun N => uniformSlabLowerTailProbability N j μ β ρ t) atTop (𝓝 0)) :
    MultiSamplable μ β 0 := by
  apply multiSamplable_of_truncatedQuenchedBlockRate (by norm_num)
  intro k hk ρ hρ
  exact zero_truncatedQuenchedBlockRate_tendsto_of_uniformSlabs hk μ β ρ
    (fun j _ t ht => hslab j ρ t hρ ht)

/-- The derivative bound on regular disorder gives the correct extensive
Hamiltonian modulus along a latitude window. -/
theorem regularDisorder_latitude_field_variation {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n + 1) P) (hJ : J ∈ regularDisorder)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ x, inner ℝ (e x) u = 0)
    {r a η : ℝ} (hr : |r| ≤ 1) (ha : |a| ≤ 1) (hnear : |r - a| ≤ η)
    (y : Vector n) (hy : ‖y‖ ^ 2 = (n : ℝ)) :
    |field c J (latitudeMap u e r y) - field c J (latitudeMap u e a y)| ≤
      2 * derivativeConstant c * ((n + 1 : ℕ) : ℝ) * Real.sqrt η := by
  have hball (s : ℝ) (hs : |s| ≤ 1) :
      latitudeMap u e s y ∈ Metric.closedBall 0 (Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    rw [Metric.mem_closedBall, dist_zero_right,
      ← latitudeMap_norm_sq hn u hu e he hs y hy, Real.sqrt_sq (norm_nonneg _)]
  have hgrad (x : Vector (n + 1))
      (hx : x ∈ Metric.closedBall 0 (Real.sqrt ((n + 1 : ℕ) : ℝ))) :
      ‖fderiv ℝ (field c J) x‖ ≤ derivativeConstant c * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    have hg := (field_regularDisorder_ball_bounds (by omega : 1 ≤ n + 1) c J hJ x
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).2.1
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hg
  have hfield := (convex_closedBall (0 : Vector (n + 1))
    (Real.sqrt ((n + 1 : ℕ) : ℝ))).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (field_contDiff c J).differentiable (by simp) x)
      hgrad (hball a ha) (hball r hr)
  have hdist := latitudeMap_dist_le hn u hu e he hr ha y hy
  have hh := hfield.trans (mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (derivativeConstant_pos c).le (Real.sqrt_nonneg _)))
  have heq : derivativeConstant c * Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (2 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt |r - a|) =
      2 * derivativeConstant c * ((n + 1 : ℕ) : ℝ) * Real.sqrt |r - a| := by
    rw [show derivativeConstant c * Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (2 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt |r - a|) =
      2 * derivativeConstant c * (Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 *
        Real.sqrt |r - a| by ring,
      Real.sq_sqrt (Nat.cast_nonneg (n + 1))]
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnear)
    (mul_nonneg (mul_nonneg (by norm_num) (derivativeConstant_pos c).le)
      (Nat.cast_nonneg _)))

/-- Latitude thickening changes the replicated normalized Hamiltonian by
at most `O(sqrt η)`, independently of the replica count. -/
theorem regularDisorder_replicatedLatitude_variation {n P k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (c : Degree P → ℝ) (β : ℝ)
    (J : Disorder (n + 1) P) (hJ : J ∈ regularDisorder)
    (u : Vector (n + 1)) (hu : ‖u‖ ^ 2 = ((n + 1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n + 1)) (he : ∀ x, inner ℝ (e x) u = 0)
    {a η : ℝ} (ha : |a| ≤ 1) (r : Fin k → ℝ)
    (hr : ∀ i, |r i| ≤ 1) (hnear : ∀ i, |r i - a| ≤ η)
    (y : Fin k → Vector n) (hy : ∀ i, ‖y i‖ ^ 2 = (n : ℝ)) :
    |β * ∑ i : Fin k, (field c J (latitudeMap u e (r i) (y i)) -
      field c J (latitudeMap u e a (y i)))| /
        (((n + 1 : ℕ) : ℝ) * (k : ℝ)) ≤
      2 * |β| * derivativeConstant c * Real.sqrt η := by
  have hsum : |∑ i : Fin k, (field c J (latitudeMap u e (r i) (y i)) -
      field c J (latitudeMap u e a (y i)))| ≤
      (k : ℝ) * (2 * derivativeConstant c * ((n + 1 : ℕ) : ℝ) * Real.sqrt η) := by
    calc
      _ ≤ ∑ i : Fin k, |field c J (latitudeMap u e (r i) (y i)) -
          field c J (latitudeMap u e a (y i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, 2 * derivativeConstant c * ((n + 1 : ℕ) : ℝ) * Real.sqrt η :=
        Finset.sum_le_sum fun i _ => regularDisorder_latitude_field_variation
          hn c J hJ u hu e he (hr i) ha (hnear i) (y i) (hy i)
      _ = _ := by simp
  rw [abs_mul]
  apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))
    (Nat.cast_pos.mpr (by omega : 0 < k)))).mpr
  calc
    _ ≤ |β| * ((k : ℝ) *
        (2 * derivativeConstant c * ((n + 1 : ℕ) : ℝ) * Real.sqrt η)) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg β)
    _ = _ := by ring

namespace Endpoints

open SphericalMarkedWindows SphericalTAPCertificate
open LiteratureSubagRemark25Final
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open PureCapturePhysicalCoarseDiniAssembly SourcePureCaptureLiteralConsumer
open SphericalPureCapCenteringIdentity SphericalPureCapSourceScalars
open TwoAtomStationarity SourcePureCaptureWindowTransport PureCapturePhysicalDiagonalBridge
open PureStationarity
open CSParisiMeasure

/-- The pure capture endpoint now needs only Chen's finite-temperature formula. -/
theorem pure_capture_of_chen
    (hChen : Chen2013FiniteParisi) (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (U : Set ℝ)
    (hU : markK (FiniteMixture.pure p (by omega) 1 (by positivity)) β Q ∈ interior U) :
    (∃ b₀ : ℝ, b₀ ∈ Ioo (0 : ℝ) (Real.sqrt Q) ∧
      ∀ b : ℝ, b ∈ Ioc (0 : ℝ) b₀ → Tendsto
        (fun M : ℝ => Filter.limsup (pureConsumerUncovered p hp β Q M b U) atTop)
        atTop (𝓝 (0 : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M₀ w₀ : ℝ, 0 < M₀ ∧ 0 < w₀ ∧
      ∀ M w : ℝ, M₀ ≤ M → w₀ ≤ w →
        Filter.limsup (fun n => pureConsumerUncovered p hp β Q M
          (w / Real.sqrt (n+2 : ℕ)) U n) atTop ≤ ε) :=
  SourceMainTheoremsReducedFinal.pure_capture_of_chen_and_bands hChen p hp h U hU
    (LiteratureSubagBandUpperFinal.expectedBandUpperApproximation _)

/-- The pure coarse cover endpoint with its band hypothesis discharged. -/
theorem pure_coarse_cover_of_chen
    (hChen : Chen2013FiniteParisi) (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∀ a : ℝ, a < Real.sqrt Q → ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n => expectedUncoveredGibbsMass n
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β a
        (pureEnergyConstant p (by omega)) τ) atTop (𝓝 (0 : ℝ)) :=
  SourceMainTheoremsReducedFinal.pure_coarse_cover_of_chen_and_bands hChen p hp h
    (LiteratureSubagBandUpperFinal.expectedBandUpperApproximation _)

/-- The literal diagonal localization event, with no band premise. -/
theorem pure_diagonal_localization_of_chen
    (hChen : Chen2013FiniteParisi) (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (a : ℝ) (ha : a < Real.sqrt Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let e := pureEnergyConstant p (by omega : 3 ≤ p)
    let c := pureIntensityConstant p (by omega : 3 ≤ p)
    ∃ τ : ℕ → ℝ,
      (∀ n, 0 < τ n) ∧
      (∀ n, 1 ≤ ((n+2 : ℕ)*τ n)/(Real.log (n+2 : ℕ))^2) ∧
      Tendsto τ atTop (𝓝 0) ∧
      Tendsto (fun n => expectedUncoveredGibbsMass n μ β a e (τ n)) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)) ∧
      Tendsto (fun n => ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c))/(n+2 : ℕ))
        atTop (𝓝 (0 : ℝ)) ∧
      ∃ Ω : (n : ℕ) → Set (Disorder (n+2) μ.maxDegree),
        (∀ n, MeasurableSet (Ω n)) ∧
        Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n))
          atTop (𝓝 (1 : ℝ)) ∧
        ∀ n J, J ∈ Ω n → ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
          (n+2 : ℕ)*(e-τ n) ≤ field (mixtureCoefficients μ) J u →
          field (mixtureCoefficients μ) J u ∈ Icc
            (PureCaptureDiagonal.center e c n-
              ((n+2 : ℕ)*τ n-Real.log (n+2 : ℕ)/(2*c)))
            (PureCaptureDiagonal.center e c n+Real.sqrt (n+2 : ℕ)) :=
  SourceMainTheoremsReducedFinal.pure_diagonal_localization_of_chen_and_bands
    hChen p hp h a ha (LiteratureSubagBandUpperFinal.expectedBandUpperApproximation _)

/-- The physical directing-norm input with no remaining band premise. -/
theorem physicalDirectingNormQ_of_chen
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    PureCapturePhysicalCoarseDiniAssembly.PhysicalDirectingNormQ μ β Q :=
  SourceMainTheoremsReducedFinal.physicalDirectingNormQ_of_chen_and_bands hChen h
    (LiteratureSubagBandUpperFinal.expectedBandUpperApproximation _)

/-- Positive canonical potential excludes an actual replica block exponentially. -/
theorem replica_exclusion_of_positive_potential_of_chen
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β q : ℝ}
    (hβ : 0 < β) (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (canonicalMinimizer μ β).law q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) :=
  SourceMainTheoremsReducedFinal.replica_exclusion_of_positive_potential_of_chen_and_bands
    hChen hβ D (LiteratureSubagBandUpperFinal.expectedBandUpperApproximation D) hq hV

/-- A strict physical TAP gap suffices without any literature hypothesis. -/
theorem source_replica_exclusion_of_strict_tap_gap_of_chen
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hgap : tapValue D q < D.pressure) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c * (N : ℝ)) :=
  SourceMainTheoremsReducedFinal.source_replica_exclusion_of_strict_tap_gap_of_chen_and_bands
    D hβ (LiteratureSubagBandUpperFinal.expectedBandUpperApproximation D) hq hgap

end Endpoints

end SlowEquilibration.LiteratureSubagBandLowerProof
