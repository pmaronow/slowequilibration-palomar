-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagContact
public import SlowEquilibration.SourceGeneralTAPTelescope
public import SlowEquilibration.ThermalPhysicalZeroContact
public import SlowEquilibration.SourcePureSection9SmallClosures
public import SlowEquilibration.SourceLiteratureParisi
public import SlowEquilibration.SourceSubagReplicaCriterion

/-!
# Deterministic contact truncation in Subag's Theorem 10

This file proves the finite-temperature part (1.43) of Proposition 11 in
Subag, *Free energy landscapes in spherical spin glasses*, arXiv:1804.10576v6.
The residual measure is the actual truncated affine pushforward of the
canonical minimizer. No physical pressure formula is used for this step.

The full contact-to-multisamplability implication is reduced to a still-unproved
bounded quenched block-cost limit. Positivity and the passage to the original
annealed replicas are proved here. In particular, the zero-temperature formula
and the TAP criterion used in the published proof are not silently treated as
consequences of the finite-temperature Parisi formula.

The two reduced replica-criterion endpoints below need that remaining input
only at zero. The principal dynamical endpoints
`SourceFiniteMixtureMainLiteral.finiteMixture_main_condensed_and_initial_literal`
and `SourceMixedCountCapturePackage.finiteMixture_all_initial_spherical_of_literature`
already have no `Theorem10Forward` premise and are not duplicated.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagTheorem10Proof

open MeasureTheory Filter Set CrisantiSommers CSParisiMeasure
open LiteratureSubagPhysicalDefinitions LiteratureSubagContact
open SourceGeneralTAPTelescope
open SphericalModel ProbabilityTheory
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- For the repository's canonical minimizer, contact means zero first
variation, including for mixtures containing a quadratic term. -/
theorem contact_iff_firstVariation_zero (μ : FiniteMixture) (β q : ℝ) :
    Contact μ β q ↔ q ∈ Ico (0 : ℝ) 1 ∧
      firstVariation β μ.xi (canonicalMinimizer μ β).law q = 0 := by
  have hmax := (ThermalPhysicalZeroContact.minimizer_firstVariation_maximum_zero
    μ β (canonicalMinimizer μ β) (canonicalMinimizer_isMinimizer μ β)).1
  constructor
  · rintro ⟨hq, hc⟩
    refine ⟨hq, le_antisymm (hmax q hq) ?_⟩
    simpa [firstVariation, μ.xi_zero] using hc 0 (by norm_num)
  · rintro ⟨hq, hz⟩
    exact ⟨hq, fun r hr => hz ▸ hmax r hr⟩

/-- Interior contacts are stationary, as used before equation (6.4). -/
theorem contact_stationary {μ : FiniteMixture} {β q : ℝ}
    (hc : Contact μ β q) (hq : 0 < q) :
    β ^ 2 * μ.xi1 q =
      ∫ t in (0 : ℝ)..q, 1 / (xHat (canonicalMinimizer μ β).law t) ^ 2 := by
  have hlocal : IsLocalMax
      (firstVariation β μ.xi (canonicalMinimizer μ β).law) q := by
    filter_upwards [Ioo_mem_nhds hq hc.1.2] with r hr
    exact hc.2 r ⟨hr.1.le, hr.2⟩
  have hd := firstVariation_hasDerivAt β μ.xi (canonicalMinimizer μ β).law
    (canonicalMinimizer μ β).hasCutoff hc.1.2 (μ.hasDerivAt_xi q)
  exact sub_eq_zero.mp (hd.deriv.symm.trans hlocal.deriv_eq_zero)

private theorem inverseSquare_intervalIntegrable (ζ : Admissible)
    {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    IntervalIntegrable (fun t => 1 / (xHat ζ.law t) ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div ((xHat_continuous ζ.law ζ.hasCutoff).continuousOn.pow 2)
  intro t ht
  exact pow_ne_zero 2 (xHat_pos ζ.law ζ.hasCutoff
    (ht.2.trans_lt (max_lt ha hb))).ne'

/-- The inverse-square part of (6.4), with the exact affine Jacobian. -/
private theorem residual_inverseSquare_integral (ζ : Admissible)
    {q s : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hs : 0 ≤ s) :
    (∫ t in (0 : ℝ)..s, 1 / (xHat (residualTrial ζ hq).law t) ^ 2) =
      (1 - q) * ∫ v in q..(q + (1 - q) * s), 1 / (xHat ζ.law v) ^ 2 := by
  have ha : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) s,
      1 / (xHat (residualTrial ζ hq).law t) ^ 2 =
        (1 - q) ^ 2 * (1 / (xHat ζ.law ((1 - q) * t + q)) ^ 2) := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    rw [add_comm ((1 - q) * t) q, ← residual_xHat_scale ζ hq ht.1]
    field_simp
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (f := fun v => 1 / (xHat ζ.law v) ^ 2)
      (a := 0) (b := s) ha q]
  simp only [smul_eq_mul, mul_zero, zero_add]
  rw [add_comm ((1 - q) * s) q]
  field_simp

/-- Subag (6.5): the residual first variation is the translated original
first variation at a positive contact. -/
theorem contact_residual_firstVariation {μ : FiniteMixture} {β q : ℝ}
    (hc : Contact μ β q) (hq : 0 < q) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    firstVariation β (CSTAPTelescope.residualMixture μ ⟨hq, hc.1.2⟩).xi
        (residualTrial (canonicalMinimizer μ β) ⟨hq, hc.1.2⟩).law s =
      firstVariation β μ.xi (canonicalMinimizer μ β).law (q + (1 - q) * s) -
        firstVariation β μ.xi (canonicalMinimizer μ β).law q := by
  let ζ := canonicalMinimizer μ β
  let hq' : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hc.1.2⟩
  let ν := residualTrial ζ hq'
  let η := CSTAPTelescope.residualMixture μ hq'
  let F : ℝ → ℝ := fun t =>
    firstVariation β μ.xi ζ.law (q + (1 - q) * t) -
      firstVariation β μ.xi ζ.law q - firstVariation β η.xi ν.law t
  have hstat := contact_stationary hc hq
  have hder : ∀ t ∈ uIcc (0 : ℝ) s, HasDerivAt F 0 t := by
    intro t ht
    rw [uIcc_of_le hs.1] at ht
    have ht1 : t < 1 := ht.2.trans_lt hs.2
    have hu1 : q + (1 - q) * t < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hc.1.2) (sub_pos.mpr ht1)]
    have hlin := ((hasDerivAt_id t).const_mul (1 - q)).const_add q
    have hres : HasDerivAt η.xi
        ((1 - q) * (μ.xi1 (q + (1 - q) * t) - μ.xi1 q)) t := by
      have hd := (((μ.hasDerivAt_xi _).comp t hlin).sub_const (μ.xi q)).sub
        ((hasDerivAt_id t).const_mul ((1 - q) * μ.xi1 q))
      convert hd using 1
      · funext v
        exact CSTAPTelescope.residualMixture_xi μ hq' v
      · simp only [id_eq]
        ring
    have hφ := (firstVariation_hasDerivAt β μ.xi ζ.law ζ.hasCutoff hu1
      (μ.hasDerivAt_xi _)).comp t hlin
    have hψ := firstVariation_hasDerivAt β η.xi ν.law ν.hasCutoff ht1 hres
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (inverseSquare_intervalIntegrable ζ (by norm_num : (0 : ℝ) < 1) hc.1.2)
      (inverseSquare_intervalIntegrable ζ hc.1.2 hu1)
    have hscale := residual_inverseSquare_integral ζ hq' ht.1
    convert (hφ.sub_const (firstVariation β μ.xi ζ.law q)).sub hψ using 1
    · rfl
    · dsimp only [ζ] at hsplit hscale ⊢
      change (∫ t in (0 : ℝ)..t, 1 / (xHat ν.law t) ^ 2) = _ at hscale
      rw [hscale]
      nlinarith [hsplit, hstat]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (continuous_const.intervalIntegrable (0 : ℝ) s)
  have hz : F 0 = 0 := by
    simp [F, firstVariation, η, FiniteMixture.xi_zero]
  have hfinal : F s = 0 := by
    simpa only [intervalIntegral.integral_zero, hz, sub_zero] using hFTC.symm
  dsimp only [F, ζ, ν, η, hq'] at hfinal
  linarith

/-- Proposition 11 (1.43): at a positive contact, truncating the canonical
law gives the canonical law of the actual Taylor residual mixture. -/
private theorem contact_residualTrial_eq_canonical {μ : FiniteMixture} {β q : ℝ}
    (hc : Contact μ β q) (hq : 0 < q) :
    residualTrial (canonicalMinimizer μ β) ⟨hq, hc.1.2⟩ =
      canonicalMinimizer (CSTAPTelescope.residualMixture μ ⟨hq, hc.1.2⟩) β := by
  let ζ := canonicalMinimizer μ β
  let hq' : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hc.1.2⟩
  let ν := residualTrial ζ hq'
  let η := CSTAPTelescope.residualMixture μ hq'
  have hz := ((contact_iff_firstVariation_zero μ β q).mp hc).2
  have hmax : ∀ s ∈ Ico (0 : ℝ) 1, firstVariation β η.xi ν.law s ≤ 0 := by
    intro s hs
    rw [contact_residual_firstVariation hc hq hs]
    exact sub_nonpos.mpr (hc.2 _ ⟨add_nonneg hq.le
      (mul_nonneg (sub_pos.mpr hc.1.2).le hs.1),
      by nlinarith [mul_pos (sub_pos.mpr hc.1.2) (sub_pos.mpr hs.2)]⟩)
  let c := residualMap q ζ.cutoff
  have hc1 : c < 1 := residualMap_lt_one hq' ζ.hasCutoff.2.1
  have hcut : HasCutoff ν.law c := residualTrial_hasCutoff ζ hq' ζ.hasCutoff
  have hcont : Continuous (fun t => firstVariation β η.xi ν.law (min t c)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (firstVariation_hasDerivAt β η.xi ν.law ν.hasCutoff
      ((min_le_right t c).trans_lt hc1) (η.hasDerivAt_xi _)).continuousAt.comp
      (f := fun t : ℝ => min t c)
      (continuous_id.min continuous_const).continuousAt
  have hae : ∀ᵐ t ∂ν.law, firstVariation β η.xi ν.law (min t c) = 0 := by
    change ∀ᵐ t ∂ζ.law.map (residualMap q),
      firstVariation β η.xi ν.law (min t c) = 0
    apply (ae_map_iff (residualMap_continuous q).measurable.aemeasurable
      (isClosed_eq hcont continuous_const).measurableSet).mpr
    have hbase := (ThermalPhysicalZeroContact.minimizer_firstVariation_maximum_zero
      μ β ζ (canonicalMinimizer_isMinimizer μ β)).2.1
    filter_upwards [ζ.hasCutoff.2.2, hbase] with r hr hrzero
    have ht := residualMap_mem hq' hr
    rw [min_eq_left ht.2]
    by_cases hrq : r ≤ q
    · have he : residualMap q r = 0 := max_eq_left
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrq) (sub_pos.mpr hc.1.2).le)
      simp [he, firstVariation, η, FiniteMixture.xi_zero]
    · have hqr : q ≤ r := (lt_of_not_ge hrq).le
      have he : q + (1 - q) * residualMap q r = r := by
        rw [residualMap, max_eq_right
          (div_nonneg (sub_nonneg.mpr hqr) (sub_pos.mpr hc.1.2).le)]
        field_simp [(sub_pos.mpr hc.1.2).ne']
        ring
      rw [contact_residual_firstVariation hc hq ⟨ht.1, ht.2.trans_lt hc1⟩, he]
      exact sub_eq_zero.mpr (hrzero.trans hz.symm)
  have hsupport : ∀ᵐ t ∂ν.law, firstVariation β η.xi ν.law t = 0 := by
    filter_upwards [hcut.2.2, hae] with t ht he
    simpa only [min_eq_left ht.2] using he
  apply eq_canonicalMinimizer_of_isMinimizer
  exact (ν.minimizer_iff_support_on_maximum β η.xi
    (fun r _ => (η.hasDerivAt_xi r).continuousAt.continuousWithinAt)).mpr
      ⟨0, hmax, hsupport⟩

/-- The residual clause of the general contact theorem, with all its
literature hypotheses removed. This is the literal affine pushforward
asserted in Subag's Proposition 11 (1.43). -/
theorem contact_residual_canonical_reduced {μ : FiniteMixture} {β q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0) :
    (canonicalMinimizer (LiteratureSubagTAP.physicalResidualMixture μ q hq) β).law =
      (canonicalMinimizer μ β).law.map (fun r => max 0 ((r - q) / (1 - q))) := by
  have hc : Contact μ β q := (contact_iff_firstVariation_zero μ β q).mpr
    ⟨⟨hq.1.le, hq.2⟩, neg_eq_zero.mp hV⟩
  exact (congrArg Admissible.law (contact_residualTrial_eq_canonical hc hq.1)).symm

/-- The contact telescope with the residual canonical minimum. The ground
term is still a trial: its optimality and identification with the physical
ground limit are not asserted by this identity. -/
theorem contact_variational_telescope {μ : FiniteMixture} {β q : ℝ}
    (hβ : 0 < β) (hc : Contact μ β q) (hq : 0 < q) :
    variationalValue μ β =
      β * CSTAPGroundTrialQuadratic.functional μ β (canonicalMinimizer μ β).law q 0 +
        Real.log (1 - q) / 2 +
          variationalValue (CSTAPTelescope.residualMixture μ ⟨hq, hc.1.2⟩) β := by
  have ht := canonical_telescope μ hβ ⟨hq, hc.1.2⟩
  rw [contact_residualTrial_eq_canonical hc hq] at ht
  exact ht

/-- Under Chen's finite-temperature formula, both physical pressures in
the contact telescope have the asserted difference. No ground-state or
Subag interface is a premise. -/
theorem contact_pressure_difference_limit
    (hChen : SourceLiteratureParisi.Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β)
    (hc : Contact μ β q) (hq : 0 < q) :
    Tendsto (fun N : ℕ => quenchedPressure N μ β -
      quenchedPressure N (CSTAPTelescope.residualMixture μ ⟨hq, hc.1.2⟩) β) atTop
      (𝓝 (β * CSTAPGroundTrialQuadratic.functional μ β
        (canonicalMinimizer μ β).law q 0 + Real.log (1 - q) / 2)) := by
  have ht := (hChen μ β hβ.le).sub
    (hChen (CSTAPTelescope.residualMixture μ ⟨hq, hc.1.2⟩) β hβ.le)
  convert ht using 1
  congr 1
  linarith [contact_variational_telescope hβ hc hq]

private theorem pi_fin_absolutelyContinuous {V : Type*} [MeasurableSpace V]
    (μ ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ ≪ ν) (k : ℕ) :
    Measure.pi (fun _ : Fin k => μ) ≪ Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero =>
      rw [Measure.pi_of_empty _ Fin.elim0, Measure.pi_of_empty _ Fin.elim0]
  | succ n ih =>
      have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm.map_eq
      have hn := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).symm.map_eq
      rw [← hm, ← hn]
      exact (MeasurableEquiv.measurableEmbedding
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) 0).symm).absolutelyContinuous_map
          (h.prod ih)

private theorem exists_overlap_center {N : ℕ} (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * Q := by
  let _ := sphereLaw_probability N
  obtain ⟨u, hu⟩ := (sphereLaw_support hN).exists
  refine ⟨Real.sqrt Q • u, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hQ, hu]
  ring

private theorem overlap_block_volume_positive {N k : ℕ}
    (hNk : k + 1 ≤ N) (hk : 1 ≤ k) {q ρ : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      {σ : Fin k → Vector N | ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ} := by
  have hN : 1 ≤ N := by omega
  by_cases hq0 : q = 0
  · subst q
    let Q : ℝ := min (ρ / 2) (1 / 2)
    have hQ : Q ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_min (by linarith) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    obtain ⟨m, hm⟩ := exists_overlap_center hN hQ.1.le
    have hv := SourcePureSection9SmallClosures.replicatedBand_volume_positive hNk hk hQ
      (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < ρ / 2) m hm
    apply hv.trans_le
    apply measure_mono
    intro σ hσ i j hij
    simp only [sub_zero]
    have hb := hσ.2 i j hij
    have ht : |overlap (σ i) (σ j)| ≤ |overlap (σ i) (σ j) - Q| + Q := by
      calc
        _ = |(overlap (σ i) (σ j) - Q) + Q| := by congr 1; ring
        _ ≤ |overlap (σ i) (σ j) - Q| + |Q| := abs_add_le _ _
        _ = _ := by rw [abs_of_pos hQ.1]
    have hQρ : Q ≤ ρ / 2 := min_le_left _ _
    linarith
  · have hQ : q ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩
    obtain ⟨m, hm⟩ := exists_overlap_center hN hq.1
    have hv := SourcePureSection9SmallClosures.replicatedBand_volume_positive hNk hk hQ
      (by norm_num : (0 : ℝ) < 1) hρ m hm
    exact hv.trans_le (measure_mono fun σ hσ => hσ.2)

private theorem conditional_overlap_block_positive {N k : ℕ}
    (hNk : k + 1 ≤ N) (hk : 1 ≤ k) (μ : FiniteMixture) (β : ℝ)
    {q ρ : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ)
    (J : Disorder N μ.maxDegree) :
    0 < (GaussianReplicaKernel.iid
      (allDimensionGibbsKernel (mixtureCoefficients μ) β) k J)
      {σ : Fin k → Vector N | ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ} := by
  have hN : 1 ≤ N := by omega
  let _ := sphereLaw_probability N
  have hH := (field_contDiff (mixtureCoefficients μ) J).continuous
  let _ := gibbsLaw_probability hN β hH
  have hrev : sphereLaw N ≪ gibbsLaw N β (field (mixtureCoefficients μ) J) := by
    apply withDensity_absolutelyContinuous'
    · exact (gibbsDensity_continuous β hH).measurable.ennreal_ofReal.aemeasurable
    · exact .of_forall fun x =>
        (ENNReal.ofReal_pos.mpr (gibbsDensity_pos hN β hH x)).ne'
  have hprod := pi_fin_absolutelyContinuous _ _ hrev k
  rw [GaussianReplicaKernel.iid_apply, allDimensionGibbsKernel_apply]
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (ne_of_gt (overlap_block_volume_positive hNk hk hq hρ)) (hprod hz)

/-- Positivity in the literal definition of multisamplability is automatic
in dimensions `N ≥ k+1`, for every overlap in `[0,1)`. -/
theorem expectedOverlapBlockProbability_pos {N k : ℕ}
    (hNk : k + 1 ≤ N) (hk : 1 ≤ k) (μ : FiniteMixture) (β : ℝ)
    {q ρ : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    0 < expectedOverlapBlockProbability N k μ β q ρ := by
  let G := allDimensionGibbsKernel (N := N) (mixtureCoefficients μ) β
  let d := disorderLaw N μ.maxDegree
  let E : Set (Fin k → Vector N) :=
    {σ | ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ}
  have hann : (GaussianReplicaKernel.law d G k) E ≠ 0 := by
    intro hz
    have hae : ∀ᵐ σ ∂(GaussianReplicaKernel.iid G k ∘ₘ d), σ ∉ E :=
      measure_eq_zero_iff_ae_notMem.mp hz
    obtain ⟨J, hJ⟩ := (Measure.ae_ae_of_ae_comp hae).exists
    have hzJ : (GaussianReplicaKernel.iid G k J) E = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr hJ
    exact (ne_of_gt (conditional_overlap_block_positive hNk hk μ β hq hρ J)) hzJ
  exact ENNReal.toReal_pos hann (measure_ne_top _ _)

/-- The equilateral replica event in Subag's Definition 2. -/
def overlapBlock {N k : ℕ} (q ρ : ℝ) : Set (Fin k → Vector N) :=
  {σ | ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ}

private theorem overlapBlock_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

/-- The original Gibbs block probability before disorder averaging. -/
def conditionalBlockProbability (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) : ℝ :=
  (GaussianReplicaKernel.iid
    (allDimensionGibbsKernel (mixtureCoefficients μ) β) k J).real (overlapBlock q ρ)

private theorem conditionalBlockProbability_integrable (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) :
    Integrable (conditionalBlockProbability N k μ β q ρ) (disorderLaw N μ.maxDegree) :=
  Kernel.IsMarkovKernel.integrable _ _ (overlapBlock_measurable q ρ)

private theorem expectedOverlapBlockProbability_eq_integral (N k : ℕ)
    (μ : FiniteMixture) (β q ρ : ℝ) :
    expectedOverlapBlockProbability N k μ β q ρ =
      ∫ J, conditionalBlockProbability N k μ β q ρ J ∂disorderLaw N μ.maxDegree := by
  unfold expectedOverlapBlockProbability GaussianReplicaKernel.law
    conditionalBlockProbability Measure.real
  rw [integral_toReal]
  · exact congrArg ENNReal.toReal
      (Measure.bind_apply (overlapBlock_measurable q ρ) (Kernel.aemeasurable _))
  · exact (Kernel.measurable_coe _ (overlapBlock_measurable q ρ)).aemeasurable
  · exact .of_forall fun _ => measure_lt_top _ _

/-- A bounded quenched block cost for the actual conditional Gibbs replicas.
The exponential floor makes the logarithm integrable in every dimension;
it is removed in the proved passage to multisamplability below. -/
def truncatedQuenchedBlockRate (N k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) : ℝ :=
  (∫ J, Real.log (max (conditionalBlockProbability N k μ β q ρ J)
    (Real.exp (-(N : ℝ)))) ∂disorderLaw N μ.maxDegree) / (N : ℝ)

private theorem truncatedBlock_jensen (N k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) :
    Real.exp (∫ J, Real.log (max (conditionalBlockProbability N k μ β q ρ J)
      (Real.exp (-(N : ℝ)))) ∂disorderLaw N μ.maxDegree) ≤
      expectedOverlapBlockProbability N k μ β q ρ + Real.exp (-(N : ℝ)) := by
  let d := disorderLaw N μ.maxDegree
  let f := conditionalBlockProbability N k μ β q ρ
  let a := Real.exp (-(N : ℝ))
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))
  have hf : Measurable f :=
    (Kernel.measurable_coe _ (overlapBlock_measurable q ρ)).ennreal_toReal
  have hfi : Integrable f d := conditionalBlockProbability_integrable N k μ β q ρ
  have hg : Integrable (fun J => max (f J) a) d := by
    refine (integrable_const (1 : ℝ)).mono'
      ((hf.max measurable_const).aestronglyMeasurable) (.of_forall fun J => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans (le_max_right _ _))]
    exact max_le measureReal_le_one ha1
  have hglog : Integrable (fun J => Real.log (max (f J) a)) d := by
    refine (integrable_const (N : ℝ)).mono'
      ((hf.max measurable_const).log.aestronglyMeasurable) (.of_forall fun J => ?_)
    have hlo := Real.log_le_log ha (le_max_right (f J) a)
    have hhi : Real.log (max (f J) a) ≤ 0 := Real.log_nonpos
      (ha.le.trans (le_max_right _ _)) (max_le measureReal_le_one ha1)
    rw [Real.norm_eq_abs]
    have halog : Real.log a = -(N : ℝ) := Real.log_exp _
    exact abs_le.mpr ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) N]⟩
  have hj := SphericalModel.integral_log_le_log_integral d hg hglog
    (.of_forall fun J => ha.trans_le (le_max_right _ _))
  have he := Real.exp_le_exp.mpr hj
  rw [Real.exp_log (integral_pos_iff_support_of_nonneg_ae
    (.of_forall fun J => (ha.trans_le (le_max_right (f J) a)).le) hg |>.mpr (by
      have hs : Function.support (fun J => max (f J) a) = univ := by
        ext J
        simp only [Function.mem_support, mem_univ, iff_true]
        exact (ha.trans_le (le_max_right _ _)).ne'
      rw [hs]
      simp))] at he
  apply he.trans
  rw [expectedOverlapBlockProbability_eq_integral]
  calc
    _ ≤ ∫ J, f J + a ∂d := integral_mono hg (hfi.add (integrable_const a))
      (fun J => max_le_add_of_nonneg measureReal_nonneg ha.le)
    _ = _ := by
      rw [integral_add hfi (integrable_const a), integral_const]
      simp only [probReal_univ, one_smul]
      rfl

/-- Jensen's inequality and the exponential floor give the exact,
positivity-aware multisamplability conclusion from a bounded quenched
block-cost limit. This lemma discharges all analytic passage to the
annealed probability appearing in Definition 2. -/
theorem multiSamplable_of_truncatedQuenchedBlockRate {μ : FiniteMixture} {β q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hRate : ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun N : ℕ => truncatedQuenchedBlockRate N k μ β q ρ)
        atTop (𝓝 (0 : ℝ))) :
    MultiSamplable μ β q := by
  intro k hk ρ hρ
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (k + 1)] with N hN
    exact expectedOverlapBlockProbability_pos hN hk μ β hq hρ
  · let M : ℕ → ℝ := fun N => ∫ J,
      Real.log (max (conditionalBlockProbability N k μ β q ρ J)
        (Real.exp (-(N : ℝ)))) ∂disorderLaw N μ.maxDegree
    have ht := hRate k hk ρ hρ
    have hhalf : ∀ᶠ N : ℕ in atTop, -(N : ℝ) / 2 ≤ M N := by
      have hh := ht.eventually (lt_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0))
      filter_upwards [hh, eventually_gt_atTop 0] with N hN hNp
      have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hNp
      change -1 / 2 < M N / (N : ℝ) at hN
      have hb := (lt_div_iff₀ hNr).mp hN
      linarith
    have hlarge : ∀ᶠ N : ℕ in atTop, 2 * Real.log 2 ≤ (N : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (2 * Real.log 2))
    have hlower : ∀ᶠ N : ℕ in atTop,
        truncatedQuenchedBlockRate N k μ β q ρ - Real.log 2 / (N : ℝ) ≤
          Real.log (expectedOverlapBlockProbability N k μ β q ρ) / (N : ℝ) := by
      filter_upwards [hhalf, hlarge] with N hN hNl
      have ha : Real.exp (-(N : ℝ)) ≤ Real.exp (M N) / 2 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
        calc
          _ = Real.exp (-(N : ℝ) + Real.log 2) := by
            rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
      have hj := truncatedBlock_jensen N k μ β q ρ
      change Real.exp (M N) ≤ _ at hj
      have hb : Real.exp (M N) / 2 ≤ expectedOverlapBlockProbability N k μ β q ρ := by
        linarith
      have hl := Real.log_le_log (div_pos (Real.exp_pos (M N)) (by norm_num)) hb
      rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_exp] at hl
      have hd := div_le_div_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) N)
      simpa only [truncatedQuenchedBlockRate, M, sub_div] using hd
    have hupper : ∀ N : ℕ,
        Real.log (expectedOverlapBlockProbability N k μ β q ρ) / (N : ℝ) ≤ 0 := by
      intro N
      exact div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos measureReal_nonneg measureReal_le_one) (Nat.cast_nonneg N)
    have hsmall : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hlowlim := ht.sub hsmall
    simp only [sub_zero] at hlowlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim tendsto_const_nhds
      hlower (.of_forall hupper)

/-- A separate, explicitly conditional reduction of the exact Theorem 10
interface. The still-unproved input is the physical quenched block-cost
limit at contacts; it is not an axiom or a claimed literature proof. -/
theorem theorem10Forward_of_contact_block_rate {μ : FiniteMixture} {β : ℝ}
    (hβ : 0 < β)
    (hRate : ∀ q : ℝ, Contact μ β q → ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun N : ℕ => truncatedQuenchedBlockRate N k μ β q ρ)
        atTop (𝓝 (0 : ℝ))) :
    Theorem10Forward μ β :=
  ⟨hβ, fun q hc => multiSamplable_of_truncatedQuenchedBlockRate hc.1 (hRate q hc)⟩

/-- The source TAP criterion on `[0,1)`, replacing Theorem 10 by just the
still-unproved zero-overlap block-cost limit. Positive overlaps use the
existing Theorem 5 premise. -/
theorem source_subag_tap_reduced {μ : FiniteMixture} {β : ℝ}
    (D : LiteratureSubagTAP.ThermodynamicData μ β)
    (h5 : LiteratureSubagTAP.Theorem5 D)
    (hZeroRate : ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun N : ℕ => truncatedQuenchedBlockRate N k μ β 0 ρ)
        atTop (𝓝 (0 : ℝ)))
    {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    SourceSubagReplicaCriterion.sourceTAPValue D q ≤ D.pressure ∧
      (D.pressure = SourceSubagReplicaCriterion.sourceTAPValue D q ↔
        MultiSamplable μ β q) := by
  by_cases hz : q = 0
  · subst q
    have hm := multiSamplable_of_truncatedQuenchedBlockRate (by norm_num) hZeroRate
    simpa only [SourceSubagReplicaCriterion.sourceTAPValue, ite_true, sub_zero,
      Real.log_one, zero_div, mul_zero, zero_add] using
      And.intro (le_refl D.pressure) (iff_of_true (Eq.refl D.pressure) hm)
  · have hpos : q ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hq.1 (Ne.symm hz), hq.2⟩
    simpa only [SourceSubagReplicaCriterion.sourceTAPValue, ite_eq_right hz] using
      And.intro (h5.2 q hpos).2 (h5.2 q hpos).1

/-- The extended-real source replica criterion, replacing Theorem 10 by
just the still-unproved zero-overlap block-cost limit. The existing
positive-overlap exclusion premise remains explicit. -/
theorem source_replica_criterion_reduced {μ : FiniteMixture} {β q : ℝ}
    (h25 : LiteratureSubagReplicaExclusion.Remark25Contrapositive μ β)
    (hZeroRate : ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun N : ℕ => truncatedQuenchedBlockRate N k μ β 0 ρ)
        atTop (𝓝 (0 : ℝ)))
    (hq : q ∈ Ico (0 : ℝ) 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      limsup (fun N : ℕ => SourceSubagReplicaCriterion.replicaLogRate N k μ β q ρ)
        atTop = 0) ↔ MultiSamplable μ β q := by
  constructor
  · intro hcrit
    by_cases hz : q = 0
    · subst q
      exact multiSamplable_of_truncatedQuenchedBlockRate (by norm_num) hZeroRate
    · by_contra hn
      obtain ⟨k, hk, ρ, hρ, c, hc, hb⟩ := h25.2 q
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hz), hq.2⟩ hn
      have hr : ∀ᶠ N : ℕ in atTop,
          SourceSubagReplicaCriterion.replicaLogRate N k μ β q ρ ≤ ((-c : ℝ) : EReal) := by
        filter_upwards [hb, eventually_gt_atTop 0] with N hN hNp
        unfold SourceSubagReplicaCriterion.replicaLogRate
        split_ifs with hp
        · exact bot_le
        · have hpos : 0 < expectedOverlapBlockProbability N k μ β q ρ :=
            lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
          have hl := Real.log_le_log hpos hN
          rw [Real.log_exp] at hl
          exact EReal.coe_le_coe_iff.mpr
            ((div_le_iff₀ (Nat.cast_pos.mpr hNp)).mpr hl)
      have hlim := limsup_le_of_le (h := hr)
      rw [hcrit k hk ρ hρ] at hlim
      have hneg : ((-c : ℝ) : EReal) < 0 := by
        exact_mod_cast neg_neg_of_pos hc
      exact (not_le_of_gt hneg) hlim
  · intro hm k hk ρ hρ
    obtain ⟨hp, ht⟩ := hm k hk ρ hρ
    apply Filter.Tendsto.limsup_eq
    apply (EReal.tendsto_coe.mpr ht).congr'
    filter_upwards [hp] with N hN
    simp only [SourceSubagReplicaCriterion.replicaLogRate, ite_eq_right hN.ne']

end SlowEquilibration.LiteratureSubagTheorem10Proof
