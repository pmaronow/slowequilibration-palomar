-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureSeparationDisjoint
public import SlowEquilibration.SourceMixedOnePointInterface
public import SlowEquilibration.SourcePureAboveStaticCertificate

/-! Subag's Corollary 13, equation (2.11), in the original-field maximum
convention. For degrees at least four the proved simultaneous-retention
and selection geometry give the exact separation interface without a
literature hypothesis. The cubic case is reduced separately to the
ordered-pair first moment used in the published argument.

The two finite-mixture principal endpoints named in the task do not use
this interface. Its actual consumers are restated below.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourcePureSeparationCorollary13Proof

open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalForm
open SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity PureStationarity
open PairConditionalDeterminantMoments SourcePureSeparationDisjoint
open SourceMixedOnePointInterface SourceMixedFilterInterface
open SphericalPureCapSourceScalars SphericalPureCenterFieldScale
open SourcePureCaptureWindowTransport
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A constant prefactor costs at most half the exponential rate. -/
private theorem exponential_prefactor_absorption (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      A * Real.exp (-c * (n+2 : ℕ)) ≤ Real.exp (-(c/2) * (n+2 : ℕ)) := by
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hlim : Tendsto (fun n : ℕ => A * Real.exp (-(c/2) * (n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (hN.const_mul_atTop (half_pos hc))).const_mul A
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn
  calc
    _ = (A * Real.exp (-(c/2) * (n+2 : ℕ))) *
        Real.exp (-(c/2) * (n+2 : ℕ)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hn.le (Real.exp_pos _).le

/-- Homogeneity transports the original near-ground interval into the
center-field high-critical threshold used by simultaneous retention. -/
private theorem original_nearGround_is_high (p : ℕ) (hp : 4 ≤ p)
    {β x Q δ : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (n : ℕ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
    {u : Vector (n+2)}
    (hu : u ∈ nearGroundCriticalSet p (by omega) n J (δ/(Real.sqrt Q)^p)) :
    surfaceGradient (field (centerCoefficients (mixtureCoefficients
      (FiniteMixture.pure p (by omega) 1 (by positivity))) Q) J) u = 0 ∧
    (n+2 : ℕ) * (markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q - δ) ≤
      field (centerCoefficients (mixtureCoefficients
        (FiniteMixture.pure p (by omega) 1 (by positivity))) Q) J u := by
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p
  have hE := (sourcePure_certificate_scalar_coordinates p hp h).1
  have hgrad := pure_center_surfaceGradient_eq_original_scale p (by omega) 1
    (by positivity) h.overlap_range.1.le (n+2) J u
  constructor
  · rw [hgrad, hu.2.1, smul_zero]
  · rw [pure_center_field_eq_original_scale p (by omega) 1 (by positivity)
      h.overlap_range.1.le, hE]
    have hlo := mul_le_mul_of_nonneg_left hu.2.2.1 hs.le
    have hid : s * ((n+2 : ℕ) * (pureEnergyConstant p (by omega) - δ/s)) =
        (n+2 : ℕ) * (pureEnergyConstant p (by omega) * s - δ) := by
      field_simp
    dsimp only [s] at hid hlo
    rw [hid] at hlo
    exact hlo

/-- The exact Corollary 13 interface for every degree at least four.
The proof uses proved one-point retention and its closed-collar geometry;
neither a literature interface nor a Parisi hypothesis is required. -/
theorem corollary13_degree_ge_four (p : ℕ) (hp : 4 ≤ p) :
    Corollary13 p (by omega) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let β := Thresholds.staticThreshold (fun r : ℝ => r^p) + 1
  obtain ⟨x,Q,h⟩ := pure_certificate_above_static p hp
    (show Thresholds.staticThreshold (fun r : ℝ => r^p) < β by dsimp [β]; linarith)
  let K := markK μ β Q
  let B := sourceRadialEdge μ Q
  have hBK : B < K := sourceContact_markK_above_edge μ h
  let L₀ := (B+K)/2
  let R₀ := K+1
  obtain ⟨C,hκ,hC,hη,hηone,hCommon⟩ := pure_onePoint_interface p (by omega) 1
    (by positivity) h (L₀ := L₀) (R₀ := R₀)
    (show B < L₀ by dsimp [L₀]; linarith)
    (show K ∈ Ioo L₀ R₀ by constructor <;> dsimp [L₀,R₀] <;> linarith)
  let κ := (L₀-B)/4
  let η := 1-Real.cos (min (Real.pi/4) (κ/(2*C)))
  intro ε hε
  let ε' := min ε ((1-η)/2)
  have hε' : 0 < ε' := lt_min hε (by dsimp [η] at *; linarith)
  have hεη : ε' < 1-η := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨l,r,δ,_hL,_hR,hδG,⟨D⟩⟩ := hCommon ε' hε' hεη
  have hδ : 0 < δ := D.admissible.width
  have hG : 0 < LatitudeGroundTrial.gap μ Q (markY β Q) (markZ x Q) ε' η := by
    linarith
  obtain ⟨c,A,hc,_hA,Ω,_hΩm,hΩp,hΩ⟩ := D.simultaneous_retention
  let s := (Real.sqrt Q)^p
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr h.overlap_range.1) p
  refine ⟨δ/s,c/2,div_pos hδ hs,half_pos hc,?_⟩
  filter_upwards [exponential_prefactor_absorption A hc] with n hn
  apply le_trans (measureReal_mono (s₂ := (Ω n)ᶜ) ?_ (measure_ne_top _ _))
    ((hΩp n).trans hn)
  rintro J ⟨u,hu,v,hv,huv,_huvneg,hOverlap⟩ hJ
  have hcritU := original_nearGround_is_high p hp h n J hu
  have hcritV := original_nearGround_is_high p hp h n J hv
  have hSel := ((hΩ n J hJ).2.2 u hu.1 hcritU.1 hcritU.2).2.2
  have hExclude := (selection_exact_exclusion
    (centerCoefficients (mixtureCoefficients μ) Q) J hκ hC
    (show η ≤ 1-Real.cos (min (Real.pi/4) (κ/(2*C))) from le_rfl)
    (show δ < LatitudeGroundTrial.gap μ Q (markY β Q) (markZ x Q) ε' η/2 by linarith)
    u hu.1 hcritU.1 hSel).2 v hv.1 hcritV.1 hcritV.2 huv.symm
  exact (not_lt_of_ge ((min_le_left _ _).trans hOverlap)) hExclude

/-- Literal ordered pairs in the exact closed energy window and with the
exact two exclusions of `Corollary13`. No finiteness is assumed. -/
def nearGroundPairSet (p : ℕ) (hp : 3 ≤ p) (n : ℕ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
    (d ε : ℝ) : Set (Vector (n+2) × Vector (n+2)) :=
  {z | z.1 ∈ nearGroundCriticalSet p hp n J d ∧
    z.2 ∈ nearGroundCriticalSet p hp n J d ∧
    z.1 ≠ z.2 ∧ z.1 ≠ -z.2 ∧ ε ≤ overlap z.1 z.2}

/-- The ordered factorial count used in the first-moment proof of the
published corollary, with both antipodal and diagonal pairs removed. -/
def nearGroundPairCount (p : ℕ) (hp : 3 ≤ p) (n : ℕ)
    (J : Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree)
    (d ε : ℝ) : ℝ≥0∞ :=
  ∑' _z : nearGroundPairSet p hp n J d ε, (1 : ℝ≥0∞)

/-- The pair-existence event is Borel even for non-Morse disorders.
Positive distance cutoffs make it a countable union of compact-witness
projections of closed sets. -/
private theorem nearGroundPairEvent_measurable (p : ℕ) (hp : 3 ≤ p)
    (n : ℕ) (d ε : ℝ) :
    MeasurableSet
      {J | ∃ u ∈ nearGroundCriticalSet p hp n J d,
        ∃ v ∈ nearGroundCriticalSet p hp n J d,
          u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let S := {u : Vector (n+2) | ‖u‖^2 = (n+2 : ℕ)}
  let : CompactSpace S :=
    isCompact_iff_compactSpace.mp (sourceSphere_compact (n+2))
  have hC : IsClosed
      {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
        z.2 ∈ nearGroundCriticalSet p hp n z.1 d} := by
    exact (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).inter
      ((isClosed_eq
        (source_surfaceGradient_joint_contDiff (mixtureCoefficients μ)).continuous
        continuous_const).inter
        (isClosed_Icc.preimage (field_jointContinuous (mixtureCoefficients μ))))
  let A := fun k : ℕ =>
    {z : Disorder (n+2) μ.maxDegree × (S × S) |
      z.2.1.1 ∈ nearGroundCriticalSet p hp n z.1 d ∧
      z.2.2.1 ∈ nearGroundCriticalSet p hp n z.1 d ∧
      1 / (k+1 : ℝ) ≤ dist z.2.1.1 z.2.2.1 ∧
      1 / (k+1 : ℝ) ≤ dist z.2.1.1 (-z.2.2.1) ∧
      ε ≤ overlap z.2.1.1 z.2.2.1}
  have hu : Continuous
      (fun z : Disorder (n+2) μ.maxDegree × (S × S) => z.2.1.1) :=
    continuous_subtype_val.comp continuous_snd.fst
  have hv : Continuous
      (fun z : Disorder (n+2) μ.maxDegree × (S × S) => z.2.2.1) :=
    continuous_subtype_val.comp continuous_snd.snd
  have hR : Continuous
      (fun z : Disorder (n+2) μ.maxDegree × (S × S) =>
        overlap z.2.1.1 z.2.2.1) := by
    unfold overlap
    exact (hu.inner hv).div_const _
  have hA : ∀ k, IsClosed (A k) := by
    intro k
    exact (hC.preimage (continuous_fst.prodMk hu)).inter
      ((hC.preimage (continuous_fst.prodMk hv)).inter
        ((isClosed_le continuous_const (hu.dist hv)).inter
          ((isClosed_le continuous_const (hu.dist hv.neg)).inter
            (isClosed_le continuous_const hR))))
  have hImage : ∀ k, IsClosed (Prod.fst '' A k) :=
    fun k => isClosedMap_fst_of_compactSpace _ (hA k)
  have hEq :
      {J | ∃ u ∈ nearGroundCriticalSet p hp n J d,
        ∃ v ∈ nearGroundCriticalSet p hp n J d,
          u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} =
        ⋃ k : ℕ, Prod.fst '' A k := by
    ext J
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨u, huC, v, hvC, huv, huvneg, hε⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt
        (lt_min (dist_pos.mpr huv) (dist_pos.mpr huvneg))
      refine ⟨k, (J, (⟨u, huC.1⟩, ⟨v, hvC.1⟩)), ?_, rfl⟩
      exact ⟨huC, hvC, (lt_min_iff.mp hk).1.le,
        (lt_min_iff.mp hk).2.le, hε⟩
    · rintro ⟨k, ⟨J', u, v⟩, hk, rfl⟩
      have hpos : (0 : ℝ) < 1 / (k+1 : ℝ) := by positivity
      exact ⟨u.1, hk.1, v.1, hk.2.1,
        dist_pos.mp (hpos.trans_le hk.2.2.1),
        dist_pos.mp (hpos.trans_le hk.2.2.2.1), hk.2.2.2.2⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun k => (hImage k).measurableSet

/-- The source's Markov step for the literal ordered count. It needs no
measurability assumption on that count and no almost-sure finiteness. -/
private theorem nearGroundPairEvent_measure_le_mean (p : ℕ) (hp : 3 ≤ p)
    (n : ℕ) (d ε : ℝ) :
    disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree
      {J | ∃ u ∈ nearGroundCriticalSet p hp n J d,
        ∃ v ∈ nearGroundCriticalSet p hp n J d,
          u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} ≤
      ∫⁻ J, nearGroundPairCount p hp n J d ε
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree := by
  classical
  rw [← lintegral_indicator_one (nearGroundPairEvent_measurable p hp n d ε)]
  apply lintegral_mono
  intro J
  by_cases hJ : ∃ u ∈ nearGroundCriticalSet p hp n J d,
      ∃ v ∈ nearGroundCriticalSet p hp n J d,
        u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hJ, Pi.one_apply]
    obtain ⟨u, hu, v, hv, huv, huvneg, hε⟩ := hJ
    exact ENNReal.le_tsum
      (f := fun _z : nearGroundPairSet p hp n J d ε => (1 : ℝ≥0∞))
      ⟨(u, v), hu, hv, huv, huvneg, hε⟩
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hJ, zero_le]

/-- The remaining first-moment estimate in the published argument. This
is an explicit proposition, not a theorem or an axiom. Only its cubic
instance is needed by `corollary13_of_cubic_pair_first_moment` below.
It follows in the paper from the global two-point complexity upper bound
and strict negativity away from overlap zero; neither is proved here. -/
def PairFirstMomentBound (p : ℕ) (hp : 3 ≤ p) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    (∫⁻ J, nearGroundPairCount p hp n J d ε
      ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) ≤
        ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ)))

/-- The complete probability/measure reduction of equation (2.11) to its
ordered-pair first moment, including the exact original closed window. -/
theorem corollary13_of_pair_first_moment (p : ℕ) (hp : 3 ≤ p)
    (hPair : PairFirstMomentBound p hp) : Corollary13 p hp := by
  intro ε hε
  obtain ⟨d,c,hd,hc,hMean⟩ := hPair ε hε
  refine ⟨d,c,hd,hc,?_⟩
  filter_upwards [hMean] with n hn
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((nearGroundPairEvent_measure_le_mean p hp n d ε).trans hn)).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)

/-- The full all-degree interface is reduced to the cubic ordered-pair
first moment alone. For every other degree the input is discharged above. -/
theorem corollary13_of_cubic_pair_first_moment
    (hCubic : PairFirstMomentBound 3 (by omega)) (p : ℕ) (hp : 3 ≤ p) :
    Corollary13 p hp := by
  by_cases h3 : p = 3
  · subst p
    exact corollary13_of_pair_first_moment 3 hp hCubic
  · exact corollary13_degree_ge_four p (by omega)

/-- Literal original-field critical-point separation for degree at least
four, with the separation literature hypothesis discharged. -/
theorem pure_original_critical_separation_reduced (p : ℕ) (hp : 4 ≤ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | ∃ u ∈ nearGroundCriticalSet p (by omega) n J d,
          ∃ v ∈ nearGroundCriticalSet p (by omega) n J d,
            u ≠ v ∧ u ≠ -v ∧ ε ≤ overlap u v} ≤ Real.exp (-c*(n+2 : ℕ)) :=
  pure_original_critical_separation p (by omega) (corollary13_degree_ge_four p hp) ε hε

/-- Microscopic disjointness with no separation or literature premise. -/
theorem pure_original_microscopic_disjointness_reduced (p : ℕ) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 1/2 < Q) (hQ1 : Q < 1) (L w : ℝ) :
    Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 (1 : ℝ)) :=
  pure_original_microscopic_disjointness p hp (corollary13_degree_ge_four p hp) hQ hQ1 L w

/-- Both conclusions of the original disjoint-band/count endpoint, with
the Corollary 13 premise removed and no new hypothesis. -/
theorem pure_original_disjoint_bands_and_bounded_count_reduced (p : ℕ) (hp : 4 ≤ p)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {L w : ℝ} (hL : 0 < L) (hw : 0 < w) :
    Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
        {J | (criticalWindow p hp n L J).PairwiseDisjoint (microscopicBand n Q w)})
      atTop (𝓝 (1 : ℝ)) ∧
    ∃ C : ℝ, ∀ n : ℕ,
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree) < ⊤ ∧
      (∫⁻ J, criticalWindowCount p hp n L J
        ∂disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).toReal ≤ C :=
  pure_original_disjoint_bands_and_bounded_count p hp h
    (corollary13_degree_ge_four p hp) hL hw

end SlowEquilibration.SourcePureSeparationCorollary13Proof
