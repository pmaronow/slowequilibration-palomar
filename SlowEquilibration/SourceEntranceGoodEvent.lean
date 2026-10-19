-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceEntranceHarmonic
public import SlowEquilibration.SourceEntranceRegularityLiteral
public import SlowEquilibration.SourceSphereSharpConcentration
public import SlowEquilibration.SourceEntropyResolventAbstract
public import SlowEquilibration.PureTensorJetConcentration
public import Mathlib.Probability.Distributions.Exponential

/-! Common entrance events and the Gaussian trace estimates needed for
Section 8. The existing latitude bank event is proved rotation invariant,
with failure at most `exp(-N)`, and now conditions both truncated and
boundary estimates. The independent-exponential killing construction is
proved to give the existing Feynman--Kac survival weights, even for bounded
measurable killing rates. The general closed-form resolvent realization
remains unproved. The trace estimates retain the scale of every contraction,
including constant traces. A trace is not identified with a spherical
harmonic projection: the Fischer decomposition and its compatibility with
the original ordered tensors remain separate obligations. In particular,
the analytic event used below is not asserted to be the full manuscript
event until that identification and the harmonic-sector clause are proved.
No additional literature interface is introduced here. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceGoodEvent

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open SourceEntranceRegularityLiteral SourceEntranceRegressionBoundary
open SphericalPosteriorGradientIndependence
open WholeFieldRegression
open EntranceLatitudeTangentObservable SourceSphereSharpConcentration
open OrderedTensorTraceGaussianBank PureTensorJetBounds
open scoped BigOperators RealInnerProductSpace NNReal ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Gaussian concentration of the genuine normalized trace bank, including
degree zero. The deviation is of order `sqrt N`, not the coefficient-space
dimension. -/
theorem tracedUnitEnvelope_upper_tail {N : ℕ} (hN : 0 < N) (q j : ℕ)
    {s : ℝ} (hs : 0 ≤ s) :
    (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
      {J | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ tracedUnitEnvelope N q j J} ≤
        Real.exp (-s^2*(N : ℝ)/2) := by
  let F : EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N q) → ℝ :=
    fun g => unitJetEnvelope N q 0 (WithLp.ofLp g)
  have hLip : LipschitzWith (1 : ℝ).toNNReal F := by
    simpa only [pow_zero] using
      (PureTensorJetConcentration.unitEnvelope_lipschitz (p := q) (j := 0) hN)
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N q →
      EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N q))
      (SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N q))
      (SphericalAging.FiniteModel.disorderLaw N q) := ⟨by fun_prop, rfl⟩
  have hmean : (∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean
      (SphericalAging.FiniteModel.TensorIndex N q)) ≤ 4*Real.sqrt (q+1)*Real.sqrt N := by
    have h := expected_tracedUnitEnvelope_le_all hN q 0
    have ht := (actual_rawOrderedTensorTrace_hasLaw hN q 0).integral_comp
      (unitJetEnvelope_integrable (N := N) (p := q) (j := 0) hN).aestronglyMeasurable
    change (∫ J, tracedUnitEnvelope N q 0 J ∂_) = _ at ht
    rw [ht] at h
    have he := hLaw.integral_comp (hLip.continuous.measurable.aestronglyMeasurable)
    simpa only [F, WithLp.ofLp_toLp] using he ▸ h
  have ht := GaussianNormConcentration.centered_lipschitz_upper_tail F
    (by norm_num : (0 : ℝ) ≤ 1) hLip (s := s*Real.sqrt N) (by positivity)
  have hm : MeasurableSet {J : SphericalAging.FiniteModel.Disorder N q |
      (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ unitJetEnvelope N q 0 J} := by
    exact (isClosed_le continuous_const
      (hLip.continuous.comp (by fun_prop))).measurableSet
  have hraw : (SphericalAging.FiniteModel.disorderLaw N q).real
      {J | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ unitJetEnvelope N q 0 J} ≤
        Real.exp (-s^2*(N : ℝ)/2) := by
    have hmF : MeasurableSet {g | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ F g} :=
      (isClosed_le continuous_const hLip.continuous).measurableSet
    have he := hLaw.measureReal_eq hmF
    change (SphericalAging.FiniteModel.disorderLaw N q).real
      {J | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ F (WithLp.toLp 2 J)} = _ at he
    simp only [F] at he
    rw [he]
    have hsub : {g | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ F g} ⊆
        {g | (∫ z, F z ∂SYK.standardGaussianMeasureOnEuclidean
          (SphericalAging.FiniteModel.TensorIndex N q)) + s*Real.sqrt N ≤ F g} := by
      intro g hg
      change (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ F g at hg
      change _ ≤ F g
      nlinarith
    apply (measureReal_mono hsub).trans (ht.trans_eq ?_)
    · congr 1
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
      norm_num
  change (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
    {J | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤
      unitJetEnvelope N q 0 (rawOrderedTensorTrace N q j J)} ≤ _
  rw [(actual_rawOrderedTensorTrace_hasLaw hN q j).measureReal_eq hm]
  exact hraw

/-- Every ordered trace has an exponential upper tail at precisely
`N^(1-j/2)`. The assertion also covers fully traced even tensors. -/
theorem tracedPhysicalEnvelope_upper_tail {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (hp : 1 ≤ q+j+j) {s : ℝ} (hs : 0 ≤ s) :
    (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
      {J | (4*Real.sqrt (q+1)+s)*(N : ℝ)^(1-(j : ℝ)/2) ≤
        tracedPhysicalEnvelope N q j J} ≤ Real.exp (-s^2*(N : ℝ)/2) := by
  let A := SphericalAging.FiniteModel.normalization N (q+j+j)*
    Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q
  have hA : 0 < A := by
    dsimp [A, SphericalAging.FiniteModel.normalization]
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    positivity
  have he : A*Real.sqrt N = (N : ℝ)^(1-(j : ℝ)/2) :=
    trace_physical_normalization_of_degree hN q j hp
  have hset : {J | (4*Real.sqrt (q+1)+s)*(N : ℝ)^(1-(j : ℝ)/2) ≤
      tracedPhysicalEnvelope N q j J} =
      {J | (4*Real.sqrt (q+1)+s)*Real.sqrt N ≤ tracedUnitEnvelope N q j J} := by
    ext J
    change _ ≤ A*tracedUnitEnvelope N q j J ↔ _
    rw [← he]
    rw [show (4*Real.sqrt (q+1)+s)*(A*Real.sqrt N) =
      A*((4*Real.sqrt (q+1)+s)*Real.sqrt N) by ring]
    exact mul_le_mul_iff_right₀ hA
  rw [hset]
  exact tracedUnitEnvelope_upper_tail hN q j hs

/-- The same sharp-scale bound for any ordered pairing of tensor slots. -/
theorem permutedTraceEnvelope_upper_tail {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (hp : 1 ≤ q+j+j) (σ : Equiv.Perm (Fin (q+j+j))) {s : ℝ} (hs : 0 ≤ s) :
    (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
      {J | (4*Real.sqrt (q+1)+s)*(N : ℝ)^(1-(j : ℝ)/2) ≤
        permutedTraceEnvelope N q j σ J} ≤ Real.exp (-s^2*(N : ℝ)/2) := by
  have hcont : Continuous (tracedPhysicalEnvelope N q j) := by
    unfold tracedPhysicalEnvelope tracedUnitEnvelope rawOrderedTensorTrace
    apply Continuous.const_mul
    have hLip := PureTensorJetConcentration.unitEnvelope_lipschitz (N := N) (p := q) (j := 0) hN
    exact hLip.continuous.comp (by
      unfold orderedTensorTrace traceBank tensorFlatten
      fun_prop)
  have hm : MeasurableSet {J | (4*Real.sqrt (q+1)+s)*(N : ℝ)^(1-(j : ℝ)/2) ≤
      tracedPhysicalEnvelope N q j J} :=
    (isClosed_le continuous_const hcont).measurableSet
  change (SphericalAging.FiniteModel.disorderLaw N (q+j+j)).real
    {J | (4*Real.sqrt (q+1)+s)*(N : ℝ)^(1-(j : ℝ)/2) ≤
      tracedPhysicalEnvelope N q j (permutedTensor σ J)} ≤ _
  rw [(permutedTensor_measurePreserving σ).hasLaw.measureReal_eq hm]
  exact tracedPhysicalEnvelope_upper_tail hN q j hp hs

open GaussianCompactMaximum GaussianSharpAbsoluteMaximum
open PairedTensorProjectionFeatures

private theorem positiveSupremum_lipschitz {ι V : Type*}
    [Fintype ι] [DecidableEq ι] [TopologicalSpace V] [CompactSpace V] [Nonempty V]
    (a : V → EuclideanSpace ℝ ι) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ v, ‖a v‖ ≤ K) :
    LipschitzWith K.toNNReal (positiveSupremum a) := by
  apply field_supremum_lipschitz (fun v : Unit ⊕ V => innerSL ℝ (withZero a v))
  intro v
  simp only [innerSL_apply_norm]
  cases v with
  | inl v => simpa only [withZero, Sum.elim_inl, norm_zero] using hK
  | inr v => simpa only [withZero, Sum.elim_inr] using ha v

private theorem absoluteSupremum_le_max_positive {ι V : Type*}
    [Fintype ι] [DecidableEq ι] [TopologicalSpace V] [CompactSpace V] [Nonempty V]
    (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) (g : EuclideanSpace ℝ ι) :
    absoluteSupremum a g ≤ max (positiveSupremum a g)
      (positiveSupremum (fun v => -a v) g) := by
  apply ciSup_le
  rintro ⟨b,v⟩
  cases b
  · apply le_trans _ (le_max_right _ _)
    simpa only [withZero, Sum.elim_inr, signedFeature, sign,
      Bool.false_eq_true, ite_false, neg_one_smul] using
      le_positiveSupremum (fun v => -a v) ha.neg g (.inr v)
  · apply le_trans _ (le_max_left _ _)
    simpa only [withZero, Sum.elim_inr, signedFeature, sign, ite_true, one_smul] using
      le_positiveSupremum a ha g (.inr v)

private theorem paired_positive_tail {N : ℕ} (hN : 2 ≤ N)
    (q j : ℕ) (hj : 0 < j) (s : ℝ) (hs : |s| = 1) :
    SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N (q+j+j))
      {g | 2*Real.sqrt ((q : ℝ)+4*j)+1 ≤
        positiveSupremum (fun u => s • pairedGaussianFeature N q j u) g} ≤
      ENNReal.ofReal (2*Real.exp (-9*(N : ℝ)/2)) := by
  let : NeZero N := ⟨by omega⟩
  let a := fun u : UnitSphere N => s • pairedGaussianFeature N q j u
  let A : ℝ := Real.sqrt ((q : ℝ)+4*j)
  let L : ℝ := pairedPhysicalScale N q j*A
  have hA : 2 ≤ A := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith [show (0 : ℝ) ≤ q by positivity]
  have hscale := pairedPhysicalScale_nonneg N q j
  have ha : Continuous a := (pairedGaussianFeature_continuous N q j).const_smul s
  have han (u : UnitSphere N) : ‖a u‖ = pairedPhysicalScale N q j := by
    simp only [a, norm_smul, Real.norm_eq_abs, hs, one_mul, pairedGaussianFeature,
      abs_of_nonneg hscale, unitPairedFeature_norm hN, mul_one]
  have hinc (u v : UnitSphere N) : ‖a u-a v‖ ≤ L*‖(u : Vector N)-(v : Vector N)‖ := by
    dsimp only [a]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, hs, one_mul]
    simp only [pairedGaussianFeature, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left (unitPairedFeature_increment_le hN q j u v)
      hscale).trans_eq (by ring)
  have hm := expected_positiveSupremum_le a (fun u : UnitSphere N => (u : Vector N))
    ha continuous_subtype_val (show 0 ≤ L by dsimp [L,A]; positivity)
    (fun u => by rw [han]; exact le_mul_of_one_le_right hscale (by linarith))
    unit_norm hinc
  simp only [Fintype.card_fin] at hm
  have hscale1 : pairedPhysicalScale N q j*Real.sqrt N ≤ 1 :=
    (pairedPhysicalScale_sqrt_dimension_le hN q j (by omega)).trans
      (Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
        (by
          have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
          linarith))
  have hmean : (∫ g, positiveSupremum a g ∂SYK.standardGaussianMeasureOnEuclidean
      (SphericalAging.FiniteModel.TensorIndex N (q+j+j))) ≤ A := by
    apply hm.trans
    calc
      L*Real.sqrt N = A*(pairedPhysicalScale N q j*Real.sqrt N) := by dsimp [L]; ring
      _ ≤ A*1 := mul_le_mul_of_nonneg_left hscale1 (by dsimp [A]; positivity)
      _ = A := mul_one A
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hLip : LipschitzWith ((Real.sqrt N)⁻¹).toNNReal (positiveSupremum a) :=
    positiveSupremum_lipschitz a (by positivity)
      (fun u => (han u).le.trans (pairedPhysicalScale_le_inv_sqrt hN q j hj))
  have ht := SphericalModel.euclidean_lipschitz_gaussian_closed_tail
    (positiveSupremum a) (Real.sqrt N)⁻¹ 3 (by positivity) (by norm_num) hLip
  have hsub : {g | 2*Real.sqrt ((q : ℝ)+4*j)+1 ≤ positiveSupremum a g} ⊆
      {g | 3 ≤ |positiveSupremum a g-(∫ z,positiveSupremum a z
        ∂SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N (q+j+j)))|} := by
    intro g hg
    change 2*A+1 ≤ positiveSupremum a g at hg
    exact (by linarith : 3 ≤ positiveSupremum a g-(∫ z,positiveSupremum a z ∂_)).trans
      (le_abs_self _)
  apply (measure_mono hsub).trans
  convert ht using 2
  congr 2
  rw [inv_pow, Real.sq_sqrt hNr.le]
  field_simp
  norm_num

/-- The existing bank threshold has considerable spare Gaussian decay.
Controlling the two positive suprema separately improves its exponent
without enlarging the event or changing any downstream constants. -/
theorem originalPairedEnvelope_sharp_tail {N : ℕ} (hN : 2 ≤ N) (q j : ℕ) (hj : 0 < j) :
    SphericalAging.FiniteModel.disorderLaw N (q+j+j)
      {J | 2*Real.sqrt ((q : ℝ)+4*j)+1 ≤ originalPairedEnvelope N q j J} ≤
        ENNReal.ofReal (4*Real.exp (-9*(N : ℝ)/2)) := by
  let : NeZero N := ⟨by omega⟩
  let a := pairedGaussianFeature N q j
  let B := 2*Real.sqrt ((q : ℝ)+4*j)+1
  have hsub : {g | B ≤ pairedGaussianEnvelope N q j g} ⊆
      {g | B ≤ positiveSupremum a g} ∪ {g | B ≤ positiveSupremum (fun u => -a u) g} := by
    intro g hg
    exact le_max_iff.mp (hg.trans
      (absoluteSupremum_le_max_positive a (pairedGaussianFeature_continuous N q j) g))
  have hp := paired_positive_tail hN q j hj 1 (by norm_num)
  have hn := paired_positive_tail hN q j hj (-1) (by norm_num)
  simp only [one_smul] at hp
  simp only [neg_one_smul] at hn
  have ht := (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hp hn))
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N (q+j+j) →
      EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N (q+j+j)))
      (SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N (q+j+j)))
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := ⟨by fun_prop, rfl⟩
  have hm : MeasurableSet {g | B ≤ pairedGaussianEnvelope N q j g} :=
    (isClosed_le continuous_const (pairedGaussianEnvelope_lipschitz hN q j hj).continuous).measurableSet
  have he := hLaw.measure_eq hm
  change _ = SYK.standardGaussianMeasureOnEuclidean _ {g | B ≤ pairedGaussianEnvelope N q j g} at he
  change SphericalAging.FiniteModel.disorderLaw N (q+j+j)
    {J | B ≤ pairedGaussianEnvelope N q j (WithLp.toLp 2 J)} ≤ _
  rw [he]
  exact ht.trans_eq (by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring)

open SphericalLatitudeTensorMoments FiniteWickPairings

private theorem latitudePairingEnvelope_sharp_tail {n p : ℕ} (hn : 1 ≤ n)
    (S : Finset (Fin p)) (L : List (Fin p × Fin p)) (hL : ValidPairing S L)
    (hj : 0 < L.length) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p
      {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.length : ℝ))+1 ≤
        latitudePairingEnvelope n p S L hL J} ≤
      ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
  have ht := originalPairedEnvelope_sharp_tail (by omega : 2 ≤ n+1)
    (Finset.univ\S).card L.length hj
  have hm : MeasurableSet {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.length : ℝ))+1 ≤
      originalPairedEnvelope (n+1) (Finset.univ\S).card L.length J} := by
    apply (isClosed_le continuous_const _).measurableSet
    exact (pairedGaussianEnvelope_lipschitz (by omega) (Finset.univ\S).card L.length hj).continuous.comp
      (by fun_prop)
  have he := (pairingReindexedTensor_measurePreserving (N := n+1) S L hL).hasLaw.measure_eq hm
  change SphericalAging.FiniteModel.disorderLaw (n+1) p
    {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.length : ℝ))+1 ≤
      originalPairedEnvelope (n+1) (Finset.univ\S).card L.length
        (pairingReindexedTensor S L hL J)} ≤ _
  rw [he]
  exact ht

private theorem measure_exists_list_le {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (T : List ι) (A : ι → Set Ω) (c : ℝ≥0∞)
    (hA : ∀ a ∈ T, ν (A a) ≤ c) :
    ν {ω | ∃ a ∈ T, ω ∈ A a} ≤ (T.length : ℝ≥0∞)*c := by
  induction T with
  | nil => simp
  | cons a T ih =>
    have he : {ω | ∃ b ∈ a::T, ω ∈ A b} = A a ∪ {ω | ∃ b ∈ T, ω ∈ A b} := by
      ext ω
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      aesop
    rw [he]
    apply (measure_union_le _ _).trans
    have h := add_le_add (hA a (by simp)) (ih (fun b hb => hA b (by simp [hb])))
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h

private theorem latitudeCorrectionBadBanks_sharp_tail {n p : ℕ} (hn : 1 ≤ n) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p (latitudeCorrectionBadBanks n p) ≤
      (latitudeCorrectionBankCount p : ℝ≥0∞)*
        ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
  unfold latitudeCorrectionBadBanks
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ S ∈ ((Finset.univ : Finset (Fin p)).powerset.erase ∅),
        ((labeledWickPairings S).length : ℝ≥0∞)*
          ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
      apply Finset.sum_le_sum
      intro S hS
      have he := measure_exists_list_le (SphericalAging.FiniteModel.disorderLaw (n+1) p)
        (labeledWickPairings S).attach
        (fun L => {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ))+1 ≤
          latitudePairingEnvelope n p S L.val (labeledWickPairings_valid S L.val L.property) J})
        (ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2))) (by
          intro L _
          exact latitudePairingEnvelope_sharp_tail hn S L.val
            (labeledWickPairings_valid S L.val L.property)
            (nonempty_Wick_pairing_length_pos (Finset.mem_erase.mp hS).1 L.property))
      simpa only [List.length_attach, Set.mem_ofPred_eq] using he
    _ = _ := by rw [← Finset.sum_mul]; simp only [latitudeCorrectionBankCount, Nat.cast_sum]

private theorem regularDisorder_sharp_tail {N P : ℕ} (hN : 2 ≤ N) (hP : 2 ≤ P) :
    (disorderLaw N P).real (regularDisorder (N := N) (P := P))ᶜ ≤ Real.exp (-2*(N : ℝ)) := by
  classical
  let : Nonempty (Degree P) := ⟨⟨⟨2, by omega⟩, by change 2 ≤ (2 : ℕ); omega⟩⟩
  let m : ℝ := Fintype.card (Degree P)
  have hm : 1 ≤ m := by
    have hcard : 0 < Fintype.card (Degree P) := Fintype.card_pos
    dsimp [m]
    exact_mod_cast hcard
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbad : (regularDisorder (N := N) (P := P))ᶜ =
      ⋃ p : Degree P, {J : Disorder N P |
        blockThreshold p < GaussianLandscape.landscapeNorm N p.val.val (J p)} := by
    ext J
    simp [regularDisorder, not_forall, not_le]
  have hblock (p : Degree P) :
      (disorderLaw N P).real {J : Disorder N P |
        blockThreshold p < GaussianLandscape.landscapeNorm N p.val.val (J p)} ≤
      2*Real.exp (-(N : ℝ)*(m+1)^2) := by
    rw [(degree_block_hasLaw p).measureReal_eq
      (measurableSet_lt measurable_const (GaussianLandscape.landscapeNorm_continuous N p.val.val).measurable)]
    have hthreshold : GaussianLandscape.landscapeThreshold p.val.val ≤ blockThreshold p := by
      unfold blockThreshold
      have hm0 : (0 : ℝ) ≤ Fintype.card (Degree P) := Nat.cast_nonneg _
      linarith
    have ht := GaussianLandscape.landscape_tail_dimension
      (N := N) (p := p.val.val) (by omega) (by omega) hthreshold
    have hb := (GaussianLandscape.landscapeThreshold_pos p.val.val).le
    have hs : 16*(m+1)^2 ≤ blockThreshold p^2 := by
      change 16*(m+1)^2 ≤ (GaussianLandscape.landscapeThreshold p.val.val+4*(m+1))^2
      nlinarith [mul_nonneg hb (show 0 ≤ m+1 by linarith)]
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hs)]))
      (by norm_num))
  rw [hbad]
  calc
    _ ≤ ∑ p : Degree P, (disorderLaw N P).real {J : Disorder N P |
        blockThreshold p < GaussianLandscape.landscapeNorm N p.val.val (J p)} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p : Degree P, 2*Real.exp (-(N : ℝ)*(m+1)^2) :=
      Finset.sum_le_sum (fun p _ => hblock p)
    _ = (2*m)*Real.exp (-(N : ℝ)*(m+1)^2) := by simp [m]; ring
    _ ≤ Real.exp (2*m)*Real.exp (-(N : ℝ)*(m+1)^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (2*m)]
    _ = Real.exp (2*m-(N : ℝ)*(m+1)^2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-2*(N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg N) (show 0 ≤ m^2-1 by nlinarith),
        mul_nonneg (sub_nonneg.mpr hNr) (show 0 ≤ m by linarith)]

/-- The *same* original latitude event used in the sharp concentration and
multiplier modules has failure at most `exp(-N)` for all large dimensions.
All its existing deterministic constants remain valid. The harmonic-sector
clause remains separate; rotational invariance is proved below. -/
theorem originalLatitudeMeanGood_sharp_probability (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop, (disorderLaw (n+1) μ.maxDegree).real
      (originalLatitudeMeanGood n μ)ᶜ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨p,hp⟩ := μ.support_nonempty
  have hP : 2 ≤ μ.maxDegree := (μ.degree_ge_two hp).trans (μ.degree_bounds hp).2
  let B : ℝ := originalLatitudeBankCount μ
  obtain ⟨M,hM⟩ := exists_nat_ge (Real.log (1+4*B))
  filter_upwards [eventually_ge_atTop (max M 1)] with n hn
  have hn1 : 1 ≤ n := by omega
  have he : (originalLatitudeMeanGood n μ)ᶜ =
      (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ∪
      ⋃ p : Degree μ.maxDegree, {J : Disorder (n+1) μ.maxDegree |
        J p ∈ latitudeCorrectionBadBanks n p.val.val} := by
    ext J
    simp only [originalLatitudeMeanGood, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_union, Set.mem_iUnion, not_and_or, not_forall, not_not]
  have hb : disorderLaw (n+1) μ.maxDegree
      (⋃ p : Degree μ.maxDegree, {J : Disorder (n+1) μ.maxDegree |
        J p ∈ latitudeCorrectionBadBanks n p.val.val}) ≤
      (originalLatitudeBankCount μ : ℝ≥0∞)*ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
    apply (measure_iUnion_fintype_le _ _).trans
    calc
      _ ≤ ∑ p : Degree μ.maxDegree, (latitudeCorrectionBankCount p.val.val : ℝ≥0∞)*
          ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
        apply Finset.sum_le_sum
        intro p _
        have heq : disorderLaw (n+1) μ.maxDegree {J | J p ∈ latitudeCorrectionBadBanks n p.val.val} =
            SphericalAging.FiniteModel.disorderLaw (n+1) p.val.val (latitudeCorrectionBadBanks n p.val.val) := by
          convert (degree_block_hasLaw p).measure_eq (latitudeCorrectionBadBanks_measurable hn1) using 1
          all_goals congr 1
        rw [heq]
        exact latitudeCorrectionBadBanks_sharp_tail hn1
      _ = _ := by rw [← Finset.sum_mul]; simp only [originalLatitudeBankCount, Nat.cast_sum]
  have hbr : (disorderLaw (n+1) μ.maxDegree).real
      (⋃ p : Degree μ.maxDegree, {J : Disorder (n+1) μ.maxDegree |
        J p ∈ latitudeCorrectionBadBanks n p.val.val}) ≤
      B*(4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
    have h := ENNReal.toReal_mono (by finiteness) hb
    simpa only [Measure.real, B, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2))] using h
  rw [he]
  apply (measureReal_union_le _ _).trans
  apply (add_le_add (regularDisorder_sharp_tail (by omega) hP) hbr).trans
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hl : Real.log (1+4*B) ≤ ((n+1 : ℕ) : ℝ) := hM.trans (by exact_mod_cast (show M ≤ n+1 by omega))
  have hNr : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (1+4*B)*Real.exp (-2*((n+1 : ℕ) : ℝ)) := by
      have h := Real.exp_le_exp.mpr (show -9*((n+1 : ℕ) : ℝ)/2 ≤ -2*((n+1 : ℕ) : ℝ) by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h hB]
    _ = Real.exp (Real.log (1+4*B)-2*((n+1 : ℕ) : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.exp_log (by positivity : 0 < 1+4*B)]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := Real.exp_le_exp.mpr (by linarith)

private theorem mass_half_of_failure {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {E : Set A} (hE : MeasurableSet E)
    {N : ℕ} (hN : 2 ≤ N) (hfail : P.real Eᶜ ≤ Real.exp (-(N : ℝ))) :
    (1/2 : ℝ) ≤ P.real E := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp (-(N : ℝ)) ≤ 1/2 := by
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hs := measureReal_add_measureReal_compl (μ := P) hE
  rw [probReal_univ] at hs
  linarith

/-- A single actual original-disorder event now supports all nonharmonic
regularity clauses and has the printed failure rate and positive mass.
The latitude and multiplier theorems already use exactly this event. -/
theorem common_analytic_event (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, ∃ n0 : ℕ, 0 < C ∧ ∀ n ≥ n0,
      MeasurableSet (originalLatitudeMeanGood n μ) ∧
      (disorderLaw (n+1) μ.maxDegree).real (originalLatitudeMeanGood n μ)ᶜ ≤
        Real.exp (-((n+1 : ℕ) : ℝ)) ∧
      (1/2 : ℝ) ≤ (disorderLaw (n+1) μ.maxDegree).real (originalLatitudeMeanGood n μ) ∧
      ∀ J ∈ originalLatitudeMeanGood n μ, NonharmonicRegularClauses μ Q C J := by
  obtain ⟨C,hC,hreg⟩ := nonharmonic_regular_event μ Q
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (originalLatitudeMeanGood_sharp_probability μ)
  refine ⟨C,max n0 1,hC,?_⟩
  intro n hn
  have hm := originalLatitudeMeanGood_measurable (by omega : 1 ≤ n) μ
  have hf := hn0 n (by omega)
  exact ⟨hm,hf,mass_half_of_failure _ hm (by omega) hf,
    fun J hJ => (hreg (n+1) (by omega)).2.2.2 J hJ.1⟩

/-- The law obtained by conditioning only the actual Gaussian coefficient
vector on the common analytic event. -/
def analyticDisorderLaw (n : ℕ) (μ : FiniteMixture) : Measure (Disorder (n+1) μ.maxDegree) :=
  ProbabilityTheory.cond (disorderLaw (n+1) μ.maxDegree) (originalLatitudeMeanGood n μ)

private theorem analytic_mass_eventually (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ (disorderLaw (n+1) μ.maxDegree).real (originalLatitudeMeanGood n μ) := by
  filter_upwards [originalLatitudeMeanGood_sharp_probability μ, eventually_ge_atTop 1] with n hn hn1
  exact mass_half_of_failure _ (originalLatitudeMeanGood_measurable hn1 μ) (by omega) hn

private theorem integral_cond_sub_event_le_twice {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {E F : Set A}
    (hEF : E ⊆ F) (hhalf : (1/2 : ℝ) ≤ P.real E) (hFpos : 0 < P.real F)
    (f : A → ℝ) (hi : Integrable f P) (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂ProbabilityTheory.cond P E) ≤
      2*∫ x, f x ∂ProbabilityTheory.cond P F := by
  have hpos : 0 < P.real E := by linarith
  have hinv : (P.real E)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
  have hinvF : 1 ≤ (P.real F)⁻¹ := (one_le_inv₀ hFpos).mpr measureReal_le_one
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_inv]
  have hsub := setIntegral_mono_set hi.integrableOn (ae_of_all _ hf)
    (ae_of_all _ fun x hx => hEF hx)
  have hnon : 0 ≤ ∫ x in F, f x ∂P := integral_nonneg hf
  calc
    _ ≤ 2*∫ x in E, f x ∂P := mul_le_mul_of_nonneg_right hinv (integral_nonneg hf)
    _ ≤ 2*∫ x in F, f x ∂P := mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnon hinvF) (by norm_num)

private theorem unit_integrable {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {f : A → ℝ}
    (hm : Measurable f) (hf : ∀ x, f x ∈ Icc 0 1) : Integrable f P := by
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by simpa [abs_of_nonneg (hf x).1] using (hf x).2

private theorem two_exp_le {c x : ℝ} (hc : 0 < c) (hx : 2*Real.log 2/c ≤ x) :
    2*Real.exp (-c*x) ≤ Real.exp (-(c/2)*x) := by
  conv_lhs => arg 1; rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := (div_le_iff₀ hc).mp hx
  nlinarith

/-- The mixed truncated cap estimate now uses the same coefficient event
as the literal latitude and multiplier estimates, for every smaller
positive horizon exponent. No conditioning-mass assumption remains. -/
theorem analytic_conditioned_mixed_truncated
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 c C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < c ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
            (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e k J ∂analyticDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hall⟩ := conditioned_mixed_truncated_cap_avoidance μ hd hQ hQ1 hnp hB hβ
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (analytic_mass_eventually μ)
  refine ⟨aStar,hStar,?_⟩
  intro a ha haStar
  obtain ⟨γ0,c,C,n0,hγ0,hc,hC,hbound⟩ := hall ha haStar
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨γ0,c/2,2*C,max n0 (max n1 (max M 1)),hγ0,by positivity,by positivity,?_⟩
  intro n hn γ hγ hγ0' e k he hk
  let f : Disorder (n+1) μ.maxDegree → ℝ := sourceAxisAveragedCapHitProbability μ Q hQ hnp (2*a)
    sourceScalarCutoff sourceScalarCutoff_contDiff_two β (exponentialGridHorizon γ (n+1)) e k
  have hf : ∀ J, f J ∈ Icc 0 1 := fun J => sourceAxisAveragedCapHitProbability_mem_unit ..
  have hi := unit_integrable (disorderLaw (n+1) μ.maxDegree)
    (sourceAxisAveragedCapHitProbability_measurable ..) hf
  have hpos : 0 < (disorderLaw (n+1) μ.maxDegree).real regularDisorder :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (regularDisorder_mass_half (by omega))
  have hcond := integral_cond_sub_event_le_twice (disorderLaw (n+1) μ.maxDegree)
    (fun _ hJ => hJ.1) (hn1 n (by omega)) hpos f hi (fun J => (hf J).1)
  have hr := hbound n (by omega) hγ hγ0' e k he hk
  have ht := two_exp_le hc (x := ((n+1 : ℕ) : ℝ))
    (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans (by nlinarith))

/-- Proper-pure truncated cap avoidance under that identical analytic-event
conditioning, with every amplitude and every smaller positive exponent. -/
theorem analytic_conditioned_pure_truncated
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 κ C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < κ ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e : ℝ, |e| ≤ B →
            (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e J ∂analyticDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-κ*((n+1 : ℕ) : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
  obtain ⟨aStar,hStar,hall⟩ := conditioned_pure_truncated_cap_avoidance d hd c hc hQ hB hβ
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (analytic_mass_eventually μ)
  refine ⟨aStar,hStar,?_⟩
  intro a ha haStar
  obtain ⟨γ0,κ,C,n0,hγ0,hκ,hC,hbound⟩ := hall ha haStar
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/κ)
  refine ⟨γ0,κ/2,2*C,max n0 (max n1 (max M 1)),hγ0,by positivity,by positivity,?_⟩
  intro n hn γ hγ hγ0' e he
  let f : Disorder (n+1) μ.maxDegree → ℝ := pureAxisAveragedCapHitProbability d (by omega) c hc Q (2*a)
    sourceScalarCutoff sourceScalarCutoff_contDiff_two β (exponentialGridHorizon γ (n+1)) e
  have hf : ∀ J, f J ∈ Icc 0 1 := fun J => pureAxisAveragedCapHitProbability_mem_unit ..
  have hi := unit_integrable (disorderLaw (n+1) μ.maxDegree)
    (pureAxisAveragedCapHitProbability_measurable ..) hf
  have hpos : 0 < (disorderLaw (n+1) μ.maxDegree).real regularDisorder :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (regularDisorder_mass_half (by omega))
  have hcond := integral_cond_sub_event_le_twice (disorderLaw (n+1) μ.maxDegree)
    (fun _ hJ => hJ.1) (hn1 n (by omega)) hpos f hi (fun J => (hf J).1)
  have hr := hbound n (by omega) hγ hγ0' e he
  have ht := two_exp_le hκ (x := ((n+1 : ℕ) : ℝ))
    (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans (by nlinarith))

private theorem event_cond_le_twice {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {E : Set A} (hE : MeasurableSet E)
    (hhalf : (1/2 : ℝ) ≤ P.real E) (B : Set A) :
    (ProbabilityTheory.cond P E).real B ≤ 2*P.real B := by
  rw [Measure.real, ProbabilityTheory.cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hpos : 0 < P.real E := by linarith
  have hinv : (P.real E)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_right hinv ENNReal.toReal_nonneg).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_right (measure_ne_top _ _)) (by norm_num))

/-- The same analytic coefficient event lifted to the literal joint seed
space: uniform axis, original Gaussian coefficients, initial point and noise. -/
def analyticBoundaryEvent (n : ℕ) (μ : FiniteMixture) :
    Set (Vector (n+1) × BoundarySeed n μ) :=
  {q | unpackDisorder q.2.1 ∈ originalLatitudeMeanGood n μ}

/-- Only the original disorder is conditioned. -/
def analyticBoundarySeedLaw (n : ℕ) (μ : FiniteMixture) :
    Measure (Vector (n+1) × BoundarySeed n μ) :=
  ProbabilityTheory.cond (boundarySeedLaw n μ) (analyticBoundaryEvent n μ)

private theorem cond_product_left {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (R : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (E : Set A) :
    ProbabilityTheory.cond (P.prod R) (E ×ˢ univ) = (ProbabilityTheory.cond P E).prod R := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left,
    Measure.restrict_prod_eq_prod_univ]

private theorem cond_product_right {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (R : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (E : Set Z) :
    ProbabilityTheory.cond (P.prod R) (univ ×ˢ E) = P.prod (ProbabilityTheory.cond R E) := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, one_mul, Measure.prod_smul_right]
  congr 1
  simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ := P) (ν := R) univ E).symm

/-- Exact independence of the uniform axis, initial point and Brownian noise
after conditioning the Gaussian disorder on the common analytic event. -/
theorem analyticBoundarySeedLaw_eq_product (n : ℕ) (μ : FiniteMixture) :
    analyticBoundarySeedLaw n μ =
      (sphereLaw (n+1)).prod
        ((ProbabilityTheory.cond (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
          {z | unpackDisorder z ∈ originalLatitudeMeanGood n μ}).prod
            ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))) := by
  have he : analyticBoundaryEvent n μ = univ ×ˢ
      ({z : EuclideanDisorder (n+1) μ.maxDegree |
        unpackDisorder z ∈ originalLatitudeMeanGood n μ} ×ˢ univ) := by
    ext q
    simp only [analyticBoundaryEvent, mem_ofPred_eq, mem_prod, mem_univ, true_and, and_true]
  unfold analyticBoundarySeedLaw boundarySeedLaw
  rw [he, cond_product_right]
  unfold posteriorTrajectoryLaw
  rw [cond_product_left]

private theorem boundary_original_hasLaw (n : ℕ) (μ : FiniteMixture) :
    HasLaw (fun q : Vector (n+1) × BoundarySeed n μ => unpackDisorder q.2.1)
      (disorderLaw (n+1) μ.maxDegree) (boundarySeedLaw n μ) := by
  have hfst : HasLaw (Prod.fst : BoundarySeed n μ → EuclideanDisorder (n+1) μ.maxDegree)
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) (posteriorTrajectoryLaw n μ) := by
    refine ⟨measurable_fst.aemeasurable,?_⟩
    unfold posteriorTrajectoryLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : HasLaw (Prod.snd : Vector (n+1) × BoundarySeed n μ → BoundarySeed n μ)
      (posteriorTrajectoryLaw n μ) (boundarySeedLaw n μ) := by
    refine ⟨measurable_snd.aemeasurable,?_⟩
    unfold boundarySeedLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hu : HasLaw (unpackDisorder (N := n+1) (P := μ.maxDegree))
      (disorderLaw (n+1) μ.maxDegree) (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) := by
    simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] using
      unpackDisorder_hasLaw (n+1) μ.maxDegree
  exact (hu.fun_comp hfst).fun_comp hsnd

private theorem boundary_analytic_mass_eventually (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop,
      MeasurableSet (analyticBoundaryEvent n μ) ∧
      (1/2 : ℝ) ≤ (boundarySeedLaw n μ).real (analyticBoundaryEvent n μ) := by
  filter_upwards [analytic_mass_eventually μ, eventually_ge_atTop 1] with n hn hn1
  have hm := originalLatitudeMeanGood_measurable hn1 μ
  have he := (boundary_original_hasLaw n μ).measureReal_eq hm
  refine ⟨hm.preimage ((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_snd.fst),?_⟩
  have he' : (boundarySeedLaw n μ).real (analyticBoundaryEvent n μ) =
      (disorderLaw (n+1) μ.maxDegree).real (originalLatitudeMeanGood n μ) := by
    convert he using 1 <;> congr 1
  rw [he']
  exact hn

local instance boundary_probability (n : ℕ) (μ : FiniteMixture) :
    IsProbabilityMeasure (boundarySeedLaw n μ) := by unfold boundarySeedLaw; infer_instance

/-- Mixed original-gradient boundary control under the very same disorder
conditioning used for latitude concentration, multipliers and truncation. -/
theorem analytic_conditioned_mixed_boundary
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {Q B β b : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (analyticBoundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ :=
    mixed_uniform_axis_gradient_cutoff_not_reached μ hnp hQ hQ1 hB hβ hb
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (boundary_analytic_mass_eventually μ)
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨T,hT,γ,c,hγ,hc,max n0 (max n1 M),?_⟩
  intro n hn e k he hk
  have hr := hn0 n (by omega) e k he hk
  obtain ⟨hm,hhalf⟩ := hn1 n (by omega)
  refine ⟨hr,?_⟩
  have hcond := event_cond_le_twice (boundarySeedLaw n μ) hm hhalf
    (mixedGradientExit n μ Q β e k b (exponentialGridHorizon γ (n+1)+2*T)
      (exponentialGridHorizon γ (n+1)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans
    (two_exp_le hc (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))))

/-- Proper-pure/value boundary control on the identical analytic event. -/
theorem analytic_conditioned_value_boundary
    (μ : FiniteMixture) {Q B β b : ℝ} (hQ : 0 < Q)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e : ℝ, |e| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (analyticBoundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ := value_uniform_axis_gradient_cutoff_not_reached μ hQ hB hβ hb
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (boundary_analytic_mass_eventually μ)
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨T,hT,γ,c,hγ,hc,max n0 (max n1 M),?_⟩
  intro n hn e he
  have hr := hn0 n (by omega) e he
  obtain ⟨hm,hhalf⟩ := hn1 n (by omega)
  refine ⟨hr,?_⟩
  have hcond := event_cond_le_twice (boundarySeedLaw n μ) hm hhalf
    (valueGradientExit n μ Q β e b (exponentialGridHorizon γ (n+1)+2*T)
      (exponentialGridHorizon γ (n+1)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans
    (two_exp_le hc (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))))

/-- The literal infimum construction of killing from a cumulative hazard
and a sampled exponential threshold. An empty hitting set gives infinity. -/
def inverseHazard (A : ℝ≥0 → ℝ) (e : ℝ) : ℝ≥0∞ := by
  classical
  exact
  if ({t : ℝ≥0 | e ≤ A t} : Set ℝ≥0).Nonempty then
    ((sInf {t : ℝ≥0 | e ≤ A t} : ℝ≥0) : ℝ≥0∞) else ⊤

/-- The definition is exactly the infimum of the finite hitting times in
the extended nonnegative reals, with infimum of the empty set equal to infinity. -/
theorem inverseHazard_eq_sInf (A : ℝ≥0 → ℝ) (e : ℝ) :
    inverseHazard A e = sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | e ≤ A t}) := by
  classical
  by_cases hn : ({t : ℝ≥0 | e ≤ A t} : Set ℝ≥0).Nonempty
  · simp only [inverseHazard, hn, ↓reduceIte]
    rw [ENNReal.coe_sInf hn, sInf_image]
  · have he : {t : ℝ≥0 | e ≤ A t} = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [inverseHazard, he, Set.image_empty, sInf_empty, Set.not_nonempty_empty, ↓reduceIte]

/-- Exact finite-time characterization of the actual killing construction;
no assumption that the accumulated hazard diverges is needed. -/
theorem inverseHazard_le_iff (A : ℝ≥0 → ℝ) (hAc : Continuous A)
    (hAm : Monotone A) (e : ℝ) (t : ℝ≥0) :
    inverseHazard A e ≤ (t : ℝ≥0∞) ↔ e ≤ A t := by
  classical
  have hb : BddBelow {s : ℝ≥0 | e ≤ A s} := ⟨0, fun s _ => by positivity⟩
  by_cases hn : ({s : ℝ≥0 | e ≤ A s} : Set ℝ≥0).Nonempty
  · have hc : IsClosed {s : ℝ≥0 | e ≤ A s} := isClosed_le continuous_const hAc
    have hi : e ≤ A (sInf {s : ℝ≥0 | e ≤ A s}) := hc.csInf_mem hn hb
    simp only [inverseHazard, hn, ↓reduceIte, ENNReal.coe_le_coe]
    exact ⟨fun ht => hi.trans (hAm ht), fun ht => csInf_le hb ht⟩
  · have ht : ¬ e ≤ A t := fun h => hn ⟨t, h⟩
    simp [inverseHazard, hn, ht]

/-- Infinite killing time occurs exactly when the exponential threshold
is never reached, including finite total hazard. -/
theorem inverseHazard_eq_top_iff (A : ℝ≥0 → ℝ) (e : ℝ) :
    inverseHazard A e = ⊤ ↔ ∀ t, A t < e := by
  classical
  by_cases hn : ({s : ℝ≥0 | e ≤ A s} : Set ℝ≥0).Nonempty
  · simp only [inverseHazard, hn, ↓reduceIte, ENNReal.coe_ne_top, false_iff]
    intro hall
    obtain ⟨t, ht⟩ := hn
    exact (not_lt_of_ge ht) (hall t)
  · simp only [inverseHazard, hn, ↓reduceIte, true_iff]
    intro t
    exact lt_of_not_ge (fun ht => hn ⟨t, ht⟩)

/-- The unit exponential threshold gives the exact conditional killing
distribution, including a possible atom at infinity. -/
theorem inverseHazard_unitExponential_cdf (A : ℝ≥0 → ℝ)
    (hAc : Continuous A) (hAm : Monotone A) (t : ℝ≥0) (ht : 0 ≤ A t) :
    (ProbabilityTheory.expMeasure 1).real {e | inverseHazard A e ≤ (t : ℝ≥0∞)} =
      1-Real.exp (-A t) := by
  have hs : {e | inverseHazard A e ≤ (t : ℝ≥0∞)} = Set.Iic (A t) := by
    ext e
    exact inverseHazard_le_iff A hAc hAm e t
  let : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  rw [hs, ← ProbabilityTheory.cdf_eq_real,
    ProbabilityTheory.cdf_expMeasure_eq (by norm_num)]
  simp only [ht, ↓reduceIte, one_mul]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Independent exponential extension of any prescribed cumulative-hazard
process, with its literal infimum hitting time. -/
def exponentialKillingTime (A : ℝ≥0 → Ω → ℝ) (q : Ω × ℝ) : ℝ≥0∞ :=
  inverseHazard (fun t => A t q.1) q.2

private theorem exponentialKillingTime_measurable
    (A : ℝ≥0 → Ω → ℝ) (hAm : ∀ t, Measurable (A t))
    (hAc : ∀ ω, Continuous (fun t => A t ω))
    (hAmono : ∀ ω, Monotone (fun t => A t ω)) :
    Measurable (exponentialKillingTime A) := by
  apply measurable_of_Iic
  intro r
  by_cases hr : r = ⊤
  · subst r; simp
  · lift r to ℝ≥0 using hr with t
    have hs : (exponentialKillingTime A) ⁻¹' Iic (t : ℝ≥0∞) =
        {q : Ω × ℝ | q.2 ≤ A t q.1} := by
      ext q
      exact inverseHazard_le_iff _ (hAc q.1) (hAmono q.1) q.2 t
    rw [hs]
    exact measurableSet_le measurable_snd ((hAm t).comp measurable_fst)

private theorem exponentialKillingTime_cdf
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ≥0 → Ω → ℝ) (hAm : ∀ t, Measurable (A t))
    (hAc : ∀ ω, Continuous (fun t => A t ω))
    (hAmono : ∀ ω, Monotone (fun t => A t ω))
    (t : ℝ≥0) (hA0 : ∀ ω, 0 ≤ A t ω) :
    (P.prod (ProbabilityTheory.expMeasure 1)).real
      {q | exponentialKillingTime A q ≤ (t : ℝ≥0∞)} =
      ∫ ω, 1-Real.exp (-A t ω) ∂P := by
  classical
  let : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  let S : Set (Ω × ℝ) := {q | exponentialKillingTime A q ≤ (t : ℝ≥0∞)}
  have hS : MeasurableSet S :=
    measurableSet_le (exponentialKillingTime_measurable A hAm hAc hAmono) measurable_const
  change (P.prod (ProbabilityTheory.expMeasure 1)).real S = _
  rw [← integral_indicator_one hS,
    integral_prod _ ((integrable_const 1).indicator hS)]
  apply integral_congr_ae
  exact .of_forall fun ω => by
    have hrow : (fun e : ℝ => S.indicator (fun _ => (1 : ℝ)) (ω,e)) =
        {e | inverseHazard (fun t => A t ω) e ≤ (t : ℝ≥0∞)}.indicator
          (fun _ => (1 : ℝ)) := by
      funext e
      rfl
    change (∫ e, S.indicator (fun _ => (1 : ℝ)) (ω,e) ∂expMeasure 1) = _
    rw [hrow]
    have hs : {e | inverseHazard (fun t => A t ω) e ≤ (t : ℝ≥0∞)} = Iic (A t ω) := by
      ext e
      exact inverseHazard_le_iff _ (hAc ω) (hAmono ω) e t
    calc
      _ = (expMeasure 1).real {e | inverseHazard (fun t => A t ω) e ≤ (t : ℝ≥0∞)} :=
        integral_indicator_one (hs ▸ measurableSet_Iic)
      _ = _ := inverseHazard_unitExponential_cdf _ (hAc ω) (hAmono ω) t (hA0 ω)

variable {E : Type*} [MeasurableSpace E]

private theorem occupation_integrand_intervalIntegrable
    (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => κ (X r.toNNReal ω)) volume a b := by
  have hgm : Measurable (fun r : ℝ => κ (X r.toNNReal ω)) :=
    (hκ.comp (hX.comp (measurable_id.prodMk measurable_const))).comp
      measurable_real_toNNReal
  exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume a b).mono_fun'
    hgm.aestronglyMeasurable.restrict (.of_forall fun r => hK _)

private theorem occupation_continuous_of_bounded
    (κ : E → ℝ) (hκ : Measurable κ)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) (ω : Ω) :
    Continuous (fun t => FeynmanKac.occupation κ X t ω) := by
  exact (intervalIntegral.continuous_primitive
    (occupation_integrand_intervalIntegrable κ hκ X hX K hK ω) 0).comp
      NNReal.continuous_coe

private theorem occupation_monotone_of_bounded
    (κ : E → ℝ) (hκ : Measurable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) (ω : Ω) :
    Monotone (fun t => FeynmanKac.occupation κ X t ω) := by
  intro s t hst
  exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg
    (show (s : ℝ) ≤ (t : ℝ) from hst)
    (.of_forall fun r => hκ0 _)
    (occupation_integrand_intervalIntegrable κ hκ X hX K hK ω 0 t)

/-- The manuscript's actual killing time for a bounded measurable rate,
on the original process space extended by an independent unit exponential. -/
def occupationKillingTime (κ : E → ℝ) (X : ℝ≥0 → Ω → E) : Ω × ℝ → ℝ≥0∞ :=
  exponentialKillingTime (FeynmanKac.occupation κ X)

/-- Bounded measurable killing rates suffice for measurability of the
actual killing time; neither the rate nor the trajectories need be continuous. -/
theorem occupationKillingTime_measurable
    (κ : E → ℝ) (hκ : Measurable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) :
    Measurable (occupationKillingTime κ X) :=
  exponentialKillingTime_measurable _
    (fun t => (FeynmanKac.occupation_stronglyMeasurable κ hκ X hX t).measurable)
    (occupation_continuous_of_bounded κ hκ X hX K hK)
    (occupation_monotone_of_bounded κ hκ hκ0 X hX K hK)

/-- The exact killing probability is one minus the Feynman--Kac survival
weight averaged over the original process. This discharges the independent
exponential construction, without assuming a resolvent identification. -/
theorem occupationKillingTime_cdf
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : E → ℝ) (hκ : Measurable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) (t : ℝ≥0) :
    (P.prod (ProbabilityTheory.expMeasure 1)).real
      {q | occupationKillingTime κ X q ≤ (t : ℝ≥0∞)} =
      ∫ ω, 1-FeynmanKac.survival κ X t ω ∂P := by
  exact exponentialKillingTime_cdf P (FeynmanKac.occupation κ X)
    (fun t => (FeynmanKac.occupation_stronglyMeasurable κ hκ X hX t).measurable)
    (occupation_continuous_of_bounded κ hκ X hX K hK)
    (occupation_monotone_of_bounded κ hκ hκ0 X hX K hK)
    t (fun ω => FeynmanKac.occupation_nonneg κ hκ0 X t ω)

/-- Actual killing on the independent exponential extension produces
exactly the existing Feynman--Kac path weights, for every integrable test
observable on the original process space. -/
theorem occupationKillingTime_alive_integral
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : E → ℝ) (hκ : Measurable κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (X : ℝ≥0 → Ω → E) (hX : Measurable (Function.uncurry X))
    (K : ℝ) (hK : ∀ x, ‖κ x‖ ≤ K) (t : ℝ≥0)
    (f : Ω → ℝ) (hf : Integrable f P) :
    (∫ q, {q | (t : ℝ≥0∞) < occupationKillingTime κ X q}.indicator
      (fun q : Ω × ℝ => f q.1) q ∂P.prod (expMeasure 1)) =
      ∫ ω, FeynmanKac.survival κ X t ω*f ω ∂P := by
  classical
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  let S : Set (Ω × ℝ) := {q | (t : ℝ≥0∞) < occupationKillingTime κ X q}
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    (occupationKillingTime_measurable κ hκ hκ0 X hX K hK)
  change (∫ q, S.indicator (fun q : Ω × ℝ => f q.1) q ∂P.prod (expMeasure 1)) = _
  rw [integral_prod _ ((hf.comp_fst (expMeasure 1)).indicator hS)]
  apply integral_congr_ae
  exact .of_forall fun ω => by
    have hrow : (fun e : ℝ => S.indicator (fun q : Ω × ℝ => f q.1) (ω,e)) =
        (Ioi (FeynmanKac.occupation κ X t ω)).indicator (fun _ => f ω) := by
      funext e
      have heq : (ω,e) ∈ S ↔ FeynmanKac.occupation κ X t ω < e := by
        change (t : ℝ≥0∞) < inverseHazard (fun r => FeynmanKac.occupation κ X r ω) e ↔ _
        rw [← not_le, inverseHazard_le_iff _
          (occupation_continuous_of_bounded κ hκ X hX K hK ω)
          (occupation_monotone_of_bounded κ hκ hκ0 X hX K hK ω), not_le]
      by_cases he : FeynmanKac.occupation κ X t ω < e
      · rw [indicator_of_mem (heq.mpr he), indicator_of_mem (show e ∈ Ioi _ from he)]
      · rw [indicator_of_notMem (fun h => he (heq.mp h)),
          indicator_of_notMem (show e ∉ Ioi _ from he)]
    change (∫ e, S.indicator (fun q : Ω × ℝ => f q.1) (ω,e) ∂expMeasure 1) = _
    rw [hrow, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul]
    have hsurv : (expMeasure 1).real (Ioi (FeynmanKac.occupation κ X t ω)) =
        FeynmanKac.survival κ X t ω := by
      rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
        ← ProbabilityTheory.cdf_eq_real,
        ProbabilityTheory.cdf_expMeasure_eq (by norm_num)]
      simp only [FeynmanKac.occupation_nonneg κ hκ0 X t ω, ↓reduceIte, one_mul,
        FeynmanKac.survival]
      ring
    rw [hsurv]

open AdaptiveGradientDisclosure TensorOrthogonalAction PureTensorJetFeatures
open SphericalProjectionMatrixFeature

private theorem projection_pair_inner {N : ℕ} (x y z : Vector N) :
    inner ℝ (projectionMatrixFeature x) (outerFeature y z) =
      inner ℝ y z-(N : ℝ)⁻¹*(inner ℝ x y*inner ℝ x z) := by
  rw [projectionMatrixFeature, inner_sub_left, real_inner_smul_left,
    identityFeature_outer_inner, outerFeature_inner]

private theorem pairedTensorFeature_action {N q j : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) :
    pairedTensorFeature N q j (U x) = action U (pairedTensorFeature N q j x) := by
  have ht (v : Fin (q+j+j) → Vector N) :
      inner ℝ (pairedTensorFeature N q j (U x)) (pureTensor (fun k => U (v k))) =
      inner ℝ (pairedTensorFeature N q j x) (pureTensor v) := by
    change inner ℝ (pairedTensorFeature N q j (U x)) (tensorFeature (fun k => U (v k))) =
      inner ℝ (pairedTensorFeature N q j x) (tensorFeature v)
    simp only [pairedTensorFeature_tensorFeature_inner, projection_pair_inner, U.inner_map_map]
  apply (rotatedBasis (p := q+j+j) U).repr.injective
  ext I
  simp only [OrthonormalBasis.repr_apply_apply, rotatedBasis_apply, rotatedFamily]
  have hr : inner ℝ (pureTensor (fun k => U (basisVector (I k))))
      (action U (pairedTensorFeature N q j x)) =
      inner ℝ (pureTensor (fun k => basisVector (I k))) (pairedTensorFeature N q j x) := by
    rw [← action_pureTensor, (action U).inner_map_map]
  rw [hr]
  exact (real_inner_comm _ _).trans
    ((ht (fun k => basisVector (I k))).trans (real_inner_comm _ _))

private theorem pairingReindexedTensor_rotated {N p : ℕ}
    (S : Finset (Fin p)) (L : List (Fin p × Fin p)) (hL : ValidPairing S L)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : SphericalAging.FiniteModel.Disorder N p) :
    pairingReindexedTensor S L hL (TensorHamiltonianRotation.rotatedDisorder U J) =
      TensorHamiltonianRotation.rotatedDisorder U (pairingReindexedTensor S L hL J) := by
  classical
  let q := (Finset.univ\S).card+L.length+L.length
  let e := pairingBlockEquiv S L hL
  let ei := pairingTensorIndexEquiv (N := N) S L hL
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ei
  have hRpure (v : Fin p → Vector N) :
      R (pureTensor v) = pureTensor (fun k => v (e k)) := by
    ext I
    change (∏ k : Fin p, v k (I (e.symm k))) = ∏ k : Fin q, v (e k) (I k)
    simpa only [Equiv.symm_apply_apply] using
      (e.prod_comp (fun k : Fin p => v k (I (e.symm k)))).symm
  have hcomm (z : EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p)) :
      R (action U z) = action U (R z) := by
    let b := EuclideanSpace.basisFun (SphericalAging.FiniteModel.TensorIndex N p) ℝ
    have hz : z = ∑ I, z I • b I := by
      simpa only [b, EuclideanSpace.basisFun_repr] using (b.sum_repr z).symm
    rw [hz]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro I _
    congr 1
    dsimp only [b]
    simp only [EuclideanSpace.basisFun_apply]
    rw [action_basis, rotatedFamily, hRpure]
    rw [show R (EuclideanSpace.single I 1) = EuclideanSpace.single (ei I) 1 from
      LinearIsometryEquiv.piLpCongrLeft_single ei I 1]
    rw [action_basis, rotatedFamily]
    rfl
  have hR (K : SphericalAging.FiniteModel.Disorder N p) :
      R (WithLp.toLp 2 K) = WithLp.toLp 2 (pairingReindexedTensor S L hL K) := by
    ext I
    change K (ei.symm I) = pairingReindexedTensor S L hL K I
    have hh := pairingReindexedTensor_apply_image S L hL K (ei.symm I)
    have hi : pairingTensorIndexEquiv S L hL (ei.symm I) = I := ei.apply_symm_apply I
    rw [hi] at hh
    exact hh.symm
  have hv : WithLp.toLp 2 (pairingReindexedTensor S L hL
      (TensorHamiltonianRotation.rotatedDisorder U J)) =
      WithLp.toLp 2 (TensorHamiltonianRotation.rotatedDisorder U (pairingReindexedTensor S L hL J)) := by
    rw [← hR, TensorHamiltonianRotation.rotatedDisorder, WithLp.toLp_ofLp,
      hcomm, hR, TensorHamiltonianRotation.rotatedDisorder, WithLp.toLp_ofLp]
  exact (WithLp.toLp_injective 2).eq_iff.mp hv

private def unitRotationEquiv {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    UnitSphere N ≃ UnitSphere N where
  toFun u := ⟨U u, by simpa only [Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map] using u.property⟩
  invFun u := ⟨U.symm u, by simpa only [Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map] using u.property⟩
  left_inv u := Subtype.ext (U.symm_apply_apply u)
  right_inv u := Subtype.ext (U.apply_symm_apply u)

private theorem originalProjectedTrace_rotated {N q j : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (x : Vector N) :
    originalProjectedTrace N q j (TensorHamiltonianRotation.rotatedDisorder U J) (U x) =
      originalProjectedTrace N q j J x := by
  unfold originalProjectedTrace
  rw [pairedTensorFeature_action, TensorHamiltonianRotation.rotatedDisorder,
    WithLp.toLp_ofLp, (action U).inner_map_map]

private theorem originalPairedEnvelope_rotated {N q j : ℕ} (hN : 2 ≤ N)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) :
    originalPairedEnvelope N q j (TensorHamiltonianRotation.rotatedDisorder U J) =
      originalPairedEnvelope N q j J := by
  let : NeZero N := ⟨by omega⟩
  let F := fun z : Bool × UnitSphere N =>
    inner ℝ (signedFeature (pairedGaussianFeature N q j) z)
      (WithLp.toLp 2 (TensorHamiltonianRotation.rotatedDisorder U J))
  let G := fun z : Bool × UnitSphere N =>
    inner ℝ (signedFeature (pairedGaussianFeature N q j) z) (WithLp.toLp 2 J)
  let e := Equiv.prodCongr (Equiv.refl Bool) (unitRotationEquiv U)
  have heval (z : Bool × UnitSphere N) : F (e z) = G z := by
    change inner ℝ (sign z.1 • pairedGaussianFeature N q j (unitRotationEquiv U z.2))
      (WithLp.toLp 2 (TensorHamiltonianRotation.rotatedDisorder U J)) =
      inner ℝ (sign z.1 • pairedGaussianFeature N q j z.2) (WithLp.toLp 2 J)
    rw [real_inner_smul_left, real_inner_smul_left]
    congr 1
    rw [← originalProjectedTrace_physicalAxis_eq hN q j
      (TensorHamiltonianRotation.rotatedDisorder U J) (unitRotationEquiv U z.2),
      ← originalProjectedTrace_physicalAxis_eq hN q j J z.2]
    have hphys : physicalAxis (unitRotationEquiv U z.2) = U (physicalAxis z.2) := by
      change Real.sqrt N • U (z.2 : Vector N) = U (Real.sqrt N • (z.2 : Vector N))
      exact (U.map_smul _ _).symm
    rw [hphys, originalProjectedTrace_rotated]
  change (⨆ z, F z) = ⨆ z, G z
  exact e.iSup_comp.symm.trans (iSup_congr heval)

/-- The original latitude correction event is orthogonally invariant:
trace contractions and their actual supremum commute with rotations. -/
theorem originalLatitudeMeanGood_rotated {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    (U : Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) :
    rotatedDisorder U J ∈ originalLatitudeMeanGood n μ ↔ J ∈ originalLatitudeMeanGood n μ := by
  have henv {p : ℕ} (S : Finset (Fin p)) (L : List (Fin p × Fin p)) (hL : ValidPairing S L)
      (K : SphericalAging.FiniteModel.Disorder (n+1) p) :
      latitudePairingEnvelope n p S L hL (TensorHamiltonianRotation.rotatedDisorder U K) =
        latitudePairingEnvelope n p S L hL K := by
    unfold latitudePairingEnvelope
    rw [pairingReindexedTensor_rotated]
    exact originalPairedEnvelope_rotated (by omega) U _
  have hbad {p : ℕ} (K : SphericalAging.FiniteModel.Disorder (n+1) p) :
      TensorHamiltonianRotation.rotatedDisorder U K ∈ latitudeCorrectionBadBanks n p ↔
        K ∈ latitudeCorrectionBadBanks n p := by
    simp only [latitudeCorrectionBadBanks, Set.mem_iUnion, Set.mem_ofPred_eq, henv]
  change (rotatedDisorder U J ∈ regularDisorder ∧
    ∀ p, TensorHamiltonianRotation.rotatedDisorder U (J p) ∉ latitudeCorrectionBadBanks n p.val.val) ↔
      (J ∈ regularDisorder ∧ ∀ p, J p ∉ latitudeCorrectionBadBanks n p.val.val)
  rw [regularDisorder_rotated]
  simp only [hbad]

/-- Both concrete conditioned laws used above are probability measures in
all sufficiently large dimensions; their normalizing masses are proved. -/
theorem analytic_laws_probability (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop, IsProbabilityMeasure (analyticDisorderLaw n μ) ∧
      IsProbabilityMeasure (analyticBoundarySeedLaw n μ) := by
  filter_upwards [analytic_mass_eventually μ, boundary_analytic_mass_eventually μ] with n hn hb
  constructor
  · apply ProbabilityTheory.cond_isProbabilityMeasure
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hn
    norm_num at hn
  · apply ProbabilityTheory.cond_isProbabilityMeasure
    intro hz
    have hh := hb.2
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hh
    norm_num at hh

end SlowEquilibration.SourceEntranceGoodEvent
