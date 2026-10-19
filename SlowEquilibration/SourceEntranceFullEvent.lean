-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceEntranceGoodEvent
public import SlowEquilibration.SourceEntranceHarmonicFinal

/-! Gaussian harmonic-sector envelopes and auxiliary entrance events.
The general zonal-Gram theorems prove feature continuity, expected supremum
bounds, Gaussian tails, and the exact manuscript source scale in every degree.
They use the proved scalar Gamma-weight bounds and introduce no literature
interface.  The auxiliary degree-zero event and its common consumers below
remain available on the actual original ordered Gaussian tensors.

The all-degree original harmonic projections, their covariance identities,
and the full manuscript event with every downstream consumer are constructed
in `SourceEntranceHarmonicSectors.FullEvent`.  The constant-completed event in
this module is an auxiliary refinement and is not identified with that full
event. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceFullEvent

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open SourceEntranceRegularityLiteral SourceEntranceGoodEvent SourceEntranceHarmonicFinal
open SourceEntranceHarmonic SourceEntranceRegressionBoundary WholeFieldRegression
open SphericalPosteriorGradientIndependence EntranceLatitudeTangentObservable
open SphericalAging.OrthogonalGaussianDisclosure
open SphericalAging.FiniteModel (Hamiltonian)
open scoped BigOperators RealInnerProductSpace NNReal ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Continuity of the genuine spherical-mean sector in the original tensor. -/
private theorem constantSector_continuous {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (c : ℝ) :
    Continuous (constantSector N p c) := by
  have he : constantSector N p c = fun J =>
      inner ℝ (constantSectorFeature N p c) (WithLp.toLp 2 J) :=
    funext (constantSector_eq_inner hN p c)
  rw [he]
  exact continuous_const.inner (by fun_prop)

/-- Taking the uniform spherical mean commutes with the actual tensor rotation. -/
private theorem constantSector_rotated {N p : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (c : ℝ) (J : SphericalAging.FiniteModel.Disorder N p) :
    constantSector N p c (TensorHamiltonianRotation.rotatedDisorder U J) =
      constantSector N p c J := by
  unfold constantSector
  have he (x : Vector N) :
      Hamiltonian N p (TensorHamiltonianRotation.rotatedDisorder U J) x =
        Hamiltonian N p J (U.symm x) := by
    simpa only [U.apply_symm_apply] using
      (TensorHamiltonianRotation.Hamiltonian_rotated U J (U.symm x))
  simp_rw [he]
  exact ((MeasureTheory.integral_map U.symm.continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Vector N =>
      Real.sqrt c * Hamiltonian N p J x) ((sphereLaw N).map U.symm) from
        ((continuous_iff_continuousAt.mpr (fun x =>
          (LandscapeDerivatives.Hamiltonian_hasFDerivAt J x).continuousAt)).const_mul
            (Real.sqrt c)).aestronglyMeasurable)).symm.trans
        (by rw [sphereLaw_rotation_invariant]))

private theorem gaussian_inner_tail {ι : Type*} [Fintype ι]
    (b : EuclideanSpace ℝ ι) (N : ℕ) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g | 4*‖b‖*Real.sqrt N < |inner ℝ b g|} ≤
        2*Real.exp (-8*(N : ℝ)) := by
  by_cases hb : b = 0
  · simp only [hb, norm_zero, mul_zero, zero_mul, inner_zero_left, abs_zero, lt_self_iff_false, Set.ofPred_false, measureReal_empty]
    positivity
  · have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hLip : LipschitzWith ‖b‖₊ (fun g => inner ℝ b g) := by
      have hnn : ‖innerSL ℝ b‖₊ = ‖b‖₊ := by
        ext
        exact innerSL_apply_norm ℝ b
      rw [← hnn]
      exact (innerSL ℝ b).lipschitzWith
    have ht := SphericalModel.euclidean_lipschitz_gaussian_closed_tail
      (fun g : EuclideanSpace ℝ ι => inner ℝ b g) ‖b‖
      (4*‖b‖*Real.sqrt N) hbn (by positivity) (by simpa using hLip)
    have hm : (∫ g, inner ℝ b g ∂SYK.standardGaussianMeasureOnEuclidean ι) = 0 :=
      by simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian, innerSL_apply_apply]
        using integral_strongDual_stdGaussian (innerSL ℝ b)
    simp only [hm, sub_zero] at ht
    have htr := ENNReal.toReal_mono (by finiteness) ht
    rw [ENNReal.toReal_ofReal (by positivity)] at htr
    apply (measureReal_mono (fun g hx => by
      change 4*‖b‖*Real.sqrt N < |inner ℝ b g| at hx
      change 4*‖b‖*Real.sqrt N ≤ |inner ℝ b g|
      exact hx.le)).trans (htr.trans_eq ?_)
    congr 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp
    ring

/-- The true spherical mean has an exponential tail at its own coefficient
norm; this remains valid when that sector is identically zero. -/
private theorem constantSector_upper_tail {N : ℕ} (hN : 0 < N) (p : ℕ) (c : ℝ) :
    (SphericalAging.FiniteModel.disorderLaw N p).real
      {J | 4*‖constantSectorFeature N p c‖*Real.sqrt N < |constantSector N p c J|} ≤
        2*Real.exp (-8*(N : ℝ)) := by
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N p →
      EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p))
      (SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N p))
      (SphericalAging.FiniteModel.disorderLaw N p) := ⟨by fun_prop,rfl⟩
  have hm : MeasurableSet {g : EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p) |
      4*‖constantSectorFeature N p c‖*Real.sqrt N < |inner ℝ (constantSectorFeature N p c) g|} :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id).abs).measurableSet
  simp_rw [constantSector_eq_inner hN]
  rw [hLaw.measureReal_eq hm]
  exact gaussian_inner_tail (constantSectorFeature N p c) N

/-- All genuine spherical-mean sectors satisfy one simultaneous Gaussian
threshold.  The threshold uses their actual variance, including odd degrees
and zero-amplitude blocks. -/
def constantSectorGood (N : ℕ) (μ : FiniteMixture) : Set (Disorder N μ.maxDegree) :=
  {J | ∀ p : Degree μ.maxDegree,
    |constantSector N p.val.val (mixtureCoefficients μ p) (J p)| ≤
      4*‖constantSectorFeature N p.val.val (mixtureCoefficients μ p)‖*Real.sqrt N}

/-- The additional event is Borel in the original coefficient vector. -/
private theorem constantSectorGood_measurable {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) :
    MeasurableSet (constantSectorGood N μ) := by
  unfold constantSectorGood
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro p
  exact (isClosed_le ((constantSector_continuous hN p.val.val
    (mixtureCoefficients μ p)).comp (by fun_prop)).abs continuous_const).measurableSet

/-- The spherical-mean event is invariant under every orthogonal rotation. -/
private theorem constantSectorGood_rotated {N : ℕ} (μ : FiniteMixture)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree) :
    rotatedDisorder U J ∈ constantSectorGood N μ ↔ J ∈ constantSectorGood N μ := by
  change (∀ p : Degree μ.maxDegree,
    |constantSector N p.val.val (mixtureCoefficients μ p)
      (TensorHamiltonianRotation.rotatedDisorder U (J p))| ≤ _) ↔ _
  simp only [constantSector_rotated]
  rfl

/-- A finite union bound retains the actual Gaussian scale of every constant
sector; no independence assumption between sectors is needed here. -/
private theorem constantSectorGood_failure {N : ℕ} (hN : 0 < N) (μ : FiniteMixture) :
    (disorderLaw N μ.maxDegree).real (constantSectorGood N μ)ᶜ ≤
      (Fintype.card (Degree μ.maxDegree) : ℝ)*(2*Real.exp (-8*(N : ℝ))) := by
  have he : (constantSectorGood N μ)ᶜ =
      ⋃ p : Degree μ.maxDegree, {J : Disorder N μ.maxDegree |
        4*‖constantSectorFeature N p.val.val (mixtureCoefficients μ p)‖*Real.sqrt N <
          |constantSector N p.val.val (mixtureCoefficients μ p) (J p)|} := by
    ext J
    simp [constantSectorGood, not_forall, not_le]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _p : Degree μ.maxDegree, 2*Real.exp (-8*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      rw [(degree_block_hasLaw p).measureReal_eq
        (isOpen_lt continuous_const (constantSector_continuous hN p.val.val
          (mixtureCoefficients μ p)).abs).measurableSet]
      exact constantSector_upper_tail hN p.val.val (mixtureCoefficients μ p)
    _ = _ := by simp

/-- The existing common analytic event, refined only by the genuine
constant-harmonic Gaussian bounds. -/
def constantCompletedEntranceEvent (n : ℕ) (μ : FiniteMixture) :
    Set (Disorder (n+1) μ.maxDegree) :=
  originalLatitudeMeanGood n μ ∩ constantSectorGood (n+1) μ

/-- Refining the analytic event does not change its deterministic latitude,
multiplier, or nonharmonic regularity implications. -/
private theorem constantCompletedEntranceEvent_subset (n : ℕ) (μ : FiniteMixture) :
    constantCompletedEntranceEvent n μ ⊆ originalLatitudeMeanGood n μ :=
  inter_subset_left

/-- The refinement is Borel. -/
private theorem constantCompletedEntranceEvent_measurable {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) : MeasurableSet (constantCompletedEntranceEvent n μ) :=
  (originalLatitudeMeanGood_measurable hn μ).inter (constantSectorGood_measurable (by omega) μ)

/-- The refinement preserves literal rotation invariance in tensor coordinates. -/
theorem constantCompletedEntranceEvent_rotated {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) (U : Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1))
    (J : Disorder (n+1) μ.maxDegree) :
    rotatedDisorder U J ∈ constantCompletedEntranceEvent n μ ↔
      J ∈ constantCompletedEntranceEvent n μ := by
  simp only [constantCompletedEntranceEvent, mem_inter_iff,
    originalLatitudeMeanGood_rotated hn μ, constantSectorGood_rotated μ]

/-- The coefficient norm is exactly the manuscript's constant-sector variance. -/
private theorem constantSectorFeature_norm_sq {N k : ℕ} (hN : 3 ≤ N) (hk : 1 ≤ k)
    {c : ℝ} (hc : 0 ≤ c) :
    ‖constantSectorFeature N (2*k) c‖^2 =
      (N : ℝ)*c*gammaWeight N (2*k) k := by
  have he := constantSector_covariance hN hk hc
  have hfun : constantSector N (2*k) c = fun J =>
      inner ℝ (constantSectorFeature N (2*k) c) (WithLp.toLp 2 J) :=
    funext (constantSector_eq_inner (by omega) (2*k) c)
  rw [hfun, tensor_inner_covariance] at he
  simpa only [real_inner_self_eq_norm_sq] using he

open SphericalLatitudeTensorMoments FiniteWickPairings
open PairedTensorProjectionFeatures

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

private theorem dimension_div_sqrt_pow {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (N : ℝ)/Real.sqrt ((N : ℝ)^k) = (N : ℝ)^(1-(k : ℝ)/2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [Real.rpow_sub hNr, Real.rpow_one]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  congr 1
  ring

/-- Every even-degree constant sector has the precise envelope scale printed
in `lem:ent-regularity`(2), with a constant fixed before the dimension. -/
private theorem constantSector_threshold_source_scale (k : ℕ) (hk : 1 ≤ k)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      4*‖constantSectorFeature N (2*k) c‖*Real.sqrt N ≤
        C*(N : ℝ)^(1-(k : ℝ)/2) := by
  obtain ⟨A,hA,hweight⟩ := gammaWeights_bound_all_dimensions (2*k)
  refine ⟨4*Real.sqrt (c*A)+1,by positivity,?_⟩
  intro N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hpow : 0 < (N : ℝ)^k := pow_pos hNr k
  have hsq := constantSectorFeature_norm_sq hN hk hc
  have hw := (le_div_iff₀ hpow).mp (hweight N hN k (by omega))
  have hprod : (‖constantSectorFeature N (2*k) c‖*Real.sqrt N*
      Real.sqrt ((N : ℝ)^k))^2 ≤ (Real.sqrt (c*A)*(N : ℝ))^2 := by
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N),
      Real.sq_sqrt hpow.le, Real.sq_sqrt (mul_nonneg hc hA.le), hsq]
    have h := mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg (N : ℝ)) hc)
    nlinarith
  have hnorm : ‖constantSectorFeature N (2*k) c‖*Real.sqrt N*
      Real.sqrt ((N : ℝ)^k) ≤ Real.sqrt (c*A)*(N : ℝ) := by
    nlinarith [show 0 ≤ Real.sqrt (c*A)*(N : ℝ) by positivity]
  have hnorm' : ‖constantSectorFeature N (2*k) c‖*Real.sqrt N ≤
      Real.sqrt (c*A)*(N : ℝ)^(1-(k : ℝ)/2) := by
    have hdiv := (le_div_iff₀ (Real.sqrt_pos.2 hpow)).2 hnorm
    simpa only [mul_div_assoc, dimension_div_sqrt_pow (by omega : 0 < N)] using hdiv
  have hr : 0 ≤ (N : ℝ)^(1-(k : ℝ)/2) := Real.rpow_nonneg hNr.le _
  nlinarith

/-- The actual even-degree spherical means satisfy the harmonic clause at
its exact source scale on the additional event. -/
theorem constantSector_source_bound (μ : FiniteMixture) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ∀ J ∈ constantSectorGood N μ, ∀ (p : Degree μ.maxDegree) (k : ℕ),
        p.val.val = 2*k →
        |constantSector N p.val.val (mixtureCoefficients μ p) (J p)| ≤
          C*(N : ℝ)^(1-(k : ℝ)/2) := by
  classical
  have h (p : Degree μ.maxDegree) :
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, p.val.val = 2*k → ∀ N : ℕ, 3 ≤ N →
        4*‖constantSectorFeature N p.val.val (mixtureCoefficients μ p)‖*Real.sqrt N ≤
          C*(N : ℝ)^(1-(k : ℝ)/2) := by
    by_cases he : ∃ k : ℕ, p.val.val = 2*k
    · obtain ⟨k,hk⟩ := he
      obtain ⟨C,hC,hbound⟩ := constantSector_threshold_source_scale k
        (by have hp := p.property; change 2 ≤ p.val.val at hp; omega)
        (mixtureCoefficients_nonnegative μ p)
      refine ⟨C,hC,?_⟩
      intro j hj N hN
      have heq : j = k := by omega
      subst j
      change 4*‖constantSectorFeature N p.val.val (mixtureCoefficients μ p)‖*Real.sqrt N ≤ _
      rw [hk]
      exact hbound N hN
    · exact ⟨1,by norm_num,fun k hk => (he ⟨k,hk⟩).elim⟩
  choose C hC hbound using h
  have hsum : 0 ≤ ∑ p : Degree μ.maxDegree, C p :=
    Finset.sum_nonneg fun p _ => (hC p).le
  refine ⟨1+∑ p : Degree μ.maxDegree, C p,by linarith,?_⟩
  intro N hN J hJ p k hk
  have hle : C p ≤ 1+∑ p : Degree μ.maxDegree, C p := by
    have := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) => (hC q).le)
      (Finset.mem_univ p)
    linarith
  exact (hJ p).trans ((hbound p k hk N hN).trans
    (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (Nat.cast_nonneg N) _)))

private theorem originalLatitudeMeanGood_spare_failure {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) :
    (disorderLaw (n+1) μ.maxDegree).real (originalLatitudeMeanGood n μ)ᶜ ≤
      (1+4*(originalLatitudeBankCount μ : ℝ))*Real.exp (-2*((n+1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨p,hp⟩ := μ.support_nonempty
  have hP : 2 ≤ μ.maxDegree := (μ.degree_ge_two hp).trans (μ.degree_bounds hp).2
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
          convert (degree_block_hasLaw p).measure_eq (latitudeCorrectionBadBanks_measurable hn) using 1
          all_goals congr 1
        rw [heq]
        exact latitudeCorrectionBadBanks_sharp_tail hn
      _ = _ := by rw [← Finset.sum_mul]; simp only [originalLatitudeBankCount, Nat.cast_sum]
  have hbr := ENNReal.toReal_mono (by finiteness) hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2))] at hbr
  rw [he]
  apply (measureReal_union_le _ _).trans
  apply (add_le_add (regularDisorder_sharp_tail (by omega) hP) hbr).trans
  have he := Real.exp_le_exp.mpr (show -9*((n+1 : ℕ) : ℝ)/2 ≤ -2*((n+1 : ℕ) : ℝ) by have h : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _; linarith)
  nlinarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (originalLatitudeBankCount μ))]

/-- Adding the genuine constant-sector bounds preserves the exact printed
failure rate, using the spare decay of the original analytic event. -/
theorem constantCompletedEntranceEvent_failure (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop, (disorderLaw (n+1) μ.maxDegree).real
      (constantCompletedEntranceEvent n μ)ᶜ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := by
  let A : ℝ := 1+4*(originalLatitudeBankCount μ : ℝ)+2*Fintype.card (Degree μ.maxDegree)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨M,hM⟩ := exists_nat_ge (Real.log A)
  filter_upwards [eventually_ge_atTop (max M 1)] with n hn
  have he : (constantCompletedEntranceEvent n μ)ᶜ =
      (originalLatitudeMeanGood n μ)ᶜ ∪ (constantSectorGood (n+1) μ)ᶜ := by
    simp only [constantCompletedEntranceEvent, compl_inter]
  rw [he]
  apply (measureReal_union_le _ _).trans
  apply (add_le_add (originalLatitudeMeanGood_spare_failure (by omega) μ)
    (constantSectorGood_failure (by omega) μ)).trans
  have hdim : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have he := Real.exp_le_exp.mpr (show -8*((n+1 : ℕ) : ℝ) ≤ -2*((n+1 : ℕ) : ℝ) by linarith)
  calc
    _ ≤ A*Real.exp (-2*((n+1 : ℕ) : ℝ)) := by
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (Fintype.card (Degree μ.maxDegree)))]
    _ = Real.exp (Real.log A-2*((n+1 : ℕ) : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.exp_log hA]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log A ≤ ((n+1 : ℕ) : ℝ) :=
        hM.trans (by exact_mod_cast (show M ≤ n+1 by omega))
      linarith

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

/-- The law obtained by conditioning only the actual Gaussian coefficient
vector on the common analytic event. -/
def constantCompletedDisorderLaw (n : ℕ) (μ : FiniteMixture) : Measure (Disorder (n+1) μ.maxDegree) :=
  ProbabilityTheory.cond (disorderLaw (n+1) μ.maxDegree) (constantCompletedEntranceEvent n μ)

private theorem constant_completed_mass_eventually (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ (disorderLaw (n+1) μ.maxDegree).real (constantCompletedEntranceEvent n μ) := by
  filter_upwards [constantCompletedEntranceEvent_failure μ, eventually_ge_atTop 1] with n hn hn1
  exact mass_half_of_failure _ (constantCompletedEntranceEvent_measurable hn1 μ) (by omega) hn

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

/-- The mixed truncated cap estimate on the constant-completed coefficient event
for every smaller
positive horizon exponent. No conditioning-mass assumption remains. -/
theorem constant_completed_conditioned_mixed_truncated
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 c C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < c ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
            (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e k J ∂constantCompletedDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hall⟩ := conditioned_mixed_truncated_cap_avoidance μ hd hQ hQ1 hnp hB hβ
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (constant_completed_mass_eventually μ)
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
    (fun _ hJ => hJ.1.1) (hn1 n (by omega)) hpos f hi (fun J => (hf J).1)
  have hr := hbound n (by omega) hγ hγ0' e k he hk
  have ht := two_exp_le hc (x := ((n+1 : ℕ) : ℝ))
    (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans (by nlinarith))

/-- Proper-pure truncated cap avoidance under that identical analytic-event
conditioning, with every amplitude and every smaller positive exponent. -/
theorem constant_completed_conditioned_pure_truncated
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 κ C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < κ ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e : ℝ, |e| ≤ B →
            (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e J ∂constantCompletedDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-κ*((n+1 : ℕ) : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
  obtain ⟨aStar,hStar,hall⟩ := conditioned_pure_truncated_cap_avoidance d hd c hc hQ hB hβ
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (constant_completed_mass_eventually μ)
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
    (fun _ hJ => hJ.1.1) (hn1 n (by omega)) hpos f hi (fun J => (hf J).1)
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

/-- The constant-completed coefficient event lifted to the literal joint seed
space: uniform axis, original Gaussian coefficients, initial point and noise. -/
def constantCompletedBoundaryEvent (n : ℕ) (μ : FiniteMixture) :
    Set (Vector (n+1) × BoundarySeed n μ) :=
  {q | unpackDisorder q.2.1 ∈ constantCompletedEntranceEvent n μ}

/-- Only the original disorder is conditioned. -/
def constantCompletedBoundarySeedLaw (n : ℕ) (μ : FiniteMixture) :
    Measure (Vector (n+1) × BoundarySeed n μ) :=
  ProbabilityTheory.cond (boundarySeedLaw n μ) (constantCompletedBoundaryEvent n μ)

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
theorem constantCompletedBoundarySeedLaw_eq_product (n : ℕ) (μ : FiniteMixture) :
    constantCompletedBoundarySeedLaw n μ =
      (sphereLaw (n+1)).prod
        ((ProbabilityTheory.cond (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
          {z | unpackDisorder z ∈ constantCompletedEntranceEvent n μ}).prod
            ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))) := by
  have he : constantCompletedBoundaryEvent n μ = univ ×ˢ
      ({z : EuclideanDisorder (n+1) μ.maxDegree |
        unpackDisorder z ∈ constantCompletedEntranceEvent n μ} ×ˢ univ) := by
    ext q
    simp only [constantCompletedBoundaryEvent, mem_ofPred_eq, mem_prod, mem_univ, true_and, and_true]
  unfold constantCompletedBoundarySeedLaw boundarySeedLaw
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

private theorem boundary_constant_completed_mass_eventually (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop,
      MeasurableSet (constantCompletedBoundaryEvent n μ) ∧
      (1/2 : ℝ) ≤ (boundarySeedLaw n μ).real (constantCompletedBoundaryEvent n μ) := by
  filter_upwards [constant_completed_mass_eventually μ, eventually_ge_atTop 1] with n hn hn1
  have hm := constantCompletedEntranceEvent_measurable hn1 μ
  have he := (boundary_original_hasLaw n μ).measureReal_eq hm
  refine ⟨hm.preimage ((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_snd.fst),?_⟩
  have he' : (boundarySeedLaw n μ).real (constantCompletedBoundaryEvent n μ) =
      (disorderLaw (n+1) μ.maxDegree).real (constantCompletedEntranceEvent n μ) := by
    convert he using 1 <;> congr 1
  rw [he']
  exact hn

local instance boundary_probability (n : ℕ) (μ : FiniteMixture) :
    IsProbabilityMeasure (boundarySeedLaw n μ) := by unfold boundarySeedLaw; infer_instance

/-- Mixed original-gradient boundary control under the very same disorder
conditioning used for latitude concentration, multipliers and truncation. -/
theorem constant_completed_conditioned_mixed_boundary
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {Q B β b : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (constantCompletedBoundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ :=
    mixed_uniform_axis_gradient_cutoff_not_reached μ hnp hQ hQ1 hB hβ hb
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (boundary_constant_completed_mass_eventually μ)
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
theorem constant_completed_conditioned_value_boundary
    (μ : FiniteMixture) {Q B β b : ℝ} (hQ : 0 < Q)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e : ℝ, |e| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (constantCompletedBoundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ := value_uniform_axis_gradient_cutoff_not_reached μ hQ hB hβ hb
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (boundary_constant_completed_mass_eventually μ)
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

/-- The two concrete laws conditioned on the constant-completed event have
positive normalizing mass in all sufficiently large dimensions. -/
theorem constant_completed_laws_probability (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop, IsProbabilityMeasure (constantCompletedDisorderLaw n μ) ∧
      IsProbabilityMeasure (constantCompletedBoundarySeedLaw n μ) := by
  filter_upwards [constant_completed_mass_eventually μ,
    boundary_constant_completed_mass_eventually μ] with n hn hb
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

/-- The completed constant-sector event supports all existing nonharmonic
regularity clauses, and the actual even-degree constant harmonics have the
precise missing scale.  This does not assert the positive-sector clause. -/
theorem constant_completed_regularity (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, ∃ n0 : ℕ, 0 < C ∧ ∀ n ≥ n0,
      MeasurableSet (constantCompletedEntranceEvent n μ) ∧
      (disorderLaw (n+1) μ.maxDegree).real (constantCompletedEntranceEvent n μ)ᶜ ≤
        Real.exp (-((n+1 : ℕ) : ℝ)) ∧
      (∀ (U : Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1)) (J : Disorder (n+1) μ.maxDegree),
        rotatedDisorder U J ∈ constantCompletedEntranceEvent n μ ↔
          J ∈ constantCompletedEntranceEvent n μ) ∧
      ∀ J ∈ constantCompletedEntranceEvent n μ,
        NonharmonicRegularClauses μ Q C J ∧
        ∀ (p : Degree μ.maxDegree) (k : ℕ), p.val.val = 2*k →
          |constantSector (n+1) p.val.val (mixtureCoefficients μ p) (J p)| ≤
            C*((n+1 : ℕ) : ℝ)^(1-(k : ℝ)/2) := by
  obtain ⟨C,hC,hreg⟩ := nonharmonic_regular_event μ Q
  obtain ⟨D,hD,hconst⟩ := constantSector_source_bound μ
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (constantCompletedEntranceEvent_failure μ)
  refine ⟨C+D,max n0 2,by positivity,?_⟩
  intro n hn
  refine ⟨constantCompletedEntranceEvent_measurable (by omega) μ,hn0 n (by omega),
    fun U J => constantCompletedEntranceEvent_rotated (by omega) μ U J,?_⟩
  intro J hJ
  obtain ⟨hm,hv,hg,hh⟩ := (hreg (n+1) (by omega)).2.2.2 J hJ.1.1
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · intro p x hx m hm3
      exact (hm p x hx m hm3).trans (mul_le_mul_of_nonneg_right
        (by linarith : C ≤ C+D) (Nat.cast_nonneg _))
    · exact hv.trans (mul_le_mul_of_nonneg_right
        (by linarith : C ≤ C+D) (Nat.cast_nonneg _))
    · exact hg.trans (mul_le_mul_of_nonneg_right
        (by linarith : C ≤ C+D) (Real.sqrt_nonneg _))
    · exact hh.trans (by linarith)
  · intro p k hk
    exact (hconst (n+1) (by omega) J hJ.2 p k hk).trans
      (mul_le_mul_of_nonneg_right (by linarith : D ≤ C+D)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The exact latitude-mean estimate used downstream remains valid for every
original sample in the constant-completed event. -/
theorem constant_completed_latitude_mean {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J ∈ constantCompletedEntranceEvent n μ)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1 : ℕ) : ℝ))
    {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (mixtureCoefficients μ) J u (latitudeFrameAt u) r| ≤
      originalLatitudeLeadingConstant μ*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        originalLatitudeCorrectionConstant μ :=
  actual_original_latitudeObservableMean_uniform_bound hn μ J hJ.1 u hu hr

/-- The printed multiplier moments and cutoff suprema on the same
constant-completed original Gaussian event, with all existing constants. -/
theorem constant_completed_mixed_multipliers (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {Q M β : ℝ} (hQ : 0 < Q) (hQone : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    ∃ α₀ C : ℝ, ∃ N₀ : ℕ,
      0 < α₀ ∧ α₀ ≤ 1/8 ∧ 0 < C ∧
      ∀ (n : ℕ), N₀ ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ constantCompletedEntranceEvent n μ →
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∀ e k : ℝ, |e| ≤ M → |k| ≤ M →
      ∀ (x : Vector (n+1)), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      let W := fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-
        fieldOfMixture μ J x
      (∫ u, |Real.exp (β*W u)-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u, Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) ∧
      ∀ (u : Vector (n+1)), OnSphere u →
        |W u| ≤ C*((n+1 : ℕ) : ℝ)*α^μ.minDegree ∧
        ‖gradient (fun y => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ y-
            fieldOfMixture μ J y) x‖ ≤
          C*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(μ.minDegree-1) := by
  obtain ⟨α₀,C,N₀,hα₀,hα₀small,hC,hbound⟩ :=
    SourceSphereSharpConcentration.mixed_source_cutoff_multipliers_and_suprema μ hd hQ hQone hnp hM hβ χ hχ hχb hχ0
  refine ⟨α₀,C,N₀,hα₀,hα₀small,hC,?_⟩
  intro n hn J hJ α hα hαsmall e k he hk x hx
  exact hbound n hn J hJ.1 α hα hαsmall e k he hk x hx

/-- The printed multiplier moments and cutoff suprema on the same
constant-completed original Gaussian event, with all existing constants. -/
theorem constant_completed_pure_multipliers (p : ℕ) (hp : 4 ≤ p)
    (c : ℝ) (hc : 0 < c) {Q M β : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ α₀ C : ℝ, ∃ N₀ : ℕ,
      0 < α₀ ∧ α₀ ≤ 1/8 ∧ 0 < C ∧
      ∀ (n : ℕ), N₀ ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ constantCompletedEntranceEvent n μ →
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∀ e : ℝ, |e| ≤ M →
      ∀ (x : Vector (n+1)), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      let W := fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-
        fieldOfMixture μ J x
      (∫ u, |Real.exp (β*W u)-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u, Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) ∧
      ∀ (u : Vector (n+1)), OnSphere u →
        |W u| ≤ C*((n+1 : ℕ) : ℝ)*α^p ∧
        ‖gradient (fun y => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ y-
            fieldOfMixture μ J y) x‖ ≤
          C*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(p-1) := by
  dsimp only
  obtain ⟨α₀,C,N₀,hα₀,hα₀small,hC,hbound⟩ :=
    SourceSphereSharpConcentration.pure_source_cutoff_multipliers_and_suprema p hp c hc hQ hM hβ χ hχ hχb hχ0
  refine ⟨α₀,C,N₀,hα₀,hα₀small,hC,?_⟩
  intro n hn J hJ α hα hαsmall e he x hx
  exact hbound n hn J hJ.1 α hα hαsmall e he x hx

/-- Both clauses of `lem:ent-latitude` on the constant-completed event.
The sphere logarithmic Sobolev premise is precisely the existing documented
`SourceSphereSharpConcentration.BakryEmerySphereLogSobolev` interface; no
additional harmonic, probabilistic, or concentration premise is introduced. -/
theorem constant_completed_center_latitude_mean_and_mgf (hLSI : SourceSphereSharpConcentration.BakryEmerySphereLogSobolev)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ constantCompletedEntranceEvent n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) := by
  obtain ⟨C,hC,hbound⟩ :=
    SourceSphereSharpConcentration.center_latitude_mean_and_mgf hLSI μ hQ
  refine ⟨C,hC,?_⟩
  intro n hn J hJ x hx r hr
  exact hbound n hn J hJ.1 x hx r hr

open PureTensorJetBounds GaussianCompactMaximum GaussianSharpAbsoluteMaximum

private theorem zonal_uniform_chord_bound (ell : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (N : ℕ), 3 ≤ N → ∀ r : ℝ, |r| ≤ 1 →
      |zonal N ell r-1| ≤ D*(1-r) := by
  obtain ⟨A,hA,hderiv⟩ := zonal_derivative_bound ell
  let D := 1+2*A
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro N hN r hr
  have hderiv' (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ‖deriv (zonal N ell) t‖ ≤ D := by
    have ht' : |t| ≤ 1 := abs_le.mpr ht
    have hp : |t|^(ell-1) ≤ 1 := pow_le_one₀ (abs_nonneg t) ht'
    have hi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      exact_mod_cast (show 1 ≤ N by omega))
    have h := hderiv N hN t ht'
    rw [Real.norm_eq_abs]
    dsimp [D]
    nlinarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc (-1 : ℝ) 1) =>
      ((contDiff_zonal N ell).differentiable (by simp)) t)
    hderiv' (convex_Icc (-1 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
    (abs_le.mp hr)
  rw [zonal_at_one hN, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [(abs_le.mp hr).2] : r-1 ≤ 0)] at h
  nlinarith

/-- Standard Gaussian supremum control from the literal zonal Gram identity.
The comparison constant depends only on the harmonic degree.  Continuity,
the mean bound, and the exponential tail are proved from that deterministic
identity; no analytic literature interface is assumed.  Instantiating this
lemma for every original harmonic sector still requires constructing those
features and proving their Gram identities. -/
theorem zonalFeature_supremum_upper_tail (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 3 ≤ N →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (a : UnitSphere N → EuclideanSpace ℝ ι) {b : ℝ}, 0 ≤ b →
        (∀ u v : UnitSphere N,
          inner ℝ (a u) (a v) = b^2*zonal N ell (inner ℝ (u : Vector N) (v : Vector N))) →
        Continuous a ∧
        (∫ g, absoluteSupremum a g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
          C*b*Real.sqrt N ∧
        ∀ {s : ℝ}, 0 ≤ s →
          (SYK.standardGaussianMeasureOnEuclidean ι).real
            {g | (C+s)*b*Real.sqrt N < absoluteSupremum a g} ≤
              Real.exp (-s^2*(N : ℝ)/2) := by
  obtain ⟨D,hD,hchord⟩ := zonal_uniform_chord_bound ell
  have hD0 : 0 < D := by linarith
  have hP : 1 ≤ Real.sqrt D := (Real.le_sqrt (by norm_num) hD0.le).2 (by nlinarith)
  refine ⟨2*Real.sqrt D,by positivity,?_⟩
  intro N hN ι _ _ a b hb hgram
  let : NeZero N := ⟨by omega⟩
  have hnormsq (u : UnitSphere N) : ‖a u‖^2 = b^2 := by
    have h := hgram u u
    simpa only [real_inner_self_eq_norm_sq, unit_norm, one_pow,
      zonal_at_one hN, mul_one] using h
  have hnorm (u : UnitSphere N) : ‖a u‖ = b :=
    (sq_eq_sq₀ (norm_nonneg _) hb).mp (hnormsq u)
  have hinc (u v : UnitSphere N) :
      ‖a u-a v‖ ≤ b*Real.sqrt D*‖(u : Vector N)-(v : Vector N)‖ := by
    have hr : |inner ℝ (u : Vector N) (v : Vector N)| ≤ 1 := by
      simpa only [unit_norm, one_mul] using abs_real_inner_le_norm (u : Vector N) (v : Vector N)
    have hc := hchord N hN (inner ℝ (u : Vector N) (v : Vector N)) hr
    have hz : 1-zonal N ell (inner ℝ (u : Vector N) (v : Vector N)) ≤
        D*(1-inner ℝ (u : Vector N) (v : Vector N)) := by
      have hh := neg_le_abs (zonal N ell (inner ℝ (u : Vector N) (v : Vector N))-1)
      linarith
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hD0.le, norm_sub_sq_real,
      hnormsq, hnormsq, hgram, norm_sub_sq_real]
    simp only [unit_norm, one_pow]
    have h := mul_le_mul_of_nonneg_left hz (sq_nonneg b)
    nlinarith
  have hLip : LipschitzWith (b*Real.sqrt D).toNNReal a := by
    apply LipschitzWith.of_dist_le'
    intro u v
    change dist (a u) (a v) ≤ b*Real.sqrt D*dist (u : Vector N) (v : Vector N)
    simpa only [dist_eq_norm] using hinc u v
  have ha : Continuous a := hLip.continuous
  have hmean := expected_absoluteSupremum_le_twice a
    (fun u : UnitSphere N => (u : Vector N)) ha continuous_subtype_val
    (L := b*Real.sqrt D) (by positivity)
    (fun u => (hnorm u).le.trans (le_mul_of_one_le_right hb hP)) unit_norm hinc
  simp only [Fintype.card_fin] at hmean
  refine ⟨ha,by nlinarith [hmean],?_⟩
  intro s hs
  by_cases hb0 : b = 0
  · have hazero : a = fun _ => 0 := by
      funext u
      apply norm_eq_zero.mp
      simpa only [hb0] using hnorm u
    have hsup : absoluteSupremum a = fun _ => 0 := by
      funext g
      simp [absoluteSupremum, signedFeature, hazero]
    rw [hsup, hb0]
    simp only [mul_zero, zero_mul, lt_self_iff_false, Set.ofPred_false, measureReal_empty]
    positivity
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hsupLip : LipschitzWith b.toNNReal (absoluteSupremum a) := by
      apply field_supremum_lipschitz
        (fun v : Bool × UnitSphere N => innerSL ℝ (signedFeature a v))
      intro v
      simpa only [innerSL_apply_norm, signedFeature, norm_smul, Real.norm_eq_abs,
        abs_sign, one_mul, hnorm] using (le_rfl : b ≤ b)
    have ht := GaussianNormConcentration.centered_lipschitz_upper_tail
      (absoluteSupremum a) hb hsupLip (s := s*b*Real.sqrt N) (by positivity)
    have hsub : {g | (2*Real.sqrt D+s)*b*Real.sqrt N < absoluteSupremum a g} ⊆
        {g | (∫ z, absoluteSupremum a z ∂SYK.standardGaussianMeasureOnEuclidean ι)+
          s*b*Real.sqrt N ≤ absoluteSupremum a g} := by
      intro g hg
      change (2*Real.sqrt D+s)*b*Real.sqrt N < absoluteSupremum a g at hg
      change _ ≤ absoluteSupremum a g
      nlinarith [hmean]
    apply (measureReal_mono hsub).trans (ht.trans_eq ?_)
    congr 1
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp

/-- The literal source-scale Gaussian envelope estimate for every coefficient
feature with the printed harmonic Gram kernel.  The constant is fixed before
the dimension and before the feature itself.  This is a proved consequence of
the deterministic Gram identity and the scalar Gamma-weight estimate, rather
than an assumed sector-concentration interface. -/
theorem zonalFeature_source_scale_upper_tail (p j : ℕ) (hj : 2*j ≤ p)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N →
      ∀ (a : UnitSphere N → EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p)),
        (∀ u v : UnitSphere N,
          inner ℝ (a u) (a v) = (N : ℝ)*c*gammaWeight N p j*
            zonal N (p-2*j) (inner ℝ (u : Vector N) (v : Vector N))) →
        (SphericalAging.FiniteModel.disorderLaw N p).real
          {J | C*(N : ℝ)^(1-(j : ℝ)/2) < absoluteSupremum a (WithLp.toLp 2 J)} ≤
            Real.exp (-2*(N : ℝ)) := by
  obtain ⟨A,hA,hweight⟩ := gammaWeights_bound_all_dimensions p
  obtain ⟨K,hK,hgaussian⟩ := zonalFeature_supremum_upper_tail (p-2*j)
  refine ⟨(K+2)*(Real.sqrt (c*A)+1),by positivity,?_⟩
  intro N hN a hgram
  let : NeZero N := ⟨by omega⟩
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hpow : 0 < (N : ℝ)^j := pow_pos hNr j
  have hvar : 0 ≤ (N : ℝ)*c*gammaWeight N p j :=
    mul_nonneg (mul_nonneg hNr.le hc) (gammaWeight_pos hN p j).le
  let b := Real.sqrt ((N : ℝ)*c*gammaWeight N p j)
  have hscale : b*Real.sqrt N ≤ (Real.sqrt (c*A)+1)*(N : ℝ)^(1-(j : ℝ)/2) := by
    have hw := (le_div_iff₀ hpow).mp (hweight N hN j hj)
    have hprod : (b*Real.sqrt N*Real.sqrt ((N : ℝ)^j))^2 ≤
        (Real.sqrt (c*A)*(N : ℝ))^2 := by
      dsimp [b]
      simp only [mul_pow, Real.sq_sqrt hvar, Real.sq_sqrt hNr.le,
        Real.sq_sqrt hpow.le, Real.sq_sqrt (mul_nonneg hc hA.le)]
      have h := mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg (N : ℝ)) hc)
      nlinarith
    have hnorm : b*Real.sqrt N*Real.sqrt ((N : ℝ)^j) ≤ Real.sqrt (c*A)*(N : ℝ) := by
      nlinarith [show 0 ≤ Real.sqrt (c*A)*(N : ℝ) by positivity]
    have hdiv := (le_div_iff₀ (Real.sqrt_pos.2 hpow)).2 hnorm
    have hscale' : b*Real.sqrt N ≤ Real.sqrt (c*A)*(N : ℝ)^(1-(j : ℝ)/2) := by
      simpa only [mul_div_assoc, dimension_div_sqrt_pow (by omega : 0 < N)] using hdiv
    exact hscale'.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hNr.le _))
  obtain ⟨ha,_,htail⟩ := hgaussian hN a (show 0 ≤ b by dsimp [b]; positivity) (by
    intro u v
    dsimp [b]
    rw [Real.sq_sqrt hvar]
    exact hgram u v)
  have htail' := htail (s := 2) (by norm_num)
  have hbound : (K+2)*b*Real.sqrt N ≤
      ((K+2)*(Real.sqrt (c*A)+1))*(N : ℝ)^(1-(j : ℝ)/2) := by
    have h := mul_le_mul_of_nonneg_left hscale (show 0 ≤ K+2 by linarith)
    nlinarith
  have hsub : {g | ((K+2)*(Real.sqrt (c*A)+1))*(N : ℝ)^(1-(j : ℝ)/2) < absoluteSupremum a g} ⊆
      {g | (K+2)*b*Real.sqrt N < absoluteSupremum a g} := by
    intro g hg
    exact lt_of_le_of_lt hbound hg
  have hLcont : Continuous (fun v : Bool × UnitSphere N => innerSL ℝ (signedFeature a v)) :=
    (innerSL ℝ).continuous.comp (signedFeature_continuous a ha)
  obtain ⟨L,_,hL⟩ := exists_feature_bound _ hLcont
  have hcont : Continuous (absoluteSupremum a) := (field_supremum_lipschitz _ hL).continuous
  have hm : MeasurableSet
      {g | ((K+2)*(Real.sqrt (c*A)+1))*(N : ℝ)^(1-(j : ℝ)/2) < absoluteSupremum a g} :=
    (isOpen_lt continuous_const hcont).measurableSet
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N p →
      EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p))
      (SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N p))
      (SphericalAging.FiniteModel.disorderLaw N p) := ⟨by fun_prop,rfl⟩
  rw [hLaw.measureReal_eq hm]
  apply (measureReal_mono hsub).trans (htail'.trans_eq ?_)
  congr 1
  ring

end SlowEquilibration.SourceEntranceFullEvent
