-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerComplete
public import SlowEquilibration.LiteratureSubagBandLowerResidual
public import SlowEquilibration.LiteratureSubagBandLowerTails

/-!
Further reductions for the residual replicated-pressure limit in Subag's
Lemma 20. Fixed-temperature block lower tails suffice: Gaussian concentration
removes the logarithmic floor without a separate moment hypothesis, and
convexity transports the result to the transverse temperature.

The passage from pressure lower tails to fixed-codimension slab lower tails
is not asserted here.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagResidualReplicatedLimit

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagBandLowerComplete LiteratureSubagBandLowerResidual
open LiteratureSubagBandLowerProof LiteratureSubagBandLowerTails
open LiteratureSubagBandLowerFinal LiteratureSubagBandUpperFinal
open LiteratureSubagTheorem10Proof LiteratureSubagTheorem10Final
open scoped Topology BigOperators RealInnerProductSpace NNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem field_at_zero {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : field c J 0 = 0 := by
  unfold field blockField SphericalAging.FiniteModel.Hamiltonian
  apply Finset.sum_eq_zero
  intro p _
  have hp : 0 < p.val.val := by have := p.property; omega
  have : Nonempty (Fin p.val.val) := Fin.pos_iff_nonempty.mp hp
  simp [SphericalAging.FiniteModel.tensorMonomial, zero_pow hp.ne']

private def replicaMeasure (N k : ℕ) (ρ : ℝ) : Measure (Fin k → Vector N) :=
  (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict
    (ReplicatedBand k 0 1 ρ (0 : Vector N))

private instance (N k : ℕ) (ρ : ℝ) : IsFiniteMeasure (replicaMeasure N k ρ) :=
  inferInstanceAs (IsFiniteMeasure ((Measure.pi (fun _ : Fin k => sphereLaw N)).restrict _))

private def replicaLinear {N : ℕ} (k : ℕ) (μ : FiniteMixture) :
    (Fin k → Vector N) → EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
  fun σ => ∑ i : Fin k, sphereLinear (mixtureCoefficients μ) (σ i)

private theorem replicaLinear_measurable (N k : ℕ) (μ : FiniteMixture) :
    Measurable (replicaLinear (N := N) k μ) := by
  apply Finset.measurable_sum
  intro i _
  exact (sphereLinear_measurable _).comp (measurable_pi_apply i)

private theorem replicaLinear_bound {N : ℕ} (hN : 1 ≤ N) (k : ℕ)
    (μ : FiniteMixture) (ρ : ℝ) :
    ∀ᵐ σ ∂replicaMeasure N k ρ, ‖replicaLinear k μ σ‖ ≤
      (k : ℝ) * Real.sqrt ((N : ℝ) * μ.xi 1) := by
  have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N), ∀ i : Fin k,
      ‖sphereLinear (mixtureCoefficients μ) (σ i)‖ ≤
        Real.sqrt ((N : ℝ) * μ.xi 1) := by
    apply eventually_all.mpr
    intro i
    simpa only [covariancePolynomial_mixture] using
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => sphereLaw N)
        (i := i)).eventually
          (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ))
  filter_upwards [ha.filter_mono ae_restrict_le] with σ hσ
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hσ i).trans_eq (by simp))

private theorem replica_logPartition_eq {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β ρ : ℝ) (g : EuclideanDisorder N μ.maxDegree) :
    GaussianSpinInterpolation.logPartition (replicaMeasure N k ρ)
      (replicaLinear k μ) (β • g) =
      Real.log (replicatedBandPartition k μ β 0 1 ρ (unpackDisorder g) (0 : Vector N)) := by
  unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
  congr 1
  apply integral_congr_ae
  exact .of_forall fun σ => by
    simp only [GaussianSpinInterpolation.weight, one_mul, replicaLinear,
      _root_.sum_apply, map_smul, smul_eq_mul, sphereLinear_apply,
      field_at_zero, sub_zero, Finset.mul_sum]

private theorem finite_logPartition_lipschitz {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V) [IsFiniteMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (GaussianSpinInterpolation.logPartition ν L) := by
  by_cases hz : ν = 0
  · apply LipschitzWith.of_dist_le_mul
    intro g h
    simp only [hz, GaussianSpinInterpolation.logPartition, GaussianSpinInterpolation.moment,
      integral_zero_measure, Real.log_zero, dist_self]
    positivity
  · let : NeZero ν := ⟨hz⟩
    apply lipschitzWith_of_nnnorm_fderiv_le
      ((GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).differentiable
        (by norm_num))
    intro w
    rw [(GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
    apply (NNReal.coe_le_coe).mp
    change ‖GaussianSpinInterpolation.score ν L w‖ ≤ (K.toNNReal : ℝ)
    rw [Real.coe_toNNReal K hK]
    exact GaussianSpinInterpolation.norm_score_le ν L hL hK hb w

private theorem lipschitz_gaussian_integrable {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Integrable f (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((GaussianSpinInterpolation.gaussian_norm_integrable.const_mul (K : ℝ)).add
    (integrable_const ‖f 0‖)).mono' hf.continuous.aestronglyMeasurable
  exact .of_forall fun g => by
    have h := hf.norm_sub_le g 0
    simp only [sub_zero] at h
    calc
      ‖f g‖ ≤ ‖f g - f 0‖ + ‖f 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f g - f 0) (f 0)
      _ ≤ _ := add_le_add h le_rfl

private theorem replicaPressure_lipschitz {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β ρ : ℝ) :
    LipschitzWith (|β| * Real.sqrt ((N : ℝ) * μ.xi 1) / (N : ℝ)).toNNReal
      (fun g : EuclideanDisorder N μ.maxDegree =>
        replicatedBandPressure k μ β 0 1 ρ (unpackDisorder g) (0 : Vector N)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hf := finite_logPartition_lipschitz (replicaMeasure N k ρ) (replicaLinear k μ)
    (replicaLinear_measurable N k μ) (by positivity) (replicaLinear_bound hN k μ ρ)
  apply LipschitzWith.of_dist_le_mul
  intro g h
  have hb := hf.dist_le_mul (β • g) (β • h)
  rw [replica_logPartition_eq, replica_logPartition_eq] at hb
  rw [Real.coe_toNNReal _ (by positivity), dist_smul₀, Real.norm_eq_abs] at hb
  rw [Real.coe_toNNReal _ (by positivity)]
  unfold replicatedBandPressure
  rw [Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos (mul_pos hNr hkr)]
  apply (div_le_iff₀ (mul_pos hNr hkr)).mpr
  calc
    _ ≤ ((k : ℝ) * Real.sqrt ((N : ℝ) * μ.xi 1)) * (|β| * dist g h) := hb
    _ = _ := by field_simp

private theorem replicaPressure_integrable {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β ρ : ℝ) :
    Integrable (fun J : Disorder N μ.maxDegree =>
      replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N)) (disorderLaw N μ.maxDegree) := by
  have hi := (euclideanDisorder_hasLaw N μ.maxDegree).integrable_comp
    (lipschitz_gaussian_integrable (replicaPressure_lipschitz hN hk μ β ρ))
  simpa only [Function.comp_def, unpack_euclideanDisorder] using hi

private theorem replica_volume_positive {N k : ℕ} (hNk : k + 1 ≤ N)
    (hk : 1 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k 0 1 ρ (0 : Vector N)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
  let q : ℝ := min (ρ / 4) (1 / 2)
  have hq : q ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (by positivity) (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  have hv := SourcePureSection9SmallClosures.replicatedBand_volume_positive
    hNk hk hq zero_lt_one (show 0 < ρ / 2 by positivity)
    (canonicalBandCenter n q) (canonicalBandCenter_norm_sq n hq.1.le)
  apply hv.trans_le (measure_mono ?_)
  intro σ hσ
  refine ⟨by simp [overlap], ?_⟩
  intro i j hij
  have hh := hσ.2 i j hij
  have hqρ : q ≤ ρ / 4 := min_le_left _ _
  calc
    |overlap (σ i) (σ j) - 0| ≤ |overlap (σ i) (σ j) - q| + |q| := by
      simpa using abs_add_le (overlap (σ i) (σ j) - q) q
    _ < ρ := by rw [abs_of_pos hq.1]; linarith

private theorem replicaPartition_pos {N k : ℕ} (hNk : k + 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (J : Disorder N μ.maxDegree) :
    0 < replicatedBandPartition k μ β 0 1 ρ J (0 : Vector N) := by
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k 0 1 ρ (0 : Vector N))) := ⟨(replica_volume_positive hNk hk hρ).ne'⟩
  have hi : Integrable (fun x : Vector N =>
      Real.exp (β * field (mixtureCoefficients μ) J x)) (sphereLaw N) :=
    partitionAgainst_integrable (sphereLaw N) (sphereLaw_support (by omega)) β
      (field_contDiff _ J).continuous
  have hp := Integrable.fintype_prod (fun _ : Fin k => hi)
  apply integral_exp_pos
  convert hp.restrict using 1
  ext σ
  simp only [field_at_zero, sub_zero, Finset.mul_sum, Real.exp_sum]

private theorem onePartition_eq {N : ℕ} (μ : FiniteMixture) (β ρ : ℝ)
    (J : Disorder N μ.maxDegree) :
    replicatedBandPartition 1 μ β 0 1 ρ J (0 : Vector N) = mixturePartition μ β J := by
  have hB : ReplicatedBand 1 0 1 ρ (0 : Vector N) = univ := by
    ext σ
    simp [ReplicatedBand, overlap]
  unfold replicatedBandPartition
  rw [hB, setIntegral_univ]
  simp only [field_at_zero, sub_zero, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin 1) (x : Vector N) =>
    Real.exp (β * field (mixtureCoefficients μ) J x))]
  simp [mixturePartition, partition, fieldOfMixture]

private theorem onePressure_eq {N : ℕ} (μ : FiniteMixture) (β ρ : ℝ)
    (J : Disorder N μ.maxDegree) :
    replicatedBandPressure 1 μ β 0 1 ρ J (0 : Vector N) =
      Real.log (mixturePartition μ β J) / (N : ℝ) := by
  simp [replicatedBandPressure, onePartition_eq]

private theorem oneExpectedPressure_eq (N : ℕ) (μ : FiniteMixture) (β ρ : ℝ) :
    expectedReplicatedBandPressure 1 μ β 0 1 ρ (0 : Vector N) =
      quenchedPressure N μ β := by
  simp only [expectedReplicatedBandPressure, onePressure_eq, integral_div]
  rfl

private theorem replicaPressure_le_full {N k : ℕ} (hNk : k + 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (J : Disorder N μ.maxDegree) :
    replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N) ≤
      Real.log (mixturePartition μ β J) / (N : ℝ) := by
  have hpart := replicatedBandPartition_mul_le_pow (by omega : 1 ≤ N) 1 k
    μ β 0 1 ρ J (0 : Vector N)
  simp only [one_mul, onePartition_eq] at hpart
  have hl := Real.log_le_log (replicaPartition_pos hNk hk μ β hρ J) hpart
  rw [Real.log_pow] at hl
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  unfold replicatedBandPressure
  apply (div_le_iff₀ (mul_pos hNr hkr)).mpr
  calc
    _ ≤ (k : ℝ) * Real.log (mixturePartition μ β J) := hl
    _ = _ := by field_simp

private theorem replicaExpectedPressure_le_full {N k : ℕ} (hNk : k + 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N) ≤
      quenchedPressure N μ β := by
  have hN : 1 ≤ N := by omega
  have h := integral_mono (replicaPressure_integrable hN hk μ β ρ)
    ((sphericalLogPartition_integrable hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β).div_const (N : ℝ))
    (replicaPressure_le_full hNk hk μ β hρ)
  change (∫ J, replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N)
    ∂disorderLaw N μ.maxDegree) ≤
    (∫ J, Real.log (partition N β (field (mixtureCoefficients μ) J))
      ∂disorderLaw N μ.maxDegree) / (N : ℝ)
  simpa only [integral_div] using h

/-- The fixed-count zero-center pressure concentrates around its true mean.
The Lipschitz constant tends to zero even without taking the replica count
to infinity or the overlap tolerance to zero. -/
theorem zero_replica_deviation_tendsto (k : ℕ) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β ρ : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => (disorderLaw N μ.maxDegree).real
      {J | t < |replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N) -
        expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N)|})
      atTop (𝓝 0) := by
  have hxi : 0 < μ.xi 1 := μ.xi_pos zero_lt_one
  let c : ℝ := t ^ 2 / (2 * (|β| + 1) ^ 2 * μ.xi 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim : Tendsto (fun N : ℕ => 2 * Real.exp (-c * (N : ℝ))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    simpa only [mul_zero, neg_mul, Function.comp_def] using hh.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ => measureReal_nonneg)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  let L : ℝ := (|β| + 1) * Real.sqrt ((N : ℝ) * μ.xi 1) / (N : ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  let F := fun g : EuclideanDisorder N μ.maxDegree =>
    replicatedBandPressure k μ β 0 1 ρ (unpackDisorder g) (0 : Vector N)
  have hLip : LipschitzWith L.toNNReal F :=
    (replicaPressure_lipschitz hN hk μ β ρ).weaken
      (Real.toNNReal_mono (by dsimp [L]; gcongr; linarith [abs_nonneg β]))
  have hlaw := euclideanDisorder_hasLaw N μ.maxDegree
  have hmean : expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N) =
      ∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) :=
    hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have hg := SYK.euclidean_lipschitz_gaussian_concentration F L t hL ht hLip
  have hset : MeasurableSet {g : EuclideanDisorder N μ.maxDegree |
      t < |F g - ∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate N μ.maxDegree)|} :=
    (isOpen_lt continuous_const (hLip.continuous.sub continuous_const).abs).measurableSet
  nth_rw 1 [← hlaw.map_eq] at hg
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at hg
  rw [← hmean] at hg
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  have he : -t ^ 2 / (2 * L ^ 2) = -c * (N : ℝ) := by
    dsimp [L, c]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [he] at hr
  simpa only [Set.preimage_ofPred_eq, F, unpack_euclideanDisorder, measureReal_def] using hr

private theorem zero_mean_eventually_lower (k : ℕ) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β ρ : ℝ)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, quenchedPressure N μ β - ε ≤
      expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N) := by
  let t := ε / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := (htail t ht).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hd := (zero_replica_deviation_tendsto k hk μ β ρ ht).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hp : Tendsto (fun N => (disorderLaw N μ.maxDegree).real
      {J | t < |Real.log (mixturePartition μ β J) / (N : ℝ) - quenchedPressure N μ β|})
      atTop (𝓝 0) := by
    simpa only [onePressure_eq, oneExpectedPressure_eq] using
      zero_replica_deviation_tendsto 1 (by omega) μ β ρ ht
  have hp' := hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hb, hd, hp', eventually_ge_atTop (1 : ℕ)] with N hb hd hp hN
  let ν := disorderLaw N μ.maxDegree
  let A : Set (Disorder N μ.maxDegree) :=
    {J | conditionalBlockProbability N k μ β 0 ρ J < Real.exp (-t * (N : ℝ))}
  let B : Set (Disorder N μ.maxDegree) :=
    {J | t < |Real.log (mixturePartition μ β J) / (N : ℝ) - quenchedPressure N μ β|}
  let C : Set (Disorder N μ.maxDegree) :=
    {J | t < |replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N) -
      expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N)|}
  have hsmall : ν.real (A ∪ B ∪ C) < 1 := by
    have h := measureReal_union_le (μ := ν) (A ∪ B) C
    have h' := measureReal_union_le (μ := ν) A B
    have hA : ν.real A < 1 / 4 := hb
    have hB : ν.real B < 1 / 4 := hp
    have hC : ν.real C < 1 / 4 := hd
    linarith
  obtain ⟨J, hJ⟩ : ∃ J, J ∉ A ∪ B ∪ C := by
    by_contra hh
    have he : A ∪ B ∪ C = univ := by
      apply eq_univ_of_forall
      intro J
      by_contra hnot
      exact hh ⟨J, hnot⟩
    rw [he, probReal_univ] at hsmall
    exact (lt_irrefl (1 : ℝ)) hsmall
  have hA : Real.exp (-t * (N : ℝ)) ≤ conditionalBlockProbability N k μ β 0 ρ J :=
    le_of_not_gt (fun hh => hJ (Or.inl (Or.inl hh)))
  have hB : |Real.log (mixturePartition μ β J) / (N : ℝ) - quenchedPressure N μ β| ≤ t :=
    le_of_not_gt (fun hh => hJ (Or.inl (Or.inr hh)))
  have hC : |replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N) -
      expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N)| ≤ t :=
    le_of_not_gt (fun hh => hJ (Or.inr hh))
  have hpos : 0 < conditionalBlockProbability N k μ β 0 ρ J :=
    (Real.exp_pos _).trans_le hA
  have hl := Real.log_le_log (Real.exp_pos _) hA
  rw [Real.log_exp] at hl
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hu : -t ≤ untruncatedBlockLog N k μ β 0 ρ J :=
    (le_div_iff₀ hNr).mpr hl
  have hu' : -t ≤ untruncatedBlockLog N k μ β 0 ρ J / (k : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < k)).mpr
    nlinarith
  have he := replicatedBandPressure_zero_eq hN hk μ β ρ J hpos
  rw [field_at_zero, mul_zero, zero_div, sub_zero] at he
  have hlo := (abs_le.mp hB).1
  have hhi := (abs_le.mp hC).2
  dsimp [t] at *
  linarith

/-- At fixed temperature, actual block lower tails imply convergence of the
untruncated replicated pressure. No block-log moment estimate is needed. -/
theorem zero_expectedPressure_tendsto_of_blockLowerTails
    (k : ℕ) (hk : 1 ≤ k) (μ : FiniteMixture) (β : ℝ) {ρ F : ℝ} (hρ : 0 < ρ)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0))
    (hpressure : Tendsto (fun N => quenchedPressure N μ β) atTop (𝓝 F)) :
    Tendsto (fun N => expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N))
      atTop (𝓝 F) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : 0 < (F - a) / 2 := by linarith
    filter_upwards [zero_mean_eventually_lower k hk μ β ρ htail he,
      hpressure.eventually (lt_mem_nhds (show a + (F - a) / 2 < F by linarith))]
      with N hN hp
    linarith
  · intro a ha
    filter_upwards [hpressure.eventually (gt_mem_nhds ha),
      eventually_ge_atTop (k + 1)] with N hp hN
    exact (replicaExpectedPressure_le_full hN hk μ β hρ).trans_lt hp

private theorem convex_scale_lower {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (h0 : f 0 ≤ 0) {s : ℝ} (hs : 1 ≤ s) :
    s * f 1 ≤ f s := by
  have hsp : 0 < s := zero_lt_one.trans_le hs
  have ha : 0 ≤ 1 / s := (one_div_pos.mpr hsp).le
  have hb : 0 ≤ 1 - 1 / s := sub_nonneg.mpr ((div_le_one hsp).mpr hs)
  have h := hf.2 (mem_univ s) (mem_univ 0) ha hb (by ring)
  have he : (1 / s : ℝ) • s + (1 - 1 / s) • (0 : ℝ) = 1 := by
    simp [smul_eq_mul, hsp.ne']
  rw [he] at h
  simp only [smul_eq_mul] at h
  have hz : (1 - 1 / s) * f 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb h0
  have hl : f 1 ≤ (1 / s) * f s := by linarith
  calc
    s * f 1 ≤ s * ((1 / s) * f s) := mul_le_mul_of_nonneg_left hl hsp.le
    _ = f s := by field_simp

private theorem replicaPressure_scale_lower {N k : ℕ} (hNk : k + 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β : ℝ) {ρ s : ℝ} (hρ : 0 < ρ) (hs : 1 ≤ s)
    (J : Disorder N μ.maxDegree) :
    s * replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N) ≤
      replicatedBandPressure k μ (β * s) 0 1 ρ J (0 : Vector N) := by
  let ν := replicaMeasure N k ρ
  have hvol := replica_volume_positive hNk hk hρ
  have hν : ν ≠ 0 := by
    intro hz
    have h := congrArg (fun m : Measure (Fin k → Vector N) => m univ) hz
    have hzero : (Measure.pi (fun _ : Fin k => sphereLaw N))
        (ReplicatedBand k 0 1 ρ (0 : Vector N)) = 0 := by
      simpa [ν, replicaMeasure] using h
    exact hvol.ne' hzero
  let : NeZero ν := ⟨hν⟩
  let L := replicaLinear (N := N) k μ
  have hL := replicaLinear_measurable N k μ
  have hb := replicaLinear_bound (by omega : 1 ≤ N) k μ ρ
  have hf : ConvexOn ℝ univ (fun t : ℝ =>
      GaussianSpinInterpolation.logPartition ν L (t • (β • euclideanDisorder J))) := by
    simpa only [zero_add] using GaussianSpinInterpolation.logPartition_line_convex
      ν L hL (by positivity : 0 ≤ (k : ℝ) * Real.sqrt ((N : ℝ) * μ.xi 1)) hb
      0 (β • euclideanDisorder J)
  have h0 : GaussianSpinInterpolation.logPartition ν L ((0 : ℝ) • (β • euclideanDisorder J)) ≤ 0 := by
    have hmass : ν.real univ ≤ 1 := by
      change ((Measure.pi (fun _ : Fin k => sphereLaw N)).restrict _).real univ ≤ 1
      simpa only [Measure.real, Measure.restrict_apply_univ] using
        (measureReal_le_one (μ := Measure.pi (fun _ : Fin k => sphereLaw N))
          (s := ReplicatedBand k 0 1 ρ (0 : Vector N)))
    simpa [GaussianSpinInterpolation.logPartition, GaussianSpinInterpolation.moment,
      GaussianSpinInterpolation.weight] using
      Real.log_nonpos (measureReal_nonneg (μ := ν) (s := univ)) hmass
  have h := convex_scale_lower hf h0 hs
  simp only [smul_smul, one_mul, mul_comm s β, replica_logPartition_eq,
    unpack_euclideanDisorder, ν, L] at h
  have hd := div_le_div_of_nonneg_right h
    (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg k))
  simpa only [replicatedBandPressure, mul_div_assoc] using hd

/-- The transverse temperature needs no new block-tail estimate: convexity
of the literal restricted partition gives the required one-sided scaling. -/
theorem zero_expectedPressure_scale_lower {N k : ℕ} (hNk : k + 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β : ℝ) {ρ s : ℝ} (hρ : 0 < ρ) (hs : 1 ≤ s) :
    s * expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N) ≤
      expectedReplicatedBandPressure k μ (β * s) 0 1 ρ (0 : Vector N) := by
  have h := integral_mono ((replicaPressure_integrable (by omega) hk μ β ρ).const_mul s)
    (replicaPressure_integrable (by omega) hk μ (β * s) ρ)
    (replicaPressure_scale_lower hNk hk μ β hρ hs)
  simpa only [integral_const_mul, expectedReplicatedBandPressure] using h

/-- A fixed-temperature replicated limit transports to the exact ambient
normalization and transverse temperature in `ResidualReplicatedLimit`. -/
theorem residualReplicatedPressure_tendsto_of_fixedTemperature
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hfixed : Tendsto (fun n => expectedReplicatedBandPressure k
      (physicalResidualMixture μ q hq) β 0 1 ρ (0 : Vector n))
        atTop (𝓝 (D.residual q))) :
    Tendsto (fun n => residualReplicatedPressure μ β q ρ hq k n)
      atTop (𝓝 (D.residual q)) := by
  let ν := physicalResidualMixture μ q hq
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hscale : Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 1) := by
    have h := dimensionCorrectedTemperature_tendsto (1 : ℝ) 1
    change Tendsto (fun n : ℕ => (1 : ℝ) * Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 1) at h
    simpa only [one_mul] using h
  have hlo := (hratio.mul hscale).mul hfixed
  simp only [one_mul] at hlo
  have hhi := quenchedPressure_tendsto_dimensionCorrected_per_ambient_all_real ν 1
    (D.residual_limit q hq)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hs : 1 ≤ Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      apply Real.one_le_sqrt.mpr
      rw [le_div_iff₀ hnr]
      push_cast
      linarith
    have h := zero_expectedPressure_scale_lower hn hk ν β hρ hs
    simpa only [residualReplicatedPressure, ν, mul_assoc] using
      mul_le_mul_of_nonneg_left h (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact mul_le_mul_of_nonneg_left
      (replicaExpectedPressure_le_full hn hk ν _ hρ)
      (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))

/-- The full residual limit reduces to actual block lower tails at the
fixed original temperature, with no second-moment or varying-temperature
hypothesis. The unresolved block-tail input is stated explicitly. -/
theorem residualReplicatedLimit_of_blockLowerTails
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (htail : ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1,
      ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k
          (physicalResidualMixture μ q hq) β 0 ρ ε) atTop (𝓝 0)) :
    ResidualReplicatedLimit D := by
  intro q hq ρ hρ k hk
  apply residualReplicatedPressure_tendsto_of_fixedTemperature D hq k hk hρ
  exact zero_expectedPressure_tendsto_of_blockLowerTails k hk _ β hρ
    (htail q hq k hk ρ hρ) (D.residual_limit q hq)

/-- Fixed-temperature uniform slab tails for the physical residual mixtures
are sufficient for the exact residual replicated limit. -/
theorem residualReplicatedLimit_of_uniformSlabLowerTails
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hslab : ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1,
      UniformSlabLowerTails (physicalResidualMixture μ q hq) β) :
    ResidualReplicatedLimit D := by
  apply residualReplicatedLimit_of_blockLowerTails D
  intro q hq k hk ρ hρ ε hε
  apply zero_blockLowerTail_tendsto_of_uniformSlabs hk _ β ρ
  · intro j hj t ht
    obtain ⟨c, hc, hbound⟩ := hslab q hq j ρ t hρ ht
    have hexp : Tendsto (fun N : ℕ => Real.exp (-c * (N : ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (.of_forall fun _ => measureReal_nonneg) hbound
  · exact hε

/-- The one-replica instance of the target is unconditional at supplied
physical thermodynamic data. -/
theorem residualReplicatedPressure_one_tendsto
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n => residualReplicatedPressure μ β q ρ hq 1 n)
      atTop (𝓝 (D.residual q)) := by
  apply residualReplicatedPressure_tendsto_of_fixedTemperature D hq 1 (by omega) hρ
  simpa only [oneExpectedPressure_eq] using D.residual_limit q hq

private theorem uniformSlabLowerTail_tendsto_of_partitionLowerTails
    (μ : FiniteMixture) (β : ℝ) (j : ℕ)
    (hfixed : ∀ η t c : ℝ, 0 < η → 0 < t → 0 < c →
      ∀ᶠ N : ℕ in atTop, ∀ σ : Fin j → Vector N,
        (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
          (disorderLaw N μ.maxDegree).real
            (fixedSlabPartitionLowerTailEvent μ β η t σ) ≤ Real.exp (-c * (N : ℝ)))
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    Tendsto (fun N => uniformSlabLowerTailProbability N j μ β ρ t) atTop (𝓝 0) := by
  let a : ℝ := 1 + (j : ℝ) * Real.log (1 + 2 / (ρ / 2))
  have ha : 0 < a := by
    have hl : 0 ≤ Real.log (1 + 2 / (ρ / 2)) := by
      apply Real.log_nonneg
      have : 0 < 2 / (ρ / 2) := by positivity
      linarith
    dsimp [a]
    positivity
  have hupper : Tendsto (fun N => (disorderLaw N μ.maxDegree).real
      (pressureUpperTailEvent N μ β (t / 2))) atTop (𝓝 0) := by
    have hd := zero_replica_deviation_tendsto 1 (by omega) μ β ρ
      (show 0 < t / 2 by positivity)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd
      (.of_forall fun _ => measureReal_nonneg)
    exact .of_forall fun N => measureReal_mono (h₂ := measure_ne_top _ _) (by
      intro J hJ
      change t / 2 < |replicatedBandPressure 1 μ β 0 1 ρ J (0 : Vector N) -
        expectedReplicatedBandPressure 1 μ β 0 1 ρ (0 : Vector N)|
      rw [onePressure_eq, oneExpectedPressure_eq]
      have hh : quenchedPressure N μ β + t / 2 <
          Real.log (mixturePartition μ β J) / (N : ℝ) := hJ
      linarith [le_abs_self (Real.log (mixturePartition μ β J) / (N : ℝ) -
        quenchedPressure N μ β)])
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsum := hupper.add hexp
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (.of_forall fun _ => measureReal_nonneg)
  filter_upwards [hfixed (ρ / 2) (t / 2) a (by positivity) (by positivity) ha,
    eventually_ge_atTop (1 : ℕ)] with N hpoint hN
  simpa only [neg_one_mul, uniformSlabLowerTailProbability] using
    uniformSlabLowerTailProbability_le_exp_add_pressureUpper hN μ β t 1
      (show 0 < ρ / 2 by positivity) (by linarith : ρ / 2 + ρ / 2 ≤ ρ) hpoint

/-- The remaining analytic bridge can be stated entirely for unnormalized
fixed slabs. The existing frame nets and sequential-replica argument then
give the full residual limit, including its transverse correction. -/
theorem residualReplicatedLimit_of_fixedSlabPartitionLowerTails
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hfixed : ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1,
      ∀ j : ℕ, ∀ η t c : ℝ, 0 < η → 0 < t → 0 < c →
        ∀ᶠ N : ℕ in atTop, ∀ σ : Fin j → Vector N,
          (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
            (disorderLaw N (physicalResidualMixture μ q hq).maxDegree).real
              (fixedSlabPartitionLowerTailEvent (physicalResidualMixture μ q hq)
                β η t σ) ≤ Real.exp (-c * (N : ℝ))) :
    ResidualReplicatedLimit D := by
  apply residualReplicatedLimit_of_blockLowerTails D
  intro q hq k hk ρ hρ ε hε
  apply zero_blockLowerTail_tendsto_of_uniformSlabs hk _ β ρ
  · intro j hj t ht
    exact uniformSlabLowerTail_tendsto_of_partitionLowerTails _ β j
      (hfixed q hq j) hρ ht
  · exact hε

private theorem fixedSlabPartitionLowerTails_of_orthonormal
    (μ : FiniteMixture) (β : ℝ)
    (hframe : ∀ r : ℕ, ∀ η t c : ℝ, 0 < η → 0 < t → 0 < c →
      ∀ᶠ N : ℕ in atTop, ∀ e : Fin r → Vector N, Orthonormal ℝ e →
        (disorderLaw N μ.maxDegree).real
          (fixedSlabPartitionLowerTailEvent μ β η t
            (fun i => Real.sqrt (N : ℝ) • e i)) ≤ Real.exp (-c * (N : ℝ)))
    (j : ℕ) (η t c : ℝ) (hη : 0 < η) (ht : 0 < t) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : Fin j → Vector N,
      (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
        (disorderLaw N μ.maxDegree).real
          (fixedSlabPartitionLowerTailEvent μ β η t σ) ≤ Real.exp (-c * (N : ℝ)) := by
  let θ := η / (Real.sqrt (j : ℝ) + 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hfinite : ∀ᶠ N : ℕ in atTop, ∀ r : Fin (j + 1), ∀ e : Fin r.val → Vector N,
      Orthonormal ℝ e → (disorderLaw N μ.maxDegree).real
        (fixedSlabPartitionLowerTailEvent μ β θ t
          (fun i => Real.sqrt (N : ℝ) • e i)) ≤ Real.exp (-c * (N : ℝ)) :=
    eventually_all.mpr fun r => hframe r.val θ t c hθ ht hc
  filter_upwards [hfinite, eventually_ge_atTop (1 : ℕ)] with N hpoint hN
  intro σ hσ
  obtain ⟨r, hr, e, he, a, hrep, ha⟩ :=
    exists_spherical_frame_coordinates (by omega : 0 < N) σ hσ
  have hwidth : Real.sqrt (r : ℝ) * θ < η := by
    have hm : Real.sqrt (r : ℝ) ≤ Real.sqrt (j : ℝ) :=
      Real.sqrt_le_sqrt (Nat.cast_le.mpr hr)
    have hθeq : (Real.sqrt (j : ℝ) + 1) * θ = η := by
      dsimp [θ]
      field_simp
    exact (mul_le_mul_of_nonneg_right hm hθ.le).trans_lt (by nlinarith)
  have hsub : {y : Vector N | ∀ i, |overlap y (Real.sqrt (N : ℝ) • e i)| < θ} ⊆
      {y : Vector N | ∀ i, |overlap y (σ i)| < η} := by
    intro y hy
    exact slab_subset_of_frame_coordinates σ _ a hrep ha hθ.le hwidth y
      (fun i => (hy i).le)
  have hpart (J : Disorder N μ.maxDegree) :
      fixedSlabPartition μ β θ J (fun i => Real.sqrt (N : ℝ) • e i) ≤
        fixedSlabPartition μ β η J σ := by
    unfold fixedSlabPartition partitionOn
    exact setIntegral_mono_set
      (partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β
        (fieldOfMixture_contDiff μ J).continuous).restrict
      (.of_forall fun _ => (Real.exp_pos _).le) (.of_forall fun _ h => hsub h)
  have hevent : fixedSlabPartitionLowerTailEvent μ β η t σ ⊆
      fixedSlabPartitionLowerTailEvent μ β θ t (fun i => Real.sqrt (N : ℝ) • e i) := by
    intro J hJ
    exact lt_of_le_of_lt (hpart J) hJ
  exact (measureReal_mono hevent (measure_ne_top _ _)).trans
    (hpoint ⟨r, by omega⟩ e he)

/-- It suffices to prove the unnormalized slab lower tail for orthonormal
frames, the fixed-codimension comparison used in the published argument. -/
theorem residualReplicatedLimit_of_orthonormalSlabPartitionLowerTails
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (hframe : ∀ q : ℝ, ∀ hq : q ∈ Ioo (0 : ℝ) 1,
      ∀ r : ℕ, ∀ η t c : ℝ, 0 < η → 0 < t → 0 < c →
        ∀ᶠ N : ℕ in atTop, ∀ e : Fin r → Vector N, Orthonormal ℝ e →
          (disorderLaw N (physicalResidualMixture μ q hq).maxDegree).real
            (fixedSlabPartitionLowerTailEvent (physicalResidualMixture μ q hq)
              β η t (fun i => Real.sqrt (N : ℝ) • e i)) ≤ Real.exp (-c * (N : ℝ))) :
    ResidualReplicatedLimit D := by
  apply residualReplicatedLimit_of_fixedSlabPartitionLowerTails D
  intro q hq
  exact fixedSlabPartitionLowerTails_of_orthonormal _ β (hframe q hq)

end SlowEquilibration.LiteratureSubagResidualReplicatedLimit
