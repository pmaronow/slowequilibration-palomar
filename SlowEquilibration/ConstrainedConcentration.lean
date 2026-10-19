-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConcentration
public import SlowEquilibration.MixtureThresholds

/-!
# Constrained, shifted free-energy concentration

All observables below use the original finite Gaussian tensor disorder law.
The reference spatial measure may be any finite nonzero measure carried by
the actual sphere. Deterministic domains and bounded measurable shifts are
constructed as a restricted, reweighted sphere measure.
-/

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The ordinary partition integral against a finite spatial measure. -/
def partitionAgainst {N : ℕ} (ν : Measure (Vector N)) (β : ℝ) (H : Vector N → ℝ) : ℝ :=
  ∫ x, Real.exp (β*H x) ∂ν

theorem integrable_of_sphere_support {N : ℕ} (ν : Measure (Vector N)) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ)) {f : Vector N → ℝ} (hf : Continuous f) :
    Integrable f ν := by
  have hball : ∀ᵐ x ∂ν, x ∈ Metric.closedBall (0:Vector N) (Real.sqrt N) := by
    filter_upwards [hsupport] with x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N:ℝ), norm_nonneg x]
  have hi := hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:Vector N) (Real.sqrt N)) (μ := ν)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hball] using hi

theorem partitionAgainst_integrable {N : ℕ} (ν : Measure (Vector N)) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ)) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (fun x => Real.exp (β*H x)) ν :=
  integrable_of_sphere_support ν hsupport (Real.continuous_exp.comp (continuous_const.mul hH))

theorem partitionAgainst_pos {N : ℕ} (ν : Measure (Vector N))
    [IsFiniteMeasure ν] [NeZero ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ)) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    0 < partitionAgainst ν β H :=
  integral_exp_pos (partitionAgainst_integrable ν hsupport β hH)

/-- The deterministic domain and shift do not affect the sharp disorder
Lipschitz constant, because the actual field comparison is uniform on the sphere. -/
theorem partitionAgainst_euclidean_comparison {N P : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ))
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β)
    (g h : EuclideanDisorder N P) :
    partitionAgainst ν β (field c (unpackDisorder g)) ≤
      Real.exp (β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h)*
        partitionAgainst ν β (field c (unpackDisorder h)) := by
  have hg := partitionAgainst_integrable ν hsupport β (field_contDiff c (unpackDisorder g)).continuous
  have hh := partitionAgainst_integrable ν hsupport β (field_contDiff c (unpackDisorder h)).continuous
  have hb : (fun x : Vector N => Real.exp (β*field c (unpackDisorder g) x)) ≤ᵐ[ν]
      fun x => Real.exp (β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h)*
        Real.exp (β*field c (unpackDisorder h) x) := by
    filter_upwards [hsupport] with x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hf := field_euclidean_difference_bound hN c hc g h x hx
    have hm := mul_le_mul_of_nonneg_left
      ((le_abs_self (field c (unpackDisorder g) x-field c (unpackDisorder h) x)).trans hf) hβ
    linarith
  have hi := integral_mono_ae hg (hh.const_mul _) hb
  simpa only [integral_const_mul, partitionAgainst] using hi

def logPartitionAgainstEuclidean {N P : ℕ} (ν : Measure (Vector N)) (c : Degree P → ℝ)
    (β : ℝ) (g : EuclideanDisorder N P) : ℝ :=
  Real.log (partitionAgainst ν β (field c (unpackDisorder g)))

theorem logPartitionAgainstEuclidean_sub_le {N P : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν] [NeZero ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ))
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β)
    (g h : EuclideanDisorder N P) :
    logPartitionAgainstEuclidean ν c β g-logPartitionAgainstEuclidean ν c β h ≤
      β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)*dist g h := by
  have hZg := partitionAgainst_pos ν hsupport β (field_contDiff c (unpackDisorder g)).continuous
  have hZh := partitionAgainst_pos ν hsupport β (field_contDiff c (unpackDisorder h)).continuous
  have hz := Real.log_le_log hZg (partitionAgainst_euclidean_comparison hN ν hsupport c hc hβ g h)
  rw [Real.log_mul (Real.exp_pos _).ne' hZh.ne', Real.log_exp] at hz
  unfold logPartitionAgainstEuclidean
  linarith

theorem logPartitionAgainstEuclidean_lipschitz {N P : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν] [NeZero ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ))
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β) :
    LipschitzWith (β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)).toNNReal
      (logPartitionAgainstEuclidean (N := N) ν c β) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hβ (Real.sqrt_nonneg _))]
  apply abs_le.mpr
  refine ⟨?_, logPartitionAgainstEuclidean_sub_le hN ν hsupport c hc hβ g h⟩
  have hh := logPartitionAgainstEuclidean_sub_le hN ν hsupport c hc hβ h g
  rw [dist_comm h g] at hh
  linarith

/-- Closed two-sided Gaussian deviation, obtained directly from the
sub-Gaussian MGF's non-strict Chernoff inequalities. -/
theorem euclidean_lipschitz_gaussian_closed_tail {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s)
    (hLip : LipschitzWith L.toNNReal F) :
    SYK.standardGaussianMeasureOnEuclidean ι
      {g | s ≤ |F g-(∫ h, F h ∂SYK.standardGaussianMeasureOnEuclidean ι)|} ≤
      ENNReal.ofReal (2*Real.exp (-s^2/(2*L^2))) := by
  let γ := SYK.standardGaussianMeasureOnEuclidean ι
  have hsg := SYK.product_standardGaussian_hasSubgaussianMGF F L hL hLip
  have hu := hsg.measure_ge_le hs
  have hl := hsg.neg.measure_ge_le hs
  simp only [Real.coe_toNNReal _ (sq_nonneg L)] at hu hl
  have hset : {g | s ≤ |F g-(∫ h, F h ∂γ)|} =
      {g | s ≤ F g-(∫ h, F h ∂γ)} ∪ {g | s ≤ -(F g-(∫ h, F h ∂γ))} := by
    ext g
    simp only [Set.mem_union, Set.mem_ofPred_eq, abs_eq_max_neg, le_max_iff]
  have hreal : γ.real {g | s ≤ |F g-(∫ h, F h ∂γ)|} ≤ 2*Real.exp (-s^2/(2*L^2)) := by
    rw [hset]
    have h := (measureReal_union_le (μ := γ) _ _).trans (add_le_add hu hl)
    simpa only [Pi.neg_apply, two_mul] using h
  rw [← ENNReal.ofReal_toReal (measure_ne_top γ _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Integrability of a Lipschitz observable follows from the same genuine
Gaussian MGF theorem used for concentration. -/
theorem euclidean_lipschitz_integrable {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℝ ι → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : LipschitzWith L.toNNReal F) :
    Integrable F (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hsg := SYK.product_standardGaussian_hasSubgaussianMGF F L hL hLip
  have h := hsg.integrable.add (integrable_const
    (∫ h, F h ∂SYK.standardGaussianMeasureOnEuclidean ι))
  convert h using 1
  funext g
  change F g = F g-(∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean ι)+
    (∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean ι)
  ring

/-- The log partition is integrable under the literal finite tensor law
for every finite nonzero deterministic spatial measure carried by the sphere. -/
theorem logPartitionAgainst_disorder_integrable {N P : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν] [NeZero ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ))
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β : ℝ} (hβ : 0 < β) :
    Integrable (fun J : Disorder N P => Real.log (partitionAgainst ν β (field c J)))
      (disorderLaw N P) := by
  let F := logPartitionAgainstEuclidean (N := N) ν c β
  let L : ℝ := β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hL : 0 < L := mul_pos hβ (Real.sqrt_pos.mpr (mul_pos hNr hcov))
  have hLip : LipschitzWith L.toNNReal F := logPartitionAgainstEuclidean_lipschitz hN ν hsupport c hc hβ.le
  have h := (euclideanDisorder_hasLaw N P).integrable_comp (euclidean_lipschitz_integrable F L hL hLip)
  simpa only [Function.comp_def, F, logPartitionAgainstEuclidean, unpack_euclideanDisorder] using h

/-- Closed two-sided deviation for the literal tensor disorder, with the
sharp Gaussian constant, for any fixed finite nonzero sphere-supported law. -/
theorem logPartitionAgainst_closed_concentration {N P : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν] [NeZero ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ))
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β s : ℝ} (hβ : 0 < β) (hs : 0 ≤ s) :
    disorderLaw N P {J | s ≤ |Real.log (partitionAgainst ν β (field c J))-
        (∫ K, Real.log (partitionAgainst ν β (field c K)) ∂disorderLaw N P)|} ≤
      ENNReal.ofReal (2*Real.exp (-s^2/(2*β^2*(N:ℝ)*covariancePolynomial c 1))) := by
  let F := logPartitionAgainstEuclidean (N := N) ν c β
  let L : ℝ := β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hL : 0 < L := mul_pos hβ (Real.sqrt_pos.mpr (mul_pos hNr hcov))
  have hLip : LipschitzWith L.toNNReal F := logPartitionAgainstEuclidean_lipschitz hN ν hsupport c hc hβ.le
  have hlaw := euclideanDisorder_hasLaw N P
  have hmean : (∫ J : Disorder N P, Real.log (partitionAgainst ν β (field c J)) ∂disorderLaw N P)=
      ∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P) :=
    hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have h := euclidean_lipschitz_gaussian_closed_tail F L s hL hs hLip
  have hset : MeasurableSet {g : EuclideanDisorder N P |
      s ≤ |F g-(∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P))|} :=
    measurableSet_le measurable_const (hLip.continuous.sub continuous_const).abs.measurable
  nth_rw 1 [← hlaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at h
  have hLsquared : L^2=β^2*(N:ℝ)*covariancePolynomial c 1 := by
    dsimp only [L]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hcov.le)]
    ring
  rw [hmean]
  simpa only [Set.preimage_ofPred_eq, F, logPartitionAgainstEuclidean,
    unpack_euclideanDisorder, hLsquared, mul_assoc] using h

/-- The exact closed tN tail in `lem:pre-concentration`, for general
finite nonzero deterministic sphere-supported spatial measures. -/
theorem logPartitionAgainst_pressure_concentration {N P : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsFiniteMeasure ν] [NeZero ν]
    (hsupport : ∀ᵐ x ∂ν, ‖x‖^2=(N:ℝ))
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    disorderLaw N P {J | t*(N:ℝ) ≤ |Real.log (partitionAgainst ν β (field c J))-
        (∫ K, Real.log (partitionAgainst ν β (field c K)) ∂disorderLaw N P)|} ≤
      ENNReal.ofReal (2*Real.exp (-(t^2*(N:ℝ))/(2*β^2*covariancePolynomial c 1))) := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h := logPartitionAgainst_closed_concentration hN ν hsupport c hc hcov hβ
    (s := t*(N:ℝ)) (mul_nonneg ht.le hNr.le)
  have hexp : -(t*(N:ℝ))^2/(2*β^2*(N:ℝ)*covariancePolynomial c 1) =
      -(t^2*(N:ℝ))/(2*β^2*covariancePolynomial c 1) := by
    field_simp
  rwa [hexp] at h

/-- Deterministic Borel domains and shifts are encoded by the actual
restricted sphere law with density exp h. -/
def domainShiftLaw (N : ℕ) (B : Set (Vector N)) (h : Vector N → ℝ) : Measure (Vector N) :=
  ((sphereLaw N).restrict B).withDensity (fun x => ENNReal.ofReal (Real.exp (h x)))

/-- Finiteness is proved from the bounded measurable shift, rather than
assumed as part of a replacement spatial law. -/
theorem domainShiftLaw_isFinite (N : ℕ) (B : Set (Vector N)) (h : Vector N → ℝ)
    (hMeas : Measurable h) (C : ℝ)
    (hBound : ∀ᵐ x ∂(sphereLaw N).restrict B, |h x| ≤ C) :
    IsFiniteMeasure (domainShiftLaw N B h) := by
  have hi : Integrable (fun x => Real.exp (h x)) ((sphereLaw N).restrict B) := by
    apply (integrable_const (Real.exp C)).mono' hMeas.exp.aestronglyMeasurable
    filter_upwards [hBound] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
  unfold domainShiftLaw
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => (Real.exp_pos (h x)).le))]
  exact ENNReal.ofReal_ne_top

/-- Positive domain mass and strictly positive shift density imply that the
constructed spatial measure is nonzero. -/
theorem domainShiftLaw_neZero (N : ℕ) (B : Set (Vector N)) (h : Vector N → ℝ)
    (hMeas : Measurable h) (hMass : 0 < (sphereLaw N) B) :
    NeZero (domainShiftLaw N B h) := by
  have hbase : (sphereLaw N).restrict B ≠ 0 := by
    intro heq
    have hh := congrArg (fun ν : Measure (Vector N) => ν univ) heq
    have hz : (sphereLaw N) B = 0 := by simpa using hh
    exact hMass.ne' hz
  constructor
  intro heq
  have hreverse : (sphereLaw N).restrict B ≪ domainShiftLaw N B h :=
    withDensity_absolutelyContinuous' hMeas.exp.ennreal_ofReal.aemeasurable
      (Eventually.of_forall (fun x => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos (h x))))
  rw [heq] at hreverse
  exact hbase (Measure.absolutelyContinuous_zero_iff.mp hreverse)

/-- The constructed constrained spatial law is carried by the actual sphere. -/
theorem domainShiftLaw_support {N : ℕ} (hN : 1 ≤ N)
    (B : Set (Vector N)) (h : Vector N → ℝ) :
    ∀ᵐ x ∂domainShiftLaw N B h, ‖x‖^2=(N:ℝ) := by
  have hac : domainShiftLaw N B h ≪ sphereLaw N :=
    (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous
  exact (sphereLaw_support hN).filter_mono hac.ae_le

/-- The constrained weighted-law partition equals the manuscript's
literal integral over B with its deterministic additive shift. -/
theorem partitionAgainst_domainShiftLaw (N : ℕ) (B : Set (Vector N))
    (h : Vector N → ℝ) (hMeas : Measurable h) (β : ℝ) (H : Vector N → ℝ) :
    partitionAgainst (domainShiftLaw N B h) β H =
      ∫ x in B, Real.exp (β*H x+h x) ∂sphereLaw N := by
  unfold partitionAgainst domainShiftLaw
  rw [integral_withDensity_eq_integral_toReal_smul hMeas.exp.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp only [ENNReal.toReal_ofReal (Real.exp_pos (h x)).le, smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

/-- The exact constrained and shifted free energy in `lem:pre-concentration`. -/
def constrainedLogPartition {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (B : Set (Vector N)) (h : Vector N → ℝ) (J : Disorder N P) : ℝ :=
  Real.log (∫ x in B, Real.exp (β*field c J x+h x) ∂sphereLaw N)

/-- Full `lem:pre-concentration`: every deterministic positive-mass Borel
domain and bounded measurable deterministic shift gives an integrable free
energy and the CLOSED deviation bound with the exact manuscript constant. -/
theorem constrainedLogPartition_concentration {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {β : ℝ} (hβ : 0 < β)
    (B : Set (Vector N)) (hB : MeasurableSet B) (hMass : 0 < (sphereLaw N) B)
    (h : Vector N → ℝ) (hMeas : Measurable h) (C : ℝ) (hBound : ∀ x ∈ B, |h x| ≤ C) :
    Integrable (constrainedLogPartition c β B h) (disorderLaw N P) ∧
      ∀ t : ℝ, 0 < t →
        disorderLaw N P {J | t*(N:ℝ) ≤ |constrainedLogPartition c β B h J-
          (∫ K, constrainedLogPartition c β B h K ∂disorderLaw N P)|} ≤
          ENNReal.ofReal (2*Real.exp (-(t^2*(N:ℝ))/(2*β^2*covariancePolynomial c 1))) := by
  have hBoundAE : ∀ᵐ x ∂(sphereLaw N).restrict B, |h x| ≤ C :=
    (ae_restrict_mem hB).mono (fun x hx => hBound x hx)
  have hfinite : IsFiniteMeasure (domainShiftLaw N B h) := domainShiftLaw_isFinite N B h hMeas C hBoundAE
  have hnonzero : NeZero (domainShiftLaw N B h) := domainShiftLaw_neZero N B h hMeas hMass
  have hsupport := domainShiftLaw_support hN B h
  have heq : constrainedLogPartition c β B h =
      fun J : Disorder N P => Real.log (partitionAgainst (domainShiftLaw N B h) β (field c J)) := by
    funext J
    rw [partitionAgainst_domainShiftLaw N B h hMeas]
    rfl
  rw [heq]
  constructor
  · exact logPartitionAgainst_disorder_integrable hN (domainShiftLaw N B h) hsupport c hc hcov hβ
  · intro t ht
    exact logPartitionAgainst_pressure_concentration hN (domainShiftLaw N B h) hsupport c hc hcov hβ ht

/-- The literal constrained shifted free energy for the manuscript's
canonical nonzero finite covariance mixture. -/
def mixtureConstrainedLogPartition {N : ℕ} (μ : SlowEquilibration.FiniteMixture) (β : ℝ)
    (B : Set (Vector N)) (h : Vector N → ℝ) (J : Disorder N μ.maxDegree) : ℝ :=
  Real.log (∫ x in B, Real.exp (β*fieldOfMixture μ J x+h x) ∂sphereLaw N)

/-- `lem:pre-concentration` instantiated for every actual canonical finite
mixture; nonzero covariance and the exact ξ(1) are proved from its coefficients. -/
theorem mixtureConstrainedLogPartition_concentration {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibration.FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (B : Set (Vector N)) (hB : MeasurableSet B) (hMass : 0 < (sphereLaw N) B)
    (h : Vector N → ℝ) (hMeas : Measurable h) (C : ℝ) (hBound : ∀ x ∈ B, |h x| ≤ C) :
    Integrable (mixtureConstrainedLogPartition μ β B h) (disorderLaw N μ.maxDegree) ∧
      ∀ t : ℝ, 0 < t →
        disorderLaw N μ.maxDegree {J | t*(N:ℝ) ≤ |mixtureConstrainedLogPartition μ β B h J-
          (∫ K, mixtureConstrainedLogPartition μ β B h K ∂disorderLaw N μ.maxDegree)|} ≤
          ENNReal.ofReal (2*Real.exp (-(t^2*(N:ℝ))/(2*β^2*μ.xi 1))) := by
  have hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1 := by
    rw [covariancePolynomial_mixture]
    exact μ.xi_pos (by norm_num)
  have hresult := constrainedLogPartition_concentration hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) hcov hβ B hB hMass h hMeas C hBound
  have heq : mixtureConstrainedLogPartition (N := N) μ β B h =
      constrainedLogPartition (mixtureCoefficients μ) β B h := rfl
  rw [heq]
  simpa only [covariancePolynomial_mixture] using hresult

end
end SlowEquilibration.SphericalModel
