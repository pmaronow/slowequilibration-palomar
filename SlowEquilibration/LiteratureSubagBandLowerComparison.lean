-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagTheorem5Proof
public import SlowEquilibration.LiteratureSubagRemark25Final
public import SlowEquilibration.ReplicaBandGibbsMass
public import SlowEquilibration.SourceMixedBandsLiteral

/-!
# Subag's finite-dimensional band reconstruction comparison

This proves `BandBlockRateComparison` exactly as encoded in the preceding
Theorem 5 reduction. The product-Gibbs band identity and the IID inequality
`P_(n*r) ≤ P_n^r` give a pointwise reconstruction bound. Gaussian concentration
of the center maximum and physical pressure, together with the proved
Proposition 24, makes that bound simultaneous over the center sphere. The
bounded truncated block logarithm permits integration with only the
probability of the exceptional event as error. All thresholds precede the
dimension limit, and the fixed-count normalization is preserved.

The lower approximation is not proved here. Subag's Section 2, Lemmas 18–20,
still requires a general zero-overlap replicated-pressure limit and its
thick-latitude comparison. Its exact named hypothesis remains explicit in
the further Theorem 5 and principal endpoint reductions below. No new
analytic hypothesis is introduced. Theorem 5 can use Chen-only physical
limit data; the dynamical endpoints retain their separate Chen–Sen input.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerComparison

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTheorem10Proof
open scoped Topology

set_option autoImplicit false

/-- The equilateral overlap constraint is Borel for every replica count. -/
private theorem overlapBlock_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

/-- Removing the cross constraints between two independent replica groups
bounds the complete block probability by the product of the two probabilities. -/
private theorem overlapBlock_pi_add_le_mul {N : ℕ} (ν : Measure (Vector N))
    [IsProbabilityMeasure ν] (n k : ℕ) (q ρ : ℝ) :
    (Measure.pi (fun _ : Fin (n + k) => ν)).real (overlapBlock q ρ) ≤
      (Measure.pi (fun _ : Fin n => ν)).real (overlapBlock q ρ) *
        (Measure.pi (fun _ : Fin k => ν)).real (overlapBlock q ρ) := by
  let e₁ := MeasurableEquiv.piCongrLeft
    (fun _ : Fin n ⊕ Fin k => Vector N) finSumFinEquiv.symm
  let e₂ := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => Vector N)
  let e := e₁.trans e₂
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin n ⊕ Fin k => ν) finSumFinEquiv.symm
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin k => ν)
  have h : MeasurePreserving e (Measure.pi (fun _ : Fin (n + k) => ν))
      ((Measure.pi (fun _ : Fin n => ν)).prod (Measure.pi (fun _ : Fin k => ν))) :=
    h₂.comp h₁
  have hm := h.hasLaw.measureReal_eq
    (p := fun x => x ∈ (overlapBlock q ρ) ×ˢ (overlapBlock q ρ))
    (by simpa only [Set.ofPred_mem_eq] using
      ((overlapBlock_measurable (N := N) (k := n) q ρ).prod
        (overlapBlock_measurable (N := N) (k := k) q ρ)))
  calc
    _ ≤ (Measure.pi (fun _ : Fin (n + k) => ν)).real
        {σ | e σ ∈ (overlapBlock q ρ) ×ˢ (overlapBlock q ρ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro σ hσ
      constructor
      · intro i j hij
        have hd : Fin.castAdd k i ≠ Fin.castAdd k j :=
          fun he => hij (Fin.castAdd_inj.mp he)
        simpa [e, e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] using
          hσ (Fin.castAdd k i) (Fin.castAdd k j) hd
      · intro i j hij
        have hd : Fin.natAdd n i ≠ Fin.natAdd n j :=
          fun he => hij (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)))
        simpa [e, e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
          MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] using
          hσ (Fin.natAdd n i) (Fin.natAdd n j) hd
    _ = _ := by
      calc
        _ = ((Measure.pi (fun _ : Fin n => ν)).prod
            (Measure.pi (fun _ : Fin k => ν))).real
              ((overlapBlock q ρ) ×ˢ (overlapBlock q ρ)) := by
          simpa only [Set.ofPred_mem_eq] using hm
        _ = _ := by simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]

/-- The preceding factorization at the literal original-disorder Gibbs kernel. -/
private theorem conditionalBlockProbability_add_le_mul (N n k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) :
    conditionalBlockProbability N (n + k) μ β q ρ J ≤
      conditionalBlockProbability N n μ β q ρ J *
        conditionalBlockProbability N k μ β q ρ J := by
  simp only [conditionalBlockProbability, GaussianReplicaKernel.iid_apply]
  exact overlapBlock_pi_add_le_mul
    (allDimensionGibbsKernel (mixtureCoefficients μ) β J) n k q ρ

/-- The finite IID inequality used in Section 4: a complete block of `n*r`
replicas is contained in `r` independent blocks of `n` replicas. -/
theorem conditionalBlockProbability_mul_le_pow (N n r : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) :
    conditionalBlockProbability N (n * r) μ β q ρ J ≤
      conditionalBlockProbability N n μ β q ρ J ^ r := by
  induction r with
  | zero =>
      simp only [Nat.mul_zero, pow_zero]
      exact measureReal_le_one
  | succ r ih =>
      rw [Nat.mul_succ, pow_succ]
      exact (conditionalBlockProbability_add_le_mul N (n * r) n μ β q ρ J).trans
        (mul_le_mul_of_nonneg_right ih measureReal_nonneg)

/-- The same IID comparison when the large count is specified by divisibility. -/
private theorem conditionalBlockProbability_le_pow_of_dvd (N n k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) (hdiv : n ∣ k) :
    ∃ r : ℕ, k = n * r ∧
      conditionalBlockProbability N k μ β q ρ J ≤
        conditionalBlockProbability N n μ β q ρ J ^ r := by
  obtain ⟨r, hr⟩ := hdiv
  exact ⟨r, hr, hr ▸ conditionalBlockProbability_mul_le_pow N n r μ β q ρ J⟩

/-- Dividing the logarithmic IID estimate by the large count preserves the
requested fixed-count normalization. The floor is applied only on the right. -/
private theorem conditionalBlockProbability_log_div_le {N n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (μ : FiniteMixture) (β q ρ : ℝ)
    (J : Disorder N μ.maxDegree) (hdiv : n ∣ k)
    (hpos : 0 < conditionalBlockProbability N k μ β q ρ J) :
    Real.log (conditionalBlockProbability N k μ β q ρ J) / (k : ℝ) ≤
      Real.log (max (conditionalBlockProbability N n μ β q ρ J)
        (Real.exp (-(N : ℝ)))) / (n : ℝ) := by
  obtain ⟨r, rfl⟩ := hdiv
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hkr : 0 < ((n * r : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  let a := max (conditionalBlockProbability N n μ β q ρ J) (Real.exp (-(N : ℝ)))
  have hb : conditionalBlockProbability N (n * r) μ β q ρ J ≤ a ^ r :=
    (conditionalBlockProbability_mul_le_pow N n r μ β q ρ J).trans
      (pow_le_pow_left₀ measureReal_nonneg (le_max_left _ _) r)
  have hlog := Real.log_le_log hpos hb
  rw [Real.log_pow] at hlog
  apply (div_le_div_iff₀ hkr hnr).mpr
  calc
    _ ≤ ((r : ℝ) * Real.log a) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hlog hnr.le
    _ = _ := by push_cast; ring

/-- The block comparison in pressure units, at every physical dimension. -/
private theorem conditionalBlockProbability_log_pressure_le {N n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) (hdiv : n ∣ k)
    (hpos : 0 < conditionalBlockProbability N k μ β q ρ J) :
    Real.log (conditionalBlockProbability N k μ β q ρ J) /
        ((N : ℝ) * (k : ℝ)) ≤
      Real.log (max (conditionalBlockProbability N n μ β q ρ J)
        (Real.exp (-(N : ℝ)))) / ((N : ℝ) * (n : ℝ)) := by
  have hh := div_le_div_of_nonneg_right
    (conditionalBlockProbability_log_div_le hn hk μ β q ρ J hdiv hpos)
    (Nat.cast_nonneg (α := ℝ) N)
  simpa only [div_div, mul_comm] using hh

end SlowEquilibration.LiteratureSubagBandLowerComparison

namespace SlowEquilibration.LiteratureSubagBandLowerComparison

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTheorem10Proof
open scoped Topology BigOperators

set_option autoImplicit false

private theorem band_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem product_density_integrable {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (fun σ : Fin k → Vector N => ∏ i, gibbsDensity N β H (σ i))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) :=
  Integrable.fintype_prod (fun _ => gibbsDensity_integrable hN β hH)

private theorem product_gibbs_eq_withDensity {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Measure.pi (fun _ : Fin k => gibbsLaw N β H) =
      (Measure.pi (fun _ : Fin k => sphereLaw N)).withDensity
        (fun σ => ENNReal.ofReal (∏ i, gibbsDensity N β H (σ i))) := by
  let := gibbsLaw_probability hN β hH
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))), Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      (gibbsDensity_pos hN β hH x).le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gibbsLaw, withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (gibbsDensity_integrable hN β hH).restrict
      (.of_forall (fun x => (gibbsDensity_pos hN β hH x).le))]

private theorem product_gibbs_real_eq_integral {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    {B : Set (Fin k → Vector N)} (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β H)).real B =
      ∫ σ in B, ∏ i, gibbsDensity N β H (σ i)
        ∂Measure.pi (fun _ : Fin k => sphereLaw N) := by
  rw [product_gibbs_eq_withDensity hN β hH, Measure.real,
    withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))),
    ENNReal.toReal_ofReal (integral_nonneg (fun σ =>
      Finset.prod_nonneg (fun i _ => (gibbsDensity_pos hN β hH (σ i)).le)))]

private theorem product_density_formula {N k : ℕ} (β : ℝ)
    (H : Vector N → ℝ) (m : Vector N) (σ : Fin k → Vector N) :
    (∏ i, gibbsDensity N β H (σ i)) =
      (Real.exp ((k : ℝ) * β * H m) / partition N β H ^ k) *
        Real.exp (β * ∑ i : Fin k, (H (σ i) - H m)) := by
  simp only [gibbsDensity, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

private theorem product_gibbs_band_mass {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (ReplicatedBand k q δ ρ m) =
      (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ k) * replicatedBandPartition k μ β q δ ρ J m := by
  rw [product_gibbs_real_eq_integral hN β (field_contDiff _ J).continuous
    (band_measurable q δ ρ m)]
  simp_rw [product_density_formula β (field (mixtureCoefficients μ) J) m]
  rw [integral_const_mul]
  rfl

private theorem replicated_integrand_integrable {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    Integrable (fun σ : Fin k → Vector N =>
      Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (σ i)-field (mixtureCoefficients μ) J m)))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) := by
  have hi := partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β
    ((field_contDiff (mixtureCoefficients μ) J).continuous.sub
      (continuous_const (y := field (mixtureCoefficients μ) J m)))
  have hh := Integrable.fintype_prod (fun _ : Fin k => hi)
  convert hh using 1
  ext σ
  rw [Finset.mul_sum,Real.exp_sum]
  rfl


end SlowEquilibration.LiteratureSubagBandLowerComparison

namespace SlowEquilibration.LiteratureSubagBandLowerComparison

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTheorem10Proof
open LiteratureSubagTAP LiteratureSubagProposition24 LiteratureSubagTheorem5Proof
open scoped Topology BigOperators

set_option autoImplicit false

/-- The logarithm of the exact product-Gibbs band identity gives the
finite-volume TAP gap bounded by the complete replica-block cost. -/
private theorem band_gap_le_block_log {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β q δ η ρ : ℝ) (hηρ : η ≤ ρ)
    (J : Disorder N μ.maxDegree) (m : Vector N)
    (hvol : 0 < (Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ η m)) :
    0 < conditionalBlockProbability N k μ β q ρ J ∧
      β * field (mixtureCoefficients μ) J m / (N : ℝ) +
        replicatedBandPressure k μ β q δ η J m -
        Real.log (mixturePartition μ β J) / (N : ℝ) ≤
      Real.log (conditionalBlockProbability N k μ β q ρ J) /
        ((N : ℝ) * (k : ℝ)) := by
  let M := (Measure.pi (fun _ : Fin k =>
    gibbsLaw N β (field (mixtureCoefficients μ) J))).real
      (ReplicatedBand k q δ η m)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hZ := mixturePartition_pos hN μ β J
  let : NeZero ((Measure.pi (fun _ : Fin k => sphereLaw N))
      (ReplicatedBand k q δ η m)) := ⟨hvol.ne'⟩
  have hB : 0 < replicatedBandPartition k μ β q δ η J m :=
    integral_exp_pos (replicated_integrand_integrable hN μ β J m).restrict
  have hM : M =
      (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ k) * replicatedBandPartition k μ β q δ η J m :=
    product_gibbs_band_mass hN μ β q δ η J m
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMP : M ≤ conditionalBlockProbability N k μ β q ρ J := by
    let := gibbsLaw_probability hN β (field_contDiff (mixtureCoefficients μ) J).continuous
    unfold conditionalBlockProbability
    rw [GaussianReplicaKernel.iid_apply, allDimensionGibbsKernel_apply]
    apply measureReal_mono _ (measure_ne_top _ _)
    intro σ hσ
    exact fun i j hij => (hσ.2 i j hij).trans_le hηρ
  refine ⟨hMpos.trans_le hMP, ?_⟩
  have hlog := Real.log_le_log hMpos hMP
  rw [hM, Real.log_mul (div_ne_zero (Real.exp_ne_zero _)
    (pow_ne_zero _ hZ.ne')) hB.ne', Real.log_div (Real.exp_ne_zero _)
      (pow_ne_zero _ hZ.ne'), Real.log_exp, Real.log_pow] at hlog
  unfold replicatedBandPressure
  apply (le_div_iff₀ (mul_pos hNr hkr)).mpr
  convert hlog using 1
  field_simp
  ring

/-- The exponential floor bounds the normalized quenched block logarithm
between `-1/n` and zero, uniformly in the disorder. -/
private theorem normalized_block_log_bounds {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    (μ : FiniteMixture) (β q ρ : ℝ) (J : Disorder N μ.maxDegree) :
    -(1 / (n : ℝ)) ≤
        Real.log (max (conditionalBlockProbability N n μ β q ρ J)
          (Real.exp (-(N : ℝ)))) / ((N : ℝ) * (n : ℝ)) ∧
      Real.log (max (conditionalBlockProbability N n μ β q ρ J)
        (Real.exp (-(N : ℝ)))) / ((N : ℝ) * (n : ℝ)) ≤ 0 := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlo := Real.log_le_log (Real.exp_pos (-(N : ℝ)))
    (le_max_right (conditionalBlockProbability N n μ β q ρ J) (Real.exp (-(N : ℝ))))
  rw [Real.log_exp] at hlo
  have hhi : Real.log (max (conditionalBlockProbability N n μ β q ρ J)
      (Real.exp (-(N : ℝ)))) ≤ 0 :=
    Real.log_nonpos ((Real.exp_pos _).le.trans (le_max_right _ _))
      (max_le measureReal_le_one
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))))
  refine ⟨?_, div_nonpos_of_nonpos_of_nonneg hhi (by positivity)⟩
  apply (le_div_iff₀ (mul_pos hNr hnr)).mpr
  convert hlo using 1
  field_simp

private theorem normalized_block_log_integrable {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    (μ : FiniteMixture) (β q ρ : ℝ) :
    Integrable (fun J =>
      Real.log (max (conditionalBlockProbability N n μ β q ρ J)
        (Real.exp (-(N : ℝ)))) / ((N : ℝ) * (n : ℝ))) (disorderLaw N μ.maxDegree) := by
  have hf : Measurable (conditionalBlockProbability N n μ β q ρ) :=
    (Kernel.measurable_coe _ (overlapBlock_measurable q ρ)).ennreal_toReal
  refine (integrable_const (1 / (n : ℝ))).mono'
    (((hf.max measurable_const).log.div_const _).aestronglyMeasurable)
    (.of_forall fun J => ?_)
  obtain ⟨hlo, hhi⟩ := normalized_block_log_bounds hN hn μ β q ρ J
  rw [Real.norm_eq_abs, abs_of_nonpos hhi]
  linarith

/-- A bounded nonpositive observable needs only a positive-probability
good event to pass a deterministic bound to its expectation. -/
private theorem constant_le_integral_of_good
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {A : Set Ω} (hA : MeasurableSet A) (hApos : 0 < ν.real A)
    {f : Ω → ℝ} (hf : Integrable f ν) {a ε b : ℝ}
    (hbound : ∀ x, -b ≤ f x ∧ f x ≤ 0)
    (hgood : ∀ x ∈ A, a ≤ f x + ε) :
    a ≤ (∫ x, f x ∂ν) + ε + b * ν.real Aᶜ := by
  obtain ⟨x, hx⟩ := nonempty_of_measureReal_ne_zero hApos.ne'
  have ha : a ≤ ε := by linarith [hgood x hx, (hbound x).2]
  have hi : Integrable (Aᶜ.indicator (fun _ => b)) ν :=
    (integrable_const b).indicator hA.compl
  have hp : ∀ x, a ≤ f x + ε + Aᶜ.indicator (fun _ => b) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx), add_zero]
      exact hgood x hx
    · rw [Set.indicator_of_mem (show x ∈ Aᶜ from hx)]
      linarith [(hbound x).1]
  have hh := integral_mono (integrable_const a) ((hf.add (integrable_const ε)).add hi) hp
  change (∫ x, a ∂ν) ≤ ∫ x, f x + ε + Aᶜ.indicator (fun _ => b) x ∂ν at hh
  have hadd := integral_add (hf.add (integrable_const ε)) hi
  have hadd' := integral_add hf (integrable_const ε)
  simp only [Pi.add_apply] at hadd hadd'
  rw [hadd, hadd', integral_const, integral_const,
    integral_indicator hA.compl, setIntegral_const, probReal_univ,
    one_smul, one_smul, smul_eq_mul] at hh
  simpa only [mul_comm (ν.real Aᶜ) b] using hh

end SlowEquilibration.LiteratureSubagBandLowerComparison

namespace SlowEquilibration.LiteratureSubagBandLowerComparison

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagTAP
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open SphericalParisiContinuousMaximum SphericalGaussianJet SphericalTaylorRemainder
open WholeFieldRegression PureTensorJetBounds
open scoped Topology RealInnerProductSpace

set_option autoImplicit false

/-- The original Hamiltonian maximum on the center sphere. -/
private def centerMaximum (N : ℕ) (μ : FiniteMixture) (q : ℝ)
    (J : Disorder N μ.maxDegree) : ℝ :=
  sSup ((field (mixtureCoefficients μ) J) ''
    {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q})

/-- The original center maximum is the compact continuous-field maximum. -/
private theorem centerMaximum_eq_maximum (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 1 ≤ N) (J : Disorder N μ.maxDegree) :
    haveI : NeZero N := ⟨by omega⟩
    centerMaximum N μ q J =
      maximum (centerContinuousField μ q N (euclideanDisorder J)) := by
  let : NeZero N := ⟨by omega⟩
  unfold centerMaximum
  rw [centerSphere_sup_eq_scaledMixture μ q hq J,
    centerMixture_coefficients μ q hq]
  exact sSup_sphere_eq_maximum μ q (by omega) J

/-- A genuine center attains the maximum in every positive dimension. -/
private theorem centerMaximum_attained (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 1 ≤ N) (J : Disorder N μ.maxDegree) :
    ∃ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q ∧
      field (mixtureCoefficients μ) J m = centerMaximum N μ q J := by
  let : NeZero N := ⟨by omega⟩
  obtain ⟨u, hu⟩ := maximum_attained (centerContinuousField μ q N (euclideanDisorder J))
  have hun : ‖u.val‖ = 1 := by
    simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using u.property
  refine ⟨Real.sqrt q • (Real.sqrt (N : ℝ) • u.val), ?_, ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), hun, mul_one, mul_pow,
      Real.sq_sqrt hq.le, Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  · rw [centerMaximum_eq_maximum μ hq hN J, hu]
    simp only [centerContinuousField, modelContinuousField_apply, valueObservation_actual]
    exact (field_center_scale (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) hq.le J _).symm

private theorem euclideanDisorder_measurable (N P : ℕ) :
    Measurable (euclideanDisorder (N := N) (P := P)) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
    (flatDisorder_measurable N P)

/-- The literal center maximum is Borel in the original tensor coordinates. -/
private theorem centerMaximum_measurable (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 1 ≤ N) :
    Measurable (centerMaximum N μ q) := by
  let : NeZero N := ⟨by omega⟩
  have hm := (maximum_continuous.comp (centerContinuousField μ q N).continuous).measurable.comp
    (euclideanDisorder_measurable N μ.maxDegree)
  have heq : centerMaximum N μ q = fun J =>
      maximum (centerContinuousField μ q N (euclideanDisorder J)) :=
    funext (centerMaximum_eq_maximum μ hq hN)
  rw [heq]
  exact hm

/-- The center maximum has the exact covariance Lipschitz constant. -/
private theorem center_maximum_lipschitz (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 1 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩
    LipschitzWith (Real.sqrt ((N : ℝ) * μ.xi q)).toNNReal
      (fun g : EuclideanDisorder N μ.maxDegree =>
        maximum (centerContinuousField μ q N g)) := by
  let : NeZero N := ⟨by omega⟩
  apply LipschitzWith.of_le_add_mul
  intro g h
  obtain ⟨u, hu⟩ := maximum_attained (centerContinuousField μ q N g)
  have hun : ‖u.val‖ = 1 := by
    simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using u.property
  have hscaled : ‖Real.sqrt (N : ℝ) • u.val‖ ^ 2 = (N : ℝ) := by
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), hun, mul_one]
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  have hd := field_euclidean_difference_bound hN
    (centerCoefficients (mixtureCoefficients μ) q)
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hq.le)
    g h (Real.sqrt (N : ℝ) • u.val) hscaled
  rw [covariancePolynomial_center, covariancePolynomial_mixture, mul_one] at hd
  have hgd : |centerContinuousField μ q N g u -
      centerContinuousField μ q N h u| ≤
      Real.sqrt ((N : ℝ) * μ.xi q) * dist g h := by
    simpa only [centerContinuousField, modelContinuousField_apply,
      valueObservation, flatJetCLM_apply, jet, iteratedFDeriv_zero_apply] using hd
  have hh := le_maximum (centerContinuousField μ q N h) u
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), hu]
  linarith [le_abs_self (centerContinuousField μ q N g u -
    centerContinuousField μ q N h u)]

/-- Two-sided concentration of the actual normalized center maximum. -/
private theorem centerMaximum_concentration (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    (disorderLaw N μ.maxDegree).real
      {J | |centerMaximum N μ q J / (N : ℝ) -
        expectedCenterGroundEnergy N μ q| > t} ≤
      2 * Real.exp (-(t ^ 2 / (2 * μ.xi q)) * (N : ℝ)) := by
  let : NeZero N := ⟨by omega⟩
  let F := fun g : EuclideanDisorder N μ.maxDegree =>
    maximum (centerContinuousField μ q N g)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hxi : 0 < μ.xi q := μ.xi_pos hq
  have hLip := center_maximum_lipschitz μ hq hN
  have hlaw := euclideanDisorder_hasLaw N μ.maxDegree
  have hmean : (∫ J, F (euclideanDisorder J) ∂disorderLaw N μ.maxDegree) =
      ∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) :=
    hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have hE : expectedCenterGroundEnergy N μ q =
      (∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate N μ.maxDegree)) / (N : ℝ) := by
    unfold expectedCenterGroundEnergy
    change (∫ J, centerMaximum N μ q J ∂disorderLaw N μ.maxDegree) / (N : ℝ) = _
    rw [integral_congr_ae (.of_forall (centerMaximum_eq_maximum μ hq hN)), hmean]
  have hc := SYK.euclidean_lipschitz_gaussian_concentration F
    (Real.sqrt ((N : ℝ) * μ.xi q)) ((N : ℝ) * t)
    (Real.sqrt_pos.mpr (mul_pos hNr hxi)) (mul_pos hNr ht) hLip
  have hset : MeasurableSet {g : EuclideanDisorder N μ.maxDegree |
      |F g - ∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate N μ.maxDegree)| > (N : ℝ) * t} :=
    (isOpen_lt continuous_const (hLip.continuous.sub continuous_const).abs).measurableSet
  nth_rw 1 [← hlaw.map_eq] at hc
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at hc
  have hevent : {J : Disorder N μ.maxDegree |
      |centerMaximum N μ q J / (N : ℝ) - expectedCenterGroundEnergy N μ q| > t} =
      euclideanDisorder ⁻¹' {g | |F g - ∫ y, F y
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)| >
          (N : ℝ) * t} := by
    ext J
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, centerMaximum_eq_maximum μ hq hN, hE]
    rw [← sub_div, abs_div, abs_of_pos hNr, gt_iff_lt, lt_div_iff₀ hNr]
    rw [mul_comm t]
  have hrate : -((N : ℝ) * t)^2 /
      (2 * (Real.sqrt ((N : ℝ) * μ.xi q))^2) =
        -(t^2/(2*μ.xi q))*(N : ℝ) := by
    rw [Real.sq_sqrt (mul_nonneg hNr.le hxi.le)]
    field_simp
  rw [hevent]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc).trans_eq (by
    rw [ENNReal.toReal_ofReal (by positivity), hrate])

/-- Two-sided concentration of the actual normalized pressure. -/
private theorem pressure_concentration (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 < β) {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    (disorderLaw N μ.maxDegree).real
      {J | |Real.log (mixturePartition μ β J) / (N : ℝ) -
        quenchedPressure N μ β| > t} ≤
      2 * Real.exp (-(t ^ 2 / (2 * β ^ 2 * μ.xi 1)) * (N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1 := by
    rw [covariancePolynomial_mixture]
    exact μ.xi_pos (by norm_num)
  have hc := logPartition_concentration hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) hcov hβ (mul_pos hNr ht)
  have hevent : {J : Disorder N μ.maxDegree |
      |Real.log (mixturePartition μ β J) / (N : ℝ) - quenchedPressure N μ β| > t} =
      {J | |Real.log (partition N β (field (mixtureCoefficients μ) J)) -
        ∫ K, Real.log (partition N β (field (mixtureCoefficients μ) K))
          ∂disorderLaw N μ.maxDegree| > (N : ℝ) * t} := by
    ext J
    simp only [Set.mem_ofPred_eq, quenchedPressure, mixturePartition]
    rw [← sub_div, abs_div, abs_of_pos hNr, gt_iff_lt, lt_div_iff₀ hNr]
    rw [mul_comm t]
    rfl
  have hrate : -((N : ℝ) * t)^2 /
      (2 * β^2 * (N : ℝ) * μ.xi 1) =
        -(t^2/(2*β^2*μ.xi 1))*(N : ℝ) := by
    field_simp
  rw [hevent]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc).trans_eq (by
    rw [ENNReal.toReal_ofReal (by positivity), covariancePolynomial_mixture, hrate])

private theorem exponential_tail_eventually_small {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.exp (-c * (N : ℝ)) < s := by
  have hlim : Tendsto (fun N : ℕ => 2 * Real.exp (-c * (N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc))
    simpa only [Function.comp_apply, mul_zero] using he.const_mul 2
  exact hlim.eventually (gt_mem_nhds hs)

/-- Center-maximum failures have arbitrarily small probability eventually. -/
private theorem centerMaximum_bad_eventually_small (μ : FiniteMixture) {q t s : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, (disorderLaw N μ.maxDegree).real
      {J | |centerMaximum N μ q J / (N : ℝ) -
        expectedCenterGroundEnergy N μ q| > t} < s := by
  have hc : 0 < t^2 / (2*μ.xi q) := by positivity [μ.xi_pos hq]
  filter_upwards [eventually_ge_atTop (1 : ℕ), exponential_tail_eventually_small hc hs]
    with N hN htail
  exact (centerMaximum_concentration μ hq hN ht).trans_lt htail

/-- Pressure failures have arbitrarily small probability eventually. -/
private theorem pressure_bad_eventually_small (μ : FiniteMixture) {β t s : ℝ}
    (hβ : 0 < β) (ht : 0 < t) (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, (disorderLaw N μ.maxDegree).real
      {J | |Real.log (mixturePartition μ β J) / (N : ℝ) -
        quenchedPressure N μ β| > t} < s := by
  have hc : 0 < t^2 / (2*β^2*μ.xi 1) := by positivity [μ.xi_pos (by norm_num : (0 : ℝ) < 1)]
  filter_upwards [eventually_ge_atTop (1 : ℕ), exponential_tail_eventually_small hc hs]
    with N hN htail
  exact (pressure_concentration μ hβ hN ht).trans_lt htail

end SlowEquilibration.LiteratureSubagBandLowerComparison

namespace SlowEquilibration.LiteratureSubagBandLowerComparison

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem10Proof LiteratureSubagTheorem5Proof LiteratureSubagProposition24
open scoped Topology

set_option autoImplicit false

/-- Subag's Section 4 finite-dimensional reconstruction estimate, with the
exact fixed-count normalization and all parameters chosen before dimension.
Only Proposition 24 is consumed; it is already a proved repository interface. -/
theorem bandBlockRateComparison (μ : FiniteMixture) (β : ℝ) :
    BandBlockRateComparison μ β := by
  intro q hq h24 n hn ρ ε hρ hε
  have hβ : 0 < β := h24.1
  let t : ℝ := ε / (4 * (β + 2))
  have ht : 0 < t := by dsimp [t]; positivity
  have hterr : (β + 2) * t = ε / 4 := by dsimp [t]; field_simp
  let u : ℝ := min (ε / 4) (1 / 4)
  have hu : 0 < u := by dsimp [u]; positivity
  have hue : u ≤ ε / 4 := min_le_left _ _
  have hu1 : u ≤ 1 / 4 := min_le_right _ _
  have hus : 0 < u / 3 := by positivity
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, K, hcon⟩ := h24.2.2 t 1 ht zero_lt_one
  refine ⟨δ₀, hδ₀, ρ₀, hρ₀, max K 1, ?_⟩
  intro δ hδ hδsmall η hη hηsmall k hk hdiv
  have hkK : K ≤ k := (le_max_left K 1).trans hk
  have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
  have hηρ₀ : η ≤ ρ₀ := hηsmall.trans (min_le_left _ _)
  have hηρ : η ≤ ρ := hηsmall.trans (min_le_right _ _)
  filter_upwards [eventually_ge_atTop (k + 1),
    centerMaximum_bad_eventually_small μ hq.1 ht hus,
    pressure_bad_eventually_small μ hβ ht hus,
    exponential_tail_eventually_small zero_lt_one hus]
    with N hNk hground hpressure hexp
  have hN : 1 ≤ N := by omega
  obtain ⟨hΩ, hpΩ⟩ := hcon δ hδ hδsmall η hη hηρ₀ k hkK N hNk
  let Ω := uniformDeviationEvent (N := N) k μ β q δ η t
  let G : Set (Disorder N μ.maxDegree) :=
    {J | |centerMaximum N μ q J / (N : ℝ) - expectedCenterGroundEnergy N μ q| ≤ t}
  let P : Set (Disorder N μ.maxDegree) :=
    {J | |Real.log (mixturePartition μ β J) / (N : ℝ) - quenchedPressure N μ β| ≤ t}
  let A := Ω ∩ G ∩ P
  have hG : MeasurableSet G := measurableSet_le
    (((centerMaximum_measurable μ hq.1 hN).div_const _).sub measurable_const).abs
    measurable_const
  have hP : MeasurableSet P := measurableSet_le
    ((((mixturePartition_continuous hN μ β).measurable.log).div_const _).sub
      measurable_const).abs measurable_const
  have hA : MeasurableSet A := (hΩ.inter hG).inter hP
  have hΩbad : (disorderLaw N μ.maxDegree).real Ωᶜ ≤ Real.exp (-(N : ℝ)) := by
    rw [measureReal_compl hΩ, probReal_univ]
    simp only [neg_one_mul] at hpΩ
    linarith
  have hAbound : (disorderLaw N μ.maxDegree).real Aᶜ ≤
      Real.exp (-(N : ℝ)) + (disorderLaw N μ.maxDegree).real Gᶜ +
        (disorderLaw N μ.maxDegree).real Pᶜ := by
    dsimp only [A]
    simp only [compl_inter]
    have h₁ := measureReal_union_le (μ := disorderLaw N μ.maxDegree) Ωᶜ Gᶜ
    have h₂ := measureReal_union_le (μ := disorderLaw N μ.maxDegree) (Ωᶜ ∪ Gᶜ) Pᶜ
    linarith
  have hGbad : (disorderLaw N μ.maxDegree).real Gᶜ < u / 3 := by
    simpa only [G, compl_ofPred, not_le] using hground
  have hPbad : (disorderLaw N μ.maxDegree).real Pᶜ < u / 3 := by
    simpa only [P, compl_ofPred, not_le] using hpressure
  have hAbad : (disorderLaw N μ.maxDegree).real Aᶜ < u := by
    simp only [neg_one_mul] at hexp
    linarith [Real.exp_pos (-(N : ℝ))]
  have hApos : 0 < (disorderLaw N μ.maxDegree).real A := by
    have hs := measureReal_add_measureReal_compl (μ := disorderLaw N μ.maxDegree) hA
    rw [probReal_univ] at hs
    linarith
  intro m hm
  let f := fun J : Disorder N μ.maxDegree =>
    Real.log (max (conditionalBlockProbability N n μ β q ρ J)
      (Real.exp (-(N : ℝ)))) / ((N : ℝ) * (n : ℝ))
  have hgood : ∀ J ∈ A,
      β * expectedCenterGroundEnergy N μ q +
          expectedReplicatedBandPressure k μ β q δ η m - quenchedPressure N μ β ≤
        f J + (β + 2) * t := by
    intro J hJ
    obtain ⟨mstar, hmstar, hmax⟩ := centerMaximum_attained μ hq.1 hN J
    have hvol := SourcePureSection9SmallClosures.replicatedBand_volume_positive
      hNk hk1 hq hδ hη mstar hmstar
    obtain ⟨hpos, hband⟩ := band_gap_le_block_log hN hk1 μ β q δ η ρ hηρ J mstar hvol
    have hblock := conditionalBlockProbability_log_pressure_le hn hk1 μ β q ρ J hdiv hpos
    have hgap : β * field (mixtureCoefficients μ) J mstar / (N : ℝ) +
        replicatedBandPressure k μ β q δ η J mstar -
          Real.log (mixturePartition μ β J) / (N : ℝ) ≤ f J :=
      hband.trans hblock
    obtain ⟨s, hs, hsbound⟩ := hJ.1.1
    have hnorm : ‖mstar‖ = ‖m‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hmstar.trans hm.symm)
    have hmean := SourceMixedBandsLiteral.replicated_band_expected_center_independent
      k μ β q δ η mstar m hnorm
    have hb := hsbound mstar hmstar
    rw [hmean] at hb
    have hg : |field (mixtureCoefficients μ) J mstar / (N : ℝ) -
        expectedCenterGroundEnergy N μ q| ≤ t := by
      rw [hmax]
      exact hJ.1.2
    have hg' : expectedCenterGroundEnergy N μ q ≤
        field (mixtureCoefficients μ) J mstar / (N : ℝ) + t := by
      linarith [(abs_le.mp hg).1]
    have hβg := mul_le_mul_of_nonneg_left hg' hβ.le
    rw [mul_add, ← mul_div_assoc] at hβg
    have hp : |Real.log (mixturePartition μ β J) / (N : ℝ) -
        quenchedPressure N μ β| ≤ t := hJ.2
    linarith [(abs_le.mp hb).1, (abs_le.mp hp).2]
  have hh := constant_le_integral_of_good (disorderLaw N μ.maxDegree) hA hApos
    (normalized_block_log_integrable hN hn μ β q ρ)
    (fun J => normalized_block_log_bounds hN hn μ β q ρ J) hgood
  have hfmean : (∫ J, f J ∂disorderLaw N μ.maxDegree) =
      truncatedQuenchedBlockRate N n μ β q ρ / (n : ℝ) := by
    simp only [f, integral_div, truncatedQuenchedBlockRate, div_div]
  change β * expectedCenterGroundEnergy N μ q +
      expectedReplicatedBandPressure k μ β q δ η m - quenchedPressure N μ β ≤
    (∫ J, f J ∂disorderLaw N μ.maxDegree) + (β + 2) * t +
      (1 / (n : ℝ)) * (disorderLaw N μ.maxDegree).real Aᶜ at hh
  rw [hfmean, hterr] at hh
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < n)).mpr hnr
  have hbad := mul_le_mul_of_nonneg_right hinv
    (measureReal_nonneg (μ := disorderLaw N μ.maxDegree) (s := Aᶜ))
  linarith

end SlowEquilibration.LiteratureSubagBandLowerComparison

namespace SlowEquilibration.LiteratureSubagBandLowerComparison

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof LiteratureSubagRemark25Final
open scoped Topology

set_option autoImplicit false

/-- The remaining lower approximation depends only on the physical residual
limit, so its statement is independent of the choice of thermodynamic data. -/
theorem expectedBandLowerApproximation_iff {μ : FiniteMixture} {β : ℝ}
    (D E : ThermodynamicData μ β) :
    ExpectedBandLowerApproximation D ↔ ExpectedBandLowerApproximation E := by
  have hres (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) : D.residual q = E.residual q :=
    (thermodynamicData_values_unique D E).2 q hq |>.2
  constructor
  · intro h q hq
    simpa only [hres q hq] using h q hq
  · intro h q hq
    simpa only [hres q hq] using h q hq

end SlowEquilibration.LiteratureSubagBandLowerComparison

namespace SlowEquilibration.LiteratureSubagBandLowerComparison.Endpoints

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalTAPCertificate LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem5Proof LiteratureSubagRemark25Proof LiteratureSubagRemark25Final
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalOrthogonalHaar SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false

/-- The exact Theorem 5 interface with reconstruction discharged. The two
expected-band approximations and subsequence extraction remain explicit. -/
theorem theorem5_of_band_estimates_reduced3 {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation D)
    (hlower : ExpectedBandLowerApproximation D)
    (hextract : SubsequenceBandExtraction D) : Theorem5 D :=
  theorem5_of_band_estimates D hβ hupper hlower hextract (bandBlockRateComparison μ β)

/-- Chen alone constructs the physical limit data needed by the reconstruction
reduction; no zero-temperature variational formula is required here. -/
theorem theorem5_chen_reduced3 (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation (chenThermodynamicData hChen μ hβ.le))
    (hlower : ExpectedBandLowerApproximation (chenThermodynamicData hChen μ hβ.le))
    (hextract : SubsequenceBandExtraction (chenThermodynamicData hChen μ hβ.le)) :
    Theorem5 (chenThermodynamicData hChen μ hβ.le) :=
  theorem5_of_band_estimates_reduced3 _ hβ hupper hlower hextract

/-- The literature-data interface with the exact finite-dimensional block
comparison proved. The original lower approximation remains a premise. -/
theorem theorem5_literature_reduced3
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ hβ.le))
    (hlower : ExpectedBandLowerApproximation
      (literatureThermodynamicData hChen hChenSen μ hβ.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ hβ.le)) :
    Theorem5 (literatureThermodynamicData hChen hChenSen μ hβ.le) :=
  theorem5_of_band_estimates_reduced3 _ hβ hupper hlower hextract

/-- The complete principal dynamical conclusion, with the block-rate
comparison discharged and the three remaining band premises stated exactly. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced3
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hlower : ExpectedBandLowerApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le)) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) :=
  LiteratureSubagTheorem5Proof.finiteMixture_main_condensed_and_initial_literal_reduced2
    μ h hChen hChenSen hupper hlower hextract (bandBlockRateComparison μ β)

universe u v

/-- The all-initial spherical endpoint, retaining its full universe-polymorphic
conclusion and removing the finite-dimensional reconstruction premise. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced3
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (hupper : ExpectedBandUpperApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hlower : ExpectedBandLowerApproximation
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (hextract : SubsequenceBandExtraction
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le)) :
    ∃ γ : ℝ, 0 < γ ∧ SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ :=
  LiteratureSubagTheorem5Proof.finiteMixture_all_initial_spherical_of_literature_reduced2.{u,v}
    μ h hChen hChenSen hupper hlower hextract (bandBlockRateComparison μ β)

end SlowEquilibration.LiteratureSubagBandLowerComparison.Endpoints
