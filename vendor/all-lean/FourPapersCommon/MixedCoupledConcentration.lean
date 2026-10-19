module
public import FourPapersCommon.MixedGuerraDisorder
public import FourPapersCommon.MixedModel
public import Targets.CoupledConcentration

@[expose] public section

/-! Actual Gaussian concentration for coupled mixed-model cascades.

The covariance-dependent norm calculation uses the actual mixed kernel. The
remaining finite Gaussian analytic lemmas reuse the audited cascade calculus.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology SpinGlass SpinGlass.Targets Set
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n k : ℕ} {ξ : AdmissibleEvenMixture}
set_option maxHeartbeats 800000

abbrev MixedCoupledGaussianSpace (sk : MixedDisorder (Ω := Ω) n ξ) :=
  EuclideanSpace ℝ (sk.hU.ι ⊕ Fin n)

def mixedCoupledGaussianU (sk : MixedDisorder (Ω := Ω) n ξ)
    (z : MixedCoupledGaussianSpace sk) : EnergySpace n :=
  ∑ i, (Real.sqrt (sk.hU.τ i) * z (Sum.inl i)) • sk.hU.w i

def mixedCoupledGaussianX (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k)
    (z : MixedCoupledGaussianSpace sk) (i : Fin n) : ℝ :=
  Real.sqrt ((mixedBeta ξ) ^ 2 * s.q 1) * z (Sum.inr i)

def mixedCoupledGaussianCoeff (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (t : ℝ) (σ : Config n) : MixedCoupledGaussianSpace sk :=
  WithLp.toLp 2 (Sum.elim
    (fun i => Real.sqrt t * Real.sqrt (sk.hU.τ i) * sk.hU.w i σ)
    (fun i => Real.sqrt (1 - t) * Real.sqrt ((mixedBeta ξ) ^ 2 * s.q 1) * spin n σ i))

theorem mixedCoupledGaussianCoeff_norm_sq (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Config n) :
    ‖mixedCoupledGaussianCoeff sk s t σ‖ ^ 2 =
      t * (n * ξ.value 1) + (1 - t) * ((mixedBeta ξ) ^ 2 * s.q 1) * n := by
  have hq := s.q_nonneg (show 1 ≤ k + 2 by omega)
  have hspin : ∀ i, (spin n σ i) ^ 2 = 1 := by
    intro i
    simp only [spin]
    split_ifs <;> norm_num
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [mixedCoupledGaussianCoeff, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_pow, Real.sq_sqrt ht.1, Real.sq_sqrt (sub_nonneg.mpr ht.2),
    Real.sq_sqrt (mul_nonneg (sq_nonneg _) hq), Real.sq_sqrt (NNReal.coe_nonneg _), hspin,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc := mixedDisorder_covariance_spectral_sum ξ sk σ σ
  rw [overlap_self n hn σ] at hc
  have he : (∑ i : sk.hU.ι, t * (sk.hU.τ i : ℝ) * (sk.hU.w i σ) ^ 2) =
      t * ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) * (sk.hU.w i σ * sk.hU.w i σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hc]
  ring

theorem mixedCoupledGaussianCoeff_norm_le (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Config n) :
    ‖mixedCoupledGaussianCoeff sk s t σ‖ ≤ coupledGaussianLip n (mixedBeta ξ) := by
  have hq1 := s.q_le_one (show 1 ≤ k + 2 by omega)
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hv : ξ.value 1 ≤ (mixedBeta ξ) ^ 2 := by
    have hh := ξ.correction_nonneg (q := 1) (by norm_num)
    rw [ξ.correction_one, ← mixedBeta_sq ξ] at hh
    linarith
  have hbound : ‖mixedCoupledGaussianCoeff sk s t σ‖ ^ 2 ≤ (n : ℝ) * (mixedBeta ξ) ^ 2 := by
    rw [mixedCoupledGaussianCoeff_norm_sq sk s hn ht σ]
    have H := mul_le_mul_of_nonneg_left hq1
      (mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg (mixedBeta ξ)))
    have H' := mul_le_mul_of_nonneg_right H hN
    have H'' := mul_le_mul_of_nonneg_left hv (mul_nonneg ht.1 hN)
    nlinarith
  have hL := (coupledGaussianLip_pos hn (mixedBeta ξ)).le
  have hs := Real.sq_sqrt hN
  have ha : |mixedBeta ξ| ^ 2 = (mixedBeta ξ) ^ 2 := sq_abs _
  have hLsq : (n : ℝ) * (mixedBeta ξ) ^ 2 ≤ (coupledGaussianLip n (mixedBeta ξ)) ^ 2 := by
    unfold coupledGaussianLip
    rw [mul_pow, hs]
    nlinarith [mul_nonneg hN (abs_nonneg (mixedBeta ξ))]
  nlinarith [norm_nonneg (mixedCoupledGaussianCoeff sk s t σ)]

theorem mixed_guerraH_coupledGaussian_eq (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h t : ℝ) (a : Fin n → ℝ) (σ : Config n)
    (z : MixedCoupledGaussianSpace sk) :
    guerraH n (mixedCoupledGaussianU sk z) h t (a + mixedCoupledGaussianX sk s z) σ =
      inner ℝ (mixedCoupledGaussianCoeff sk s t σ) z +
        ∑ i, spin n σ i * (Real.sqrt (1 - t) * a i + h) := by
  simp only [guerraH, mixedCoupledGaussianU, mixedCoupledGaussianX, mixedCoupledGaussianCoeff,
    PiLp.inner_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    RCLike.inner_apply, conj_trivial, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, Pi.add_apply]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  simp only [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm]

theorem mixed_guerraH_coupledGaussian_lipschitz (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (a : Fin n → ℝ) (σ : Config n) :
    LipschitzWith (coupledGaussianLip n (mixedBeta ξ)).toNNReal
      (fun z => guerraH n (mixedCoupledGaussianU sk z) h t (a + mixedCoupledGaussianX sk s z) σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [mixed_guerraH_coupledGaussian_eq, add_sub_add_right_eq_sub,
    ← inner_sub_right, Real.coe_toNNReal _ (coupledGaussianLip_pos hn _).le, dist_eq_norm]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (mixedCoupledGaussianCoeff_norm_le sk s hn ht σ) (norm_nonneg _))

def mixedGaussianCoupledGap (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h t u : ℝ) (d j : ℕ) (z : MixedCoupledGaussianSpace sk) : ℝ :=
  coupledGap n s (mixedBeta ξ) (mixedCoupledGaussianU sk z) h t u d j (mixedCoupledGaussianX sk s z)

theorem mixedGaussianCoupledGap_lipschitz (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) :
    LipschitzWith (4 * coupledGaussianLip n (mixedBeta ξ)).toNNReal
      (mixedGaussianCoupledGap sk s h t u d j) := by
  have H := coupledGap_lipschitz s (mixedBeta ξ) h u ht hu d j
    (mixedCoupledGaussianU sk) (mixedCoupledGaussianX sk s)
    (mixed_guerraH_coupledGaussian_lipschitz sk s h hn ht)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [mixedGaussianCoupledGap, Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    Real.toNNReal_ofNat] using! H.dist_le_mul z w

theorem mixedGaussianCoupledGap_upper_tail (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)).real
      {z | a ≤ mixedGaussianCoupledGap sk s h t u d j z -
        ∫ w, mixedGaussianCoupledGap sk s h t u d j w
          ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)} ≤
      Real.exp (-a ^ 2 / (32 * (1 + |mixedBeta ξ|) ^ 2 * n)) := by
  have H := (SYK.product_standardGaussian_hasSubgaussianMGF (mixedGaussianCoupledGap sk s h t u d j)
    (4 * coupledGaussianLip n (mixedBeta ξ)) (mul_pos (by norm_num) (coupledGaussianLip_pos hn _))
    (mixedGaussianCoupledGap_lipschitz sk s h hn ht u hu d j)).measure_ge_le ha
  rw [Real.coe_toNNReal _ (sq_nonneg _)] at H
  have he : 2 * (4 * coupledGaussianLip n (mixedBeta ξ)) ^ 2 =
      32 * (1 + |mixedBeta ξ|) ^ 2 * n := by
    unfold coupledGaussianLip
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  rwa [he] at H

theorem integrable_mixedGaussianCoupledGap (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) :
    Integrable (mixedGaussianCoupledGap sk s h t u d j)
      (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) := by
  have H := (SYK.product_standardGaussian_hasSubgaussianMGF (mixedGaussianCoupledGap sk s h t u d j)
    (4 * coupledGaussianLip n (mixedBeta ξ)) (mul_pos (by norm_num) (coupledGaussianLip_pos hn (mixedBeta ξ)))
    (mixedGaussianCoupledGap_lipschitz sk s h hn ht u hu d j)).integrable
  simpa only [Pi.add_def, sub_add_cancel] using H.add (integrable_const
    (∫ z, mixedGaussianCoupledGap sk s h t u d j z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)))

/-- The weighted overlap event before the last, zero-mass Gaussian average. -/
noncomputable def mixedGaussianCoupledEvent (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h t u : ℝ) (d : ℕ) (z : MixedCoupledGaussianSpace sk) : ℝ :=
  coupledObservable n s (mixedBeta ξ) (mixedCoupledGaussianU sk z) h t d (overlapEvent n u) (k + 1)
    (mixedCoupledGaussianX sk s z) (mixedCoupledGaussianX sk s z)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem measurable_mixedGaussianCoupledEvent (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h t u : ℝ) (d : ℕ) : Measurable (mixedGaussianCoupledEvent sk s h t u d) := by
  have hU : Measurable (mixedCoupledGaussianU sk) := by unfold mixedCoupledGaussianU; fun_prop
  have hX : Measurable (mixedCoupledGaussianX sk s) := by unfold mixedCoupledGaussianX; fun_prop
  exact (measurable_coupledObservable_joint s (mixedBeta ξ) h t d (overlapEvent n u) (k + 1)).comp
    (f := fun z : MixedCoupledGaussianSpace sk =>
      (mixedCoupledGaussianU sk z, (mixedCoupledGaussianX sk s z, mixedCoupledGaussianX sk s z)))
    (hU.prodMk (hX.prodMk hX))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem integrable_mixedGaussianCoupledEvent (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) :
    Integrable (mixedGaussianCoupledEvent sk s h t u d)
      (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) := by
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_mixedGaussianCoupledEvent sk s h t u d).aestronglyMeasurable ?_
  filter_upwards with z
  unfold mixedGaussianCoupledEvent
  rw [Real.norm_of_nonneg (le_of_lt
    (coupledEvent_pos s hs (mixedBeta ξ) _ h u ht hu d (k + 1) (by omega) _ _))]
  exact coupledEvent_le_one s hs (mixedBeta ξ) _ h u ht hu d (k + 1) le_rfl _ _

/-- The concentration/expectation conclusion of Lemma 2.6 in standard Gaussian
coordinates. Its mean hypothesis and conclusion are transferred to `sk.U` in
`Targets.CoupledOuterExpectation`; this theorem does not assume a concentration bound. -/
theorem mixedGaussianCoupledEvent_small (sk : MixedDisorder (Ω := Ω) n ξ)
    (s : RSBScheme k) (h : ℝ) (hn : 0 < n) (hs : 0 < s.m 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hmean : (∫ z, mixedGaussianCoupledGap sk s h t u d (k + 1) z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) ≤ -ε * n) :
    (∫ z, mixedGaussianCoupledEvent sk s h t u d z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) ≤
      Real.exp (-(s.m 1 * ε / 4) * n) +
        Real.exp (-(ε ^ 2 / (128 * (1 + |(mixedBeta ξ)|) ^ 2)) * n) := by
  let μ := SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)
  let F := mixedGaussianCoupledGap sk s h t u d (k + 1)
  let Q := mixedGaussianCoupledEvent sk s h t u d
  have hF : Measurable F := (mixedGaussianCoupledGap_lipschitz sk s h hn ht u hu d (k + 1)).continuous.measurable
  have hm := coupledMass_pos s hs d (k + 1) le_rfl
  have hsplit := integral_event_le_exp_add_tail μ hF
    (measurable_mixedGaussianCoupledEvent sk s h t u d) hm.le
    (fun z => (coupledEvent_pos s hs (mixedBeta ξ) _ h u ht hu d (k + 1) (by omega) _ _).le)
    (fun z => coupledEvent_le_one s hs (mixedBeta ξ) _ h u ht hu d (k + 1) le_rfl _ _)
    (fun z => coupledEvent_le_exp_gap s hs (mixedBeta ξ) _ h u ht hu d (k + 1) le_rfl _ _)
    (r := ε * n / 2)
  have htail := mixedGaussianCoupledGap_upper_tail sk s h hn ht u hu d (k + 1)
    (a := ε * n / 2) (by positivity)
  have hset : {z | -(ε * n / 2) ≤ F z} ⊆ {z | ε * n / 2 ≤ F z - ∫ w, F w ∂μ} := by
    intro z hz
    try dsimp only [Set.mem_ofPred_eq] at hz ⊢
    change (∫ z, F z ∂μ) ≤ -ε * n at hmean
    linarith
  have hmass : s.m 1 / 2 ≤ coupledMass s d (k + 1) := by
    simp only [coupledMass, Nat.add_sub_cancel_left]
    split_ifs <;> linarith
  have hexp : Real.exp (-coupledMass s d (k + 1) * (ε * n / 2)) ≤
      Real.exp (-(s.m 1 * ε / 4) * n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hmass (show 0 ≤ ε * n by positivity)]
  have he : -(ε * (n : ℝ) / 2) ^ 2 / (32 * (1 + |(mixedBeta ξ)|) ^ 2 * n) =
      -(ε ^ 2 / (128 * (1 + |(mixedBeta ξ)|) ^ 2)) * n := by
    have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    have hb : (1 + |(mixedBeta ξ)|) ≠ 0 := by positivity
    field_simp
    ring
  rw [he] at htail
  exact hsplit.trans (add_le_add hexp ((measureReal_mono hset).trans htail))


end FourPapersCommon
