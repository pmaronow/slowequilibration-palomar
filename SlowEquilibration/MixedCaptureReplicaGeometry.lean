-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.DirectingPhysicalNorm
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact finite-replica mean geometry in the coarse-cover proof. The
diagonal correction is Q + (1-Q)/n, rather than Q. The statements apply
to genuine normalized spin vectors in an arbitrary real Hilbert space,
so physical spins are obtained by division by the sphere radius. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.MixedCaptureReplicaGeometry

open Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def replicaMean {n : ℕ} (σ : Fin n → H) : H := (n : ℝ)⁻¹ • ∑ i, σ i

def correctedNormSq (Q : ℝ) (n : ℕ) : ℝ := Q + (1 - Q) / (n : ℝ)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Actual uniform finite averages preserve a uniform error bound. -/
theorem average_sub_average_abs_le {n : ℕ} (hn : 0 < n)
    (f g : Fin n → ℝ) {θ : ℝ} (hfg : ∀ i, |f i - g i| ≤ θ) :
    |(n : ℝ)⁻¹ * ∑ i, f i - (n : ℝ)⁻¹ * ∑ i, g i| ≤ θ := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : |∑ i : Fin n, (f i - g i)| ≤ (n : ℝ) * θ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin n, θ := Finset.sum_le_sum fun i hi => hfg i
      _ = _ := by simp
  calc
    _ = |(n : ℝ)⁻¹ * ∑ i : Fin n, (f i - g i)| := by
      rw [Finset.sum_sub_distrib, mul_sub]
    _ = (n : ℝ)⁻¹ * |∑ i : Fin n, (f i - g i)| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hnreal.le)]
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * θ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = θ := by field_simp

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- The exact average of the diagonal-one/off-diagonal-Q model row. -/
theorem ideal_row_average {n : ℕ} (hn : 0 < n) (Q : ℝ) (i : Fin n) :
    (n : ℝ)⁻¹ * (∑ j : Fin n, if i = j then (1 : ℝ) else Q) = correctedNormSq Q n := by
  classical
  have hsplit (j : Fin n) : (if i = j then (1 : ℝ) else Q) =
      Q + (if i = j then 1 - Q else 0) := by split_ifs <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hone : (∑ j : Fin n, if i = j then 1 - Q else 0) = 1 - Q := by simp
  rw [hone]
  unfold correctedNormSq
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

theorem replicaMean_inner_right {n : ℕ} (σ : Fin n → H) (v : H) :
    inner ℝ v (replicaMean σ) = (n : ℝ)⁻¹ * ∑ j, inner ℝ v (σ j) := by
  rw [replicaMean, real_inner_smul_right, inner_sum]

theorem replicaMean_norm_sq {n : ℕ} (σ : Fin n → H) :
    ‖replicaMean σ‖ ^ 2 = (n : ℝ)⁻¹ * ∑ i, inner ℝ (σ i) (replicaMean σ) := by
  rw [← real_inner_self_eq_norm_sq, replicaMean, real_inner_smul_left, sum_inner]

/-- Every replica's overlap with its true finite average is close to
the exact diagonal-corrected value. -/
theorem replicaMean_row_error {n : ℕ} (hn : 0 < n) (σ : Fin n → H)
    (hσ : ∀ i, ‖σ i‖ ^ 2 = 1) {Q θ : ℝ} (hθ : 0 ≤ θ)
    (hpair : ∀ i j, i ≠ j → |inner ℝ (σ i) (σ j) - Q| ≤ θ) (i : Fin n) :
    |inner ℝ (σ i) (replicaMean σ) - correctedNormSq Q n| ≤ θ := by
  rw [replicaMean_inner_right, ← ideal_row_average hn Q i]
  apply average_sub_average_abs_le hn
  intro j
  by_cases hij : i = j
  · subst j
    simpa [real_inner_self_eq_norm_sq, hσ i] using hθ
  · rw [ite_eq_right hij]
    exact hpair i j hij

/-- The squared norm of the empirical mean includes the 1/n diagonal
contribution. This is the first bound in source equation mb-diagonal. -/
theorem replicaMean_norm_sq_error {n : ℕ} (hn : 0 < n) (σ : Fin n → H)
    (hσ : ∀ i, ‖σ i‖ ^ 2 = 1) {Q θ : ℝ} (hθ : 0 ≤ θ)
    (hpair : ∀ i j, i ≠ j → |inner ℝ (σ i) (σ j) - Q| ≤ θ) :
    |‖replicaMean σ‖ ^ 2 - correctedNormSq Q n| ≤ θ := by
  rw [replicaMean_norm_sq]
  have havg : (n : ℝ)⁻¹ * (∑ _ : Fin n, correctedNormSq Q n) = correctedNormSq Q n := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  rw [← havg]
  exact average_sub_average_abs_le hn _ _ (replicaMean_row_error hn σ hσ hθ hpair)

/-- The distinguished Gibbs sample's overlap with the finite mean is
the average of its overlaps with the companions. -/
theorem query_replicaMean_error {n : ℕ} (hn : 0 < n) (σ : Fin n → H)
    (v : H) {Q θ : ℝ} (hquery : ∀ i, |inner ℝ v (σ i) - Q| ≤ θ) :
    |inner ℝ v (replicaMean σ) - Q| ≤ θ := by
  rw [replicaMean_inner_right]
  have havg : (n : ℝ)⁻¹ * (∑ _ : Fin n, Q) = Q := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  rw [← havg]
  exact average_sub_average_abs_le hn _ _ hquery

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem correctedNormSq_ge {Q : ℝ} (hQ : Q ≤ 1) {n : ℕ} (_hn : 0 < n) :
    Q ≤ correctedNormSq Q n := by
  unfold correctedNormSq
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hQ) (Nat.cast_nonneg _))

/-- The actual empirical mean is nonzero under the source small-overlap
tolerance; no mean-norm positivity is assumed. -/
theorem replicaMean_ne_zero {n : ℕ} (hn : 0 < n) (σ : Fin n → H)
    (hσ : ∀ i, ‖σ i‖ ^ 2 = 1) {Q θ : ℝ} (hQ : Q ≤ 1)
    (hθ : 0 ≤ θ) (hθQ : θ < Q)
    (hpair : ∀ i j, i ≠ j → |inner ℝ (σ i) (σ j) - Q| ≤ θ) : replicaMean σ ≠ 0 := by
  have herr := (abs_le.mp (replicaMean_norm_sq_error hn σ hσ hθ hpair)).1
  have hqn := correctedNormSq_ge hQ hn
  intro hz
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub] at herr
  linarith

def normalizedReplicaMean {n : ℕ} (σ : Fin n → H) : H := ‖replicaMean σ‖⁻¹ • replicaMean σ

/-- The empirical mean rescaled to the source contact sphere. -/
def contactReplicaMean {n : ℕ} (Q : ℝ) (σ : Fin n → H) : H :=
  Real.sqrt Q • normalizedReplicaMean σ

/-- The normalized empirical mean lies on the genuine unit sphere. -/
theorem normalizedReplicaMean_norm {n : ℕ} (σ : Fin n → H) (hmean : replicaMean σ ≠ 0) :
    ‖normalizedReplicaMean σ‖ = 1 := by
  rw [normalizedReplicaMean, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hmean)

theorem contactReplicaMean_norm_sq {n : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (σ : Fin n → H) (hmean : replicaMean σ ≠ 0) : ‖contactReplicaMean Q σ‖ ^ 2 = Q := by
  rw [contactReplicaMean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg Q),
    normalizedReplicaMean_norm σ hmean, mul_one, Real.sq_sqrt hQ]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- The scalar square-root error used in the exact-latitude projection. -/
theorem contact_sqrt_error_le {Q r : ℝ} (hQ : 0 ≤ Q) (hr : 0 ≤ r) :
    |Real.sqrt Q * r - Q| ≤ |r ^ 2 - Q| := by
  have ha := Real.sqrt_nonneg Q
  calc
    _ = |Real.sqrt Q * (r - Real.sqrt Q)| := by rw [mul_sub, ← sq, Real.sq_sqrt hQ]
    _ = Real.sqrt Q * |r - Real.sqrt Q| := by rw [abs_mul, abs_of_nonneg ha]
    _ ≤ (r + Real.sqrt Q) * |r - Real.sqrt Q| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = |(r + Real.sqrt Q) * (r - Real.sqrt Q)| := by
      rw [abs_mul, abs_of_nonneg (add_nonneg hr ha)]
    _ = _ := by congr 1; nlinarith [Real.sq_sqrt hQ]

/-- The third bound of source equation mb-diagonal, with an explicit
constant. The diagonal correction contributes the separate 1/n term. -/
theorem contactReplicaMean_row_error {n : ℕ} (hn : 0 < n) (σ : Fin n → H)
    (hσ : ∀ i, ‖σ i‖ ^ 2 = 1) {Q θ : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 ≤ θ) (hθQ : θ < Q / 2)
    (hpair : ∀ i j, i ≠ j → |inner ℝ (σ i) (σ j) - Q| ≤ θ) (i : Fin n) :
    |inner ℝ (σ i) (contactReplicaMean Q σ) - Q| ≤
      (2 * Real.sqrt 2 + 1) * θ + 1 / (n : ℝ) := by
  let r := ‖replicaMean σ‖
  let a := Real.sqrt Q
  let qn := correctedNormSq Q n
  have hmean := replicaMean_ne_zero hn σ hσ hQ.2.le hθ (by linarith [hQ.1]) hpair
  have hr : 0 < r := norm_pos_iff.mpr hmean
  have ha : 0 ≤ a := Real.sqrt_nonneg Q
  have hnorm := replicaMean_norm_sq_error hn σ hσ hθ hpair
  have hrow := replicaMean_row_error hn σ hσ hθ hpair i
  have hqn := correctedNormSq_ge hQ.2.le hn
  have hmargin : Q / 2 ≤ r ^ 2 := by
    have hlower := (abs_le.mp hnorm).1
    change -θ ≤ r ^ 2 - qn at hlower
    change Q ≤ qn at hqn
    linarith
  have hrat : a / r ≤ Real.sqrt 2 := by
    apply (div_le_iff₀ hr).mpr
    apply (sq_le_sq₀ ha (mul_nonneg (Real.sqrt_nonneg 2) hr.le)).mp
    have ha2 : a ^ 2 = Q := Real.sq_sqrt hQ.1.le
    rw [mul_pow, ha2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hrowbar : |inner ℝ (σ i) (replicaMean σ) - r ^ 2| ≤ 2 * θ := by
    have ht := abs_sub_le (inner ℝ (σ i) (replicaMean σ)) qn (r ^ 2)
    have hn' : |qn - r ^ 2| ≤ θ := by simpa only [abs_sub_comm] using hnorm
    linarith
  have hraw : |r ^ 2 - Q| ≤ θ + 1 / (n : ℝ) := by
    have ht := abs_sub_le (r ^ 2) qn Q
    have hqnabs : |qn - Q| = (1 - Q) / (n : ℝ) := by
      dsimp [qn, correctedNormSq]
      rw [add_sub_cancel_left, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hQ.2.le) (Nat.cast_nonneg _))]
    have hfrac : (1 - Q) / (n : ℝ) ≤ 1 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by linarith [hQ.1]) (Nat.cast_nonneg _)
    rw [hqnabs] at ht
    linarith
  have hsqrt := contact_sqrt_error_le hQ.1.le hr.le
  change |a * r - Q| ≤ |r ^ 2 - Q| at hsqrt
  have heq : inner ℝ (σ i) (contactReplicaMean Q σ) - Q =
      (a / r) * (inner ℝ (σ i) (replicaMean σ) - r ^ 2) + (a * r - Q) := by
    rw [contactReplicaMean, normalizedReplicaMean, real_inner_smul_right, real_inner_smul_right]
    change a * (r⁻¹ * inner ℝ (σ i) (replicaMean σ)) - Q = _
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(a / r) * (inner ℝ (σ i) (replicaMean σ) - r ^ 2)| + |a * r - Q| := abs_add_le _ _
    _ = (a / r) * |inner ℝ (σ i) (replicaMean σ) - r ^ 2| + |a * r - Q| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg ha hr.le)]
    _ ≤ Real.sqrt 2 * (2 * θ) + (θ + 1 / (n : ℝ)) :=
      add_le_add (mul_le_mul hrat hrowbar (abs_nonneg _) (Real.sqrt_nonneg 2)) (hsqrt.trans hraw)
    _ = _ := by ring

/-- For each fixed group size, an overlap tolerance is chosen before
the replicas. The normalized mean's query overlap is then as close as
desired to Q/sqrt(Q+(1-Q)/n), retaining the source diagonal correction. -/
theorem exists_normalizedMean_query_tolerance {n : ℕ} (hn : 0 < n)
    {Q b : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) (hb : 0 < b) :
    ∃ θ > (0 : ℝ), θ < Q ∧ ∀ (σ : Fin n → H) (v : H),
      (∀ i, ‖σ i‖ ^ 2 = 1) →
      (∀ i j, i ≠ j → |inner ℝ (σ i) (σ j) - Q| ≤ θ) →
      (∀ i, |inner ℝ v (σ i) - Q| ≤ θ) →
      ‖normalizedReplicaMean σ‖ = 1 ∧
        |inner ℝ v (normalizedReplicaMean σ) - Q / Real.sqrt (correctedNormSq Q n)| < b := by
  let qn := correctedNormSq Q n
  have hqnpos : 0 < qn := hQ.1.trans_le (correctedNormSq_ge hQ.2.le hn)
  have hcont : ContinuousAt (fun p : ℝ × ℝ => p.2 / Real.sqrt p.1) (qn, Q) :=
    continuous_snd.continuousAt.div
      (Real.continuous_sqrt.continuousAt.comp continuous_fst.continuousAt)
      (Real.sqrt_ne_zero'.mpr hqnpos)
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.continuousAt_iff.mp hcont b hb
  let θ := min (δ / 2) (Q / 2)
  have hθpos : 0 < θ := lt_min (by positivity) (div_pos hQ.1 (by norm_num))
  have hθQ : θ < Q := (min_le_right _ _).trans_lt (by linarith [hQ.1])
  refine ⟨θ, hθpos, hθQ, ?_⟩
  intro σ v hσ hpair hquery
  have hmean := replicaMean_ne_zero hn σ hσ hQ.2.le hθpos.le hθQ hpair
  refine ⟨normalizedReplicaMean_norm σ hmean, ?_⟩
  have hnorm := replicaMean_norm_sq_error hn σ hσ hθpos.le hpair
  have hquerymean := query_replicaMean_error hn σ v hquery
  have hdist : dist (‖replicaMean σ‖ ^ 2, inner ℝ v (replicaMean σ)) (qn, Q) ≤ θ := by
    rw [Prod.dist_eq]
    exact max_le (by simpa only [Real.dist_eq] using hnorm)
      (by simpa only [Real.dist_eq] using hquerymean)
  have hδθ : θ < δ := (min_le_left _ _).trans_lt (by linarith)
  have hout := hcontrol (hdist.trans_lt hδθ)
  have heq : inner ℝ v (normalizedReplicaMean σ) =
      inner ℝ v (replicaMean σ) / Real.sqrt (‖replicaMean σ‖ ^ 2) := by
    rw [normalizedReplicaMean, real_inner_smul_right, Real.sqrt_sq (norm_nonneg _)]
    ring
  rw [heq]
  simpa only [Real.dist_eq] using hout

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem correctedNormSq_tendsto (Q : ℝ) :
    Tendsto (correctedNormSq Q) atTop (𝓝 Q) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (1 - Q)).const_add Q
  change Tendsto (fun n : ℕ => Q + (1 - Q) / (n : ℝ)) atTop (𝓝 Q)
  simpa only [add_zero] using h

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem corrected_query_tendsto {Q : ℝ} (hQ : 0 < Q) :
    Tendsto (fun n => Q / Real.sqrt (correctedNormSq Q n)) atTop (𝓝 (Real.sqrt Q)) := by
  have h := (tendsto_const_nhds (x := Q)).div
    (Real.continuous_sqrt.continuousAt.tendsto.comp (correctedNormSq_tendsto Q))
    (Real.sqrt_ne_zero'.mpr hQ)
  have heq : Q / Real.sqrt Q = Real.sqrt Q := by
    apply (div_eq_iff (Real.sqrt_ne_zero'.mpr hQ)).mpr
    exact (Real.mul_self_sqrt hQ.le).symm
  rw [heq] at h
  apply h.congr
  exact fun n => Pi.div_apply _ _ n

/-- All geometric parameters are chosen before the replicas. A
sufficiently coherent group places the query in
the latitude-sqrt-Q band of any center sufficiently near its true mean. -/
theorem replica_cluster_to_band_parameters {Q b : ℝ}
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hb : 0 < b) (n₀ : ℕ) :
    ∃ n ≥ n₀, 0 < n ∧ ∃ θ > (0 : ℝ), θ < Q ∧
      ∀ (σ : Fin n → H) (v c : H),
        (∀ i, ‖σ i‖ ^ 2 = 1) → ‖v‖ ≤ 1 →
        (∀ i j, i ≠ j → |inner ℝ (σ i) (σ j) - Q| ≤ θ) →
        (∀ i, |inner ℝ v (σ i) - Q| ≤ θ) →
        ‖c - normalizedReplicaMean σ‖ < b / 2 →
        ‖normalizedReplicaMean σ‖ = 1 ∧ |inner ℝ v c - Real.sqrt Q| < b := by
  have hlarge : ∀ᶠ n : ℕ in atTop,
      |Q / Real.sqrt (correctedNormSq Q n) - Real.sqrt Q| < b / 4 := by
    have h := (corrected_query_tendsto hQ.1).eventually
      (Metric.ball_mem_nhds _ (by linarith : 0 < b / 4))
    simpa only [Metric.mem_ball, Real.dist_eq] using h
  obtain ⟨n, hnmin, hnlarge⟩ :=
    (hlarge.and (eventually_ge_atTop (max n₀ 1))).exists
  have hn0 : 0 < n := by omega
  have hnn₀ : n₀ ≤ n := (le_max_left _ _).trans hnlarge
  obtain ⟨θ, hθ, hθQ, hcontrol⟩ := exists_normalizedMean_query_tolerance
    (H := H) hn0 hQ (by linarith : 0 < b / 4)
  refine ⟨n, hnn₀, hn0, θ, hθ, hθQ, ?_⟩
  intro σ v c hσ hv hpair hquery hc
  obtain ⟨hunit, herr⟩ := hcontrol σ v hσ hpair hquery
  refine ⟨hunit, ?_⟩
  have hmove : |inner ℝ v c - inner ℝ v (normalizedReplicaMean σ)| < b / 2 := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans_lt
      ((mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans_lt (by simpa only [one_mul] using hc))
  have h1 := abs_sub_le (inner ℝ v c) (inner ℝ v (normalizedReplicaMean σ)) (Real.sqrt Q)
  have h2 := abs_sub_le (inner ℝ v (normalizedReplicaMean σ))
    (Q / Real.sqrt (correctedNormSq Q n)) (Real.sqrt Q)
  linarith

end SlowEquilibration.MixedCaptureReplicaGeometry
