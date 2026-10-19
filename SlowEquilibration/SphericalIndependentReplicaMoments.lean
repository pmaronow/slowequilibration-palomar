-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalAnnealedGibbs
public import SlowEquilibration.IndependentReplicaTensorContraction
public import SlowEquilibration.SphericalOverlapPolynomialExponentialMoments

/-! Fixed tensor moments of two independent original disorder/Gibbs systems.
Only one-replica uniformity is used.  No overlap estimate for replicas with
common disorder is postulated.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalIndependentReplicaMoments

open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalAnnealedGibbs
open IndependentReplicaTensorContraction
open scoped BigOperators Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem spherePair_continuous_integrable {N : ℕ} (hN : 1 ≤ N)
    {f : Vector N × Vector N → ℝ} (hf : Continuous f) :
    Integrable f ((sphereLaw N).prod (sphereLaw N)) := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  have hs : ∀ᵐ z : Vector N × Vector N ∂(sphereLaw N).prod (sphereLaw N),
      ‖z.1‖ ^ 2 = (N : ℝ) ∧ ‖z.2‖ ^ 2 = (N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with x hx
    filter_upwards [sphereLaw_support hN] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rw [← hz.1, Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rw [← hz.2, Real.sqrt_sq (norm_nonneg z.2)]

/-- Every fixed unnormalized cross dot-product moment of independent
uniform sphere points has order at most N^(M/2), including odd M. -/
theorem sphere_pair_abs_inner_pow_eventually_bounded (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (∫ z : Vector N × Vector N, |inner ℝ z.1 z.2| ^ M
        ∂(sphereLaw N).prod (sphereLaw N)) ≤ C * (N : ℝ) ^ ((M : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := sphere_overlap_polynomial_eventually_bounded M
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with N hbound hN
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hi : Integrable (fun z : Vector N × Vector N => |overlap z.1 z.2| ^ M)
      ((sphereLaw N).prod (sphereLaw N)) := by
    apply spherePair_continuous_integrable hN
    unfold overlap
    fun_prop
  have hpair : (∫ z : Vector N × Vector N, |overlap z.1 z.2| ^ M
      ∂(sphereLaw N).prod (sphereLaw N)) ≤ C * (N : ℝ) ^ (-(M : ℝ) / 2) := by
    rw [integral_prod _ hi]
    calc
      _ ≤ ∫ _x : Vector N, C * (N : ℝ) ^ (-(M : ℝ) / 2) ∂sphereLaw N := by
        apply integral_mono_of_nonneg
          (.of_forall fun _ => integral_nonneg fun _ => by positivity) (integrable_const _)
        filter_upwards [sphereLaw_support hN] with x hx
        exact (hbound x hx).2
      _ = _ := by simp
  have he (z : Vector N × Vector N) :
      |inner ℝ z.1 z.2| ^ M = (N : ℝ) ^ M * |overlap z.1 z.2| ^ M := by
    have heq : inner ℝ z.1 z.2 = (N : ℝ) * overlap z.1 z.2 := by
      unfold overlap
      field_simp
    rw [heq, abs_mul, abs_of_pos hNp, mul_pow]
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ ≤ (N : ℝ) ^ M * (C * (N : ℝ) ^ (-(M : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = C * (N : ℝ) ^ ((M : ℝ) / 2) := by
      rw [show (N : ℝ) ^ M * (C * (N : ℝ) ^ (-(M : ℝ) / 2)) =
        C * ((N : ℝ) ^ M * (N : ℝ) ^ (-(M : ℝ) / 2)) by ring,
        ← Real.rpow_natCast, ← Real.rpow_add hNp]
      congr 2
      ring

/-- Individual cross-pair moments are unchanged if arbitrary replicas are
selected from two independent original disorder/Gibbs systems. -/
theorem independent_replica_abs_inner_pow_integral {N r s : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (i : Fin r) (j : Fin s) (M : ℕ) :
    (∫ z : (Fin r → Vector N) × (Fin s → Vector N), |inner ℝ (z.1 i) (z.2 j)| ^ M
      ∂(annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β s)) =
    ∫ z : Vector N × Vector N, |inner ℝ z.1 z.2| ^ M
      ∂(sphereLaw N).prod (sphereLaw N) := by
  simpa only [Function.comp_apply] using
    (independent_annealedReplica_pair_hasLaw hN μ β i j).integral_comp
      (f := fun z : Vector N × Vector N => |inner ℝ z.1 z.2| ^ M) (by fun_prop)

/-- Mixed moments keep their total tensor degree with no independence
requirement among the selected cross pairs.  The finite number of factors
and all replica labels are uniform in the dimension estimate. -/
theorem independent_replica_mixed_moment_eventually_bounded
    (k : ℕ) [NeZero k] (p : Fin k → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (r s : ℕ)
        (i : Fin k → Fin r) (j : Fin k → Fin s),
      (∫ z : (Fin r → Vector N) × (Fin s → Vector N),
        ∏ a, |inner ℝ (z.1 (i a)) (z.2 (j a))| ^ p a
        ∂(annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β s)) ≤
          C * (N : ℝ) ^ (((∑ a, p a : ℕ) : ℝ) / 2) := by
  let M : ℕ := ∑ a, p a
  obtain ⟨C, hC, hbound⟩ := sphere_pair_abs_inner_pow_eventually_bounded M
  refine ⟨(k : ℝ) * C, mul_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero k)) hC, ?_⟩
  filter_upwards [hbound] with N hbound
  intro hN μ β r s i j
  let ν := (annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β s)
  have hi (a : Fin k) : Integrable
      (fun z : (Fin r → Vector N) × (Fin s → Vector N) =>
        |inner ℝ (z.1 (i a)) (z.2 (j a))| ^ M) ν := by
    exact (independent_annealedReplica_pair_hasLaw hN μ β (i a) (j a)).integrable_fun_comp
      (f := fun z : Vector N × Vector N => |inner ℝ z.1 z.2| ^ M)
      (spherePair_continuous_integrable hN (by fun_prop))
  calc
    _ ≤ ∫ z : (Fin r → Vector N) × (Fin s → Vector N),
        ∑ a : Fin k, |inner ℝ (z.1 (i a)) (z.2 (j a))| ^ M ∂ν := by
      apply integral_mono_of_nonneg
        (.of_forall fun _ => Finset.prod_nonneg fun _ _ => by positivity)
        (integrable_finsetSum _ fun a _ => hi a)
      exact .of_forall fun z => prod_pow_le_sum_pow_total
        (fun a => |inner ℝ (z.1 (i a)) (z.2 (j a))|) p (fun _ => abs_nonneg _)
    _ = ∑ a : Fin k, ∫ z : (Fin r → Vector N) × (Fin s → Vector N),
        |inner ℝ (z.1 (i a)) (z.2 (j a))| ^ M ∂ν :=
      integral_finsetSum _ fun a _ => hi a
    _ ≤ ∑ _a : Fin k, C * (N : ℝ) ^ ((M : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro a _
      change (∫ z : (Fin r → Vector N) × (Fin s → Vector N),
        |inner ℝ (z.1 (i a)) (z.2 (j a))| ^ M
        ∂(annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β s)) ≤ _
      rw [independent_replica_abs_inner_pow_integral]
      exact hbound
    _ = _ := by simp [M, mul_assoc]

/-- Every unrestricted ordered replicated tensor monomial is integrable
under the actual disorder-averaged Gibbs law. -/
theorem replicaMonomial_integrable {α : Type*} [Fintype α] {N r : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (labels : α → Fin r)
    (I : α → Fin N) :
    Integrable (fun σ : Fin r → Vector N =>
      replicaMonomial labels (fun a i => σ a i) I) (annealedReplicaLaw hN μ β r) := by
  have hs (a : α) : ∀ᵐ σ ∂annealedReplicaLaw hN μ β r,
      ‖σ (labels a)‖ ^ 2 = (N : ℝ) := by
    have h := sphereLaw_support hN
    rw [← (annealedReplica_eval_hasLaw hN μ β (labels a)).map_eq] at h
    exact ae_of_ae_map (measurable_pi_apply (labels a)).aemeasurable h
  have hm : Continuous (fun σ : Fin r → Vector N =>
      replicaMonomial labels (fun a i => σ a i) I) := by
    unfold replicaMonomial
    apply continuous_finset_prod
    intro a _
    exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) (I a)).comp
      (continuous_apply (labels a))
  apply Integrable.of_bound hm.aestronglyMeasurable ((Real.sqrt N) ^ Fintype.card α)
  filter_upwards [ae_all_iff.mpr hs] with σ hσ
  rw [Real.norm_eq_abs, replicaMonomial, Finset.abs_prod]
  calc
    _ ≤ ∏ _a : α, Real.sqrt N := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro a _
      have hn : ‖σ (labels a)‖ = Real.sqrt N := by
        rw [← hσ a, Real.sqrt_sq (norm_nonneg _)]
      simpa only [hn, Real.norm_eq_abs] using PiLp.norm_apply_le (σ (labels a)) (I a)
    _ = _ := by simp

/-- The same fixed-order estimate with an arbitrary finite type of
physical tensor slots.  In particular the slots can be the dependent sum
of the indices of all derivative degrees, with no reindexing to `Fin`. -/
theorem normalized_replica_tensor_mean_square_eventually_bounded_of_fintype
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
    (k : ℕ) (hdegree : 2 * k ≤ Fintype.card α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (r : ℕ) (labels : α → Fin r),
      (N : ℝ) ^ (-((Fintype.card α - k : ℕ) : ℝ)) *
        (∑ I : α → Fin N,
          (∫ σ : Fin r → Vector N, replicaMonomial labels (fun a i => σ a i) I
            ∂annealedReplicaLaw hN μ β r) ^ 2) ≤ C := by
  let M := Fintype.card α
  obtain ⟨C, hC, hbound⟩ := sphere_pair_abs_inner_pow_eventually_bounded M
  have hM : 0 < (M : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨(M : ℝ) * C, mul_pos hM hC, ?_⟩
  filter_upwards [hbound] with N hbound
  intro hN μ β r labels
  let ν := annealedReplicaLaw hN μ β r
  have hmean := sum_square_integral_replicaMonomial ν labels
    (fun (σ : Fin r → Vector N) a i => σ a i)
    (fun I => replicaMonomial_integrable hN μ β labels I)
  have hi (a : α) : Integrable
      (fun z : (Fin r → Vector N) × (Fin r → Vector N) =>
        |inner ℝ (z.1 (labels a)) (z.2 (labels a))| ^ M) (ν.prod ν) := by
    exact (independent_annealedReplica_pair_hasLaw hN μ β (labels a) (labels a)).integrable_fun_comp
      (f := fun z : Vector N × Vector N => |inner ℝ z.1 z.2| ^ M)
      (spherePair_continuous_integrable hN (by fun_prop))
  have hraw :
      (∑ I : α → Fin N,
        (∫ σ : Fin r → Vector N, replicaMonomial labels (fun a i => σ a i) I ∂ν) ^ 2) ≤
      ((M : ℝ) * C) * (N : ℝ) ^ ((M : ℝ) / 2) := by
    rw [hmean]
    calc
      _ ≤ ∫ z : (Fin r → Vector N) × (Fin r → Vector N),
          ∏ a : α, |inner ℝ (z.1 (labels a)) (z.2 (labels a))| ∂ν.prod ν := by
        apply le_trans ((le_abs_self _).trans abs_integral_le_integral_abs)
        apply le_of_eq
        apply integral_congr_ae
        exact .of_forall fun z => by
          change |∏ a : α, ∑ i : Fin N, z.1 (labels a) i * z.2 (labels a) i| =
            ∏ a : α, |inner ℝ (z.1 (labels a)) (z.2 (labels a))|
          rw [Finset.abs_prod]
          apply Finset.prod_congr rfl
          intro a _
          congr 1
          simp [PiLp.inner_apply, mul_comm]
      _ ≤ ∫ z : (Fin r → Vector N) × (Fin r → Vector N),
          ∑ a : α, |inner ℝ (z.1 (labels a)) (z.2 (labels a))| ^ M ∂ν.prod ν := by
        apply integral_mono_of_nonneg
          (.of_forall fun _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
          (integrable_finsetSum _ fun a _ => hi a)
        exact .of_forall fun z => by
          simpa only [pow_one, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_one]
            using prod_pow_le_sum_pow_total
              (fun a : α => |inner ℝ (z.1 (labels a)) (z.2 (labels a))|)
              (fun _ => 1) (fun _ => abs_nonneg _)
      _ = ∑ a : α, ∫ z : (Fin r → Vector N) × (Fin r → Vector N),
          |inner ℝ (z.1 (labels a)) (z.2 (labels a))| ^ M ∂ν.prod ν :=
        integral_finsetSum _ fun a _ => hi a
      _ ≤ ∑ _a : α, C * (N : ℝ) ^ ((M : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro a _
        change (∫ z : (Fin r → Vector N) × (Fin r → Vector N),
          |inner ℝ (z.1 (labels a)) (z.2 (labels a))| ^ M
          ∂(annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β r)) ≤ _
        rw [independent_replica_abs_inner_pow_integral]
        exact hbound
      _ = _ := by simp [M, mul_assoc]
  calc
    _ ≤ (N : ℝ) ^ (-((M - k : ℕ) : ℝ)) *
        (((M : ℝ) * C) * (N : ℝ) ^ ((M : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = ((M : ℝ) * C) * ((N : ℝ) ^ (-((M - k : ℕ) : ℝ)) *
        (N : ℝ) ^ ((M : ℝ) / 2)) := by ring
    _ ≤ ((M : ℝ) * C) * 1 := mul_le_mul_of_nonneg_left
      (normalized_cross_moment_scale_le_one (by exact_mod_cast hN) M k hdegree)
      (mul_nonneg hM.le hC.le)
    _ = _ := mul_one _

/-- The normalized squared mean of every fixed replicated tensor
monomial is bounded independently of the dimension.  All tensor indices,
including repetitions, are summed.  This is the model-specific estimate
needed for each monomial in the fixed-order Gibbs derivative expansion. -/
theorem normalized_replica_tensor_mean_square_eventually_bounded
    (M k : ℕ) [NeZero M] (hdegree : 2 * k ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (r : ℕ)
        (labels : Fin M → Fin r),
      (N : ℝ) ^ (-((M - k : ℕ) : ℝ)) *
        (∑ I : Fin M → Fin N,
          (∫ σ : Fin r → Vector N, replicaMonomial labels (fun a i => σ a i) I
            ∂annealedReplicaLaw hN μ β r) ^ 2) ≤ C := by
  simpa only [Fintype.card_fin] using
    normalized_replica_tensor_mean_square_eventually_bounded_of_fintype
      (Fin M) k (by simpa only [Fintype.card_fin] using hdegree)

end SlowEquilibration.SphericalIndependentReplicaMoments
