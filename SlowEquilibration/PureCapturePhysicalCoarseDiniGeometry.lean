-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFiniteEnsembleTransfer

/-! Dimension-uniform finite-replica geometry for the actual coarse cover.
The replica count is selected first, then one scalar overlap tolerance is
chosen before every physical dimension and every realized replica tuple. -/

@[expose] public section
namespace SlowEquilibration.PureCapturePhysicalCoarseDiniGeometry
noncomputable section
open Set Filter SphericalModel SphericalForm
open SphericalAging.HardSphereDynamics SphericalBarycenter MixedCaptureReplicaGeometry
open PureCapturePhysicalCoarseTransfer PureCapturePhysicalFiniteEnsembleTransfer
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem physicalTrainingCenter_query_tolerance_all_dimensions
    {k : ℕ} (hk : 0 < k) {Q a₁ : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (ha₁ : a₁ < Q/Real.sqrt (correctedNormSq Q k)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Q ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ (x : Vector N) (σ : Fin k → Vector N),
        OnSphere x → (∀ i, OnSphere (σ i)) → goodCompanionBlock Q θ x σ →
        ‖physicalTrainingCenter σ‖^2=(N:ℝ) ∧
          a₁ < overlap x (physicalTrainingCenter σ) := by
  let qk := correctedNormSq Q k
  let b := (Q/Real.sqrt qk-a₁)/2
  have hqk : 0 < qk := hQ.1.trans_le (correctedNormSq_ge hQ.2.le hk)
  have hb : 0 < b := half_pos (sub_pos.mpr ha₁)
  have hcont : ContinuousAt (fun p : ℝ×ℝ => p.2/Real.sqrt p.1) (qk,Q) :=
    continuous_snd.continuousAt.div
      (Real.continuous_sqrt.continuousAt.comp continuous_fst.continuousAt)
      (Real.sqrt_ne_zero'.mpr hqk)
  obtain ⟨ε,hε,hcontrol⟩ := Metric.continuousAt_iff.mp hcont b hb
  let θ := min (ε/2) (Q/2)
  have hθ : 0 < θ := lt_min (half_pos hε) (half_pos hQ.1)
  have hθQ : θ < Q := (min_le_right _ _).trans_lt (by linarith [hQ.1])
  have hθε : θ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨θ,hθ,hθQ,?_⟩
  intro N hN x σ hx hσ hgood
  have hunit (i : Fin k) : ‖spin (σ i)‖^2=1 := by
    rw [spin_norm hN _ (hσ i),one_pow]
  have hpair : ∀ i j : Fin k, i ≠ j →
      |inner ℝ (spin (σ i)) (spin (σ j))-Q| ≤ θ := by
    intro i j hij
    simpa only [spin_inner hN] using (hgood.1 i j hij).le
  have hquery : ∀ i : Fin k, |inner ℝ (spin x) (spin (σ i))-Q| ≤ θ := by
    intro i
    simpa only [spin_inner hN] using (hgood.2 i).le
  have hnorm := replicaMean_norm_sq_error hk (fun i => spin (σ i)) hunit hθ.le hpair
  have hmean := query_replicaMean_error hk (fun i => spin (σ i)) (spin x) hquery
  have hdist : dist (‖replicaMean (fun i => spin (σ i))‖^2,
      inner ℝ (spin x) (replicaMean (fun i => spin (σ i)))) (qk,Q) ≤ θ := by
    rw [Prod.dist_eq]
    exact max_le (by simpa only [Real.dist_eq] using hnorm)
      (by simpa only [Real.dist_eq] using hmean)
  have hout := hcontrol (hdist.trans_lt hθε)
  have hsphere := physicalTrainingCenter_sphere hN hk σ hσ hQ hθ.le hθQ
    (fun i j hij => (hgood.1 i j hij).le)
  refine ⟨hsphere,?_⟩
  have heq : overlap x (physicalTrainingCenter σ) =
      inner ℝ (spin x) (replicaMean (fun i => spin (σ i)))/
        Real.sqrt (‖replicaMean (fun i => spin (σ i))‖^2) := by
    rw [←spin_inner hN,spin_physicalTrainingCenter hN,
      normalizedReplicaMean,real_inner_smul_right,Real.sqrt_sq (norm_nonneg _)]
    ring
  have habs : |inner ℝ (spin x) (replicaMean (fun i => spin (σ i)))/
      Real.sqrt (‖replicaMean (fun i => spin (σ i))‖^2)-Q/Real.sqrt qk| < b := by
    simpa only [Real.dist_eq] using hout
  rw [heq]
  dsimp only [b] at habs
  linarith [(abs_lt.mp habs).1]

/-- Every lower bound on group size can be met before choosing a common
overlap tolerance. The corrected finite diagonal tends to Q. -/
theorem exists_replica_count_and_dimension_uniform_tolerance
    {Q a₁ : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1) (ha₁ : a₁ < Real.sqrt Q) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ 0 < k ∧ ∃ θ : ℝ, 0 < θ ∧ θ < Q ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (x : Vector N) (σ : Fin k → Vector N),
        OnSphere x → (∀ i, OnSphere (σ i)) → goodCompanionBlock Q θ x σ →
        ‖physicalTrainingCenter σ‖^2=(N:ℝ) ∧
          a₁ < overlap x (physicalTrainingCenter σ) := by
  have hlarge := (corrected_query_tendsto hQ.1).eventually (eventually_gt_nhds ha₁)
  obtain ⟨k,hk₀,hk,hquery⟩ := ((eventually_ge_atTop k₀).and
    ((eventually_gt_atTop 0).and hlarge)).exists
  obtain ⟨θ,hθ,hθQ,hcontrol⟩ :=
    physicalTrainingCenter_query_tolerance_all_dimensions hk hQ hquery
  exact ⟨k,hk₀,hk,θ,hθ,hθQ,hcontrol⟩

end
end SlowEquilibration.PureCapturePhysicalCoarseDiniGeometry
