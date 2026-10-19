-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalCoarseTransfer
public import SlowEquilibration.LiteratureSubagPhysicalDefinitions
public import SlowEquilibration.SphericalGaussianJet

/-! Deterministic geometry in the proof of manuscript Proposition
`prop:pc-replica-means`: nearby net centers contain the replica tuple in
Subag's replicated band, the contact mean is the rescaled training center,
and the pure field has exact radial homogeneity. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.ReplicaMeanNetCover

open SphericalModel SphericalBarycenter MixedCaptureReplicaGeometry
open MixedCapturePhysicalReplicaGeometry PureCapturePhysicalCoarseTransfer
open LiteratureSubagPhysicalDefinitions SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open scoped BigOperators

set_option autoImplicit false

/-- Membership in Subag's band around any net point near the rescaled replica mean. -/
theorem mem_replicatedBand_of_near_contactMean {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {Q η δ ρ ϑ : ℝ} (hQ : Q ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 ≤ η) (hηQ : η < Q / 2) (hηρ : η ≤ ρ)
    (hδ : (2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ) + ϑ ≤ δ * Real.sqrt Q)
    (σ : Fin k → Vector N) (hσ : ∀ i, OnSphere (σ i))
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| < η)
    (m : Vector N) (hm : ‖m - physicalContactMean Q σ‖ ≤ ϑ * Real.sqrt (N : ℝ)) :
    σ ∈ ReplicatedBand k Q δ ρ m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsource := (source_mb_diagonal hN (by omega) σ hσ hQ hη hηQ
    (fun i j hij => (hpair i j hij).le)).2.2
  refine ⟨?_, fun i j hij => (hpair i j hij).trans_le hηρ⟩
  intro i
  have hxnorm : ‖σ i‖ = Real.sqrt (N : ℝ) := by
    rw [← (onSphere_iff_norm_sq (σ i)).mp (hσ i), Real.sqrt_sq (norm_nonneg _)]
  have hraw : |inner ℝ (σ i) (m - physicalContactMean Q σ)| ≤ ϑ * (N : ℝ) := by
    calc
      _ ≤ ‖σ i‖ * ‖m - physicalContactMean Q σ‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt (N : ℝ) * (ϑ * Real.sqrt (N : ℝ)) := by
        rw [hxnorm]
        exact mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)
      _ = ϑ * (N : ℝ) := by
        calc
          _ = ϑ * (Real.sqrt (N : ℝ)) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hNpos.le]
  have hdiff : |overlap (σ i) m - overlap (σ i) (physicalContactMean Q σ)| ≤ ϑ := by
    rw [overlap, overlap, ← sub_div, ← inner_sub_right, abs_div,
      abs_of_pos hNpos]
    exact (div_le_iff₀ hNpos).mpr hraw
  calc
    |overlap (σ i) m - Q| ≤
        |overlap (σ i) m - overlap (σ i) (physicalContactMean Q σ)| +
          |overlap (σ i) (physicalContactMean Q σ) - Q| := abs_sub_le _ _ _
    _ ≤ ϑ + ((2 * Real.sqrt 2 + 1) * η + 1 / (k : ℝ)) :=
      add_le_add hdiff (hsource i)
    _ ≤ δ * Real.sqrt Q := by linarith

/-- The source contact mean is the training center rescaled to the contact sphere. -/
theorem physicalContactMean_eq_smul_trainingCenter {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {Q : ℝ} (hQ : 0 ≤ Q) (σ : Fin k → Vector N) (hpos : 0 < physicalMeanNormSq σ) :
    physicalContactMean Q σ = Real.sqrt Q • physicalTrainingCenter σ := by
  have _ := hk
  have _ := hpos
  have hroot : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
  have hs := congrArg (fun x : Vector N => Real.sqrt (N : ℝ) • x)
    (spin_physicalContactMean hN hQ σ)
  simpa only [spin, contactReplicaMean, physicalTrainingCenter, smul_smul,
    mul_inv_cancel₀ hroot, one_smul, mul_comm] using hs

/-- Exact radial homogeneity of the pure field. -/
theorem pure_field_smul (p : ℕ) (hp : 2 ≤ p) {N : ℕ}
    (J : Disorder N (FiniteMixture.pure p hp 1 one_pos).maxDegree) {a : ℝ} (ha : 0 ≤ a)
    (u : Vector N) :
    field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J (a • u) =
      a ^ p * field (mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos)) J u := by
  classical
  have _ := ha
  unfold field
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  unfold blockField
  rw [pure_spatial_smul]
  by_cases hdp : d.val.val = p
  · rw [show a ^ d.val.val = a ^ p from congrArg (fun q : ℕ => a ^ q) hdp]
    ring
  · have hc : mixtureCoefficients (FiniteMixture.pure p hp 1 one_pos) d = 0 := by
      simp [mixtureCoefficients, FiniteMixture.pure, hdp]
    simp [hc]

end SlowEquilibration.ReplicaMeanNetCover
