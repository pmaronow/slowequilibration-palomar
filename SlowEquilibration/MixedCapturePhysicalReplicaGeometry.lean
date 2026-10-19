-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedCaptureReplicaGeometry
public import SlowEquilibration.SphericalBarycenter

/-! The literal physical-radius version of manuscript equation
mb-diagonal. The mean, norm correction, normalized contact center and
overlaps are the source quantities on the radius-sqrt-N sphere. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.MixedCapturePhysicalReplicaGeometry

open SphericalModel SphericalForm SphericalBarycenter
open SphericalAging.HardSphereDynamics
open MixedCaptureReplicaGeometry
open scoped BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {N n : ℕ}

def physicalMean (σ : Fin n → Vector N) : Vector N := replicaMean σ

def physicalMeanNormSq (σ : Fin n → Vector N) : ℝ := ‖physicalMean σ‖ ^ 2 / (N : ℝ)

def physicalContactMean (Q : ℝ) (σ : Fin n → Vector N) : Vector N :=
  Real.sqrt (Q / physicalMeanNormSq σ) • physicalMean σ

/-- Spin normalization is literal scalar multiplication and commutes
with the actual finite empirical average. -/
theorem spin_physicalMean (σ : Fin n → Vector N) :
    spin (physicalMean σ) = replicaMean (fun i => spin (σ i)) := by
  unfold physicalMean replicaMean spin
  rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm]

theorem spin_norm_sq_eq (hN : 1 ≤ N) (x : Vector N) :
    ‖spin x‖ ^ 2 = ‖x‖ ^ 2 / (N : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, spin_inner hN, overlap, real_inner_self_eq_norm_sq]

theorem physicalMeanNormSq_eq_unitMeanNormSq (hN : 1 ≤ N) (σ : Fin n → Vector N) :
    physicalMeanNormSq σ = ‖replicaMean (fun i => spin (σ i))‖ ^ 2 := by
  rw [← spin_physicalMean, spin_norm_sq_eq hN]
  rfl

/-- The literal sqrt(Q/qbar) source normalization equals the proved
contact-sphere normalization of the unit-spin empirical mean. -/
theorem spin_physicalContactMean (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 ≤ Q)
    (σ : Fin n → Vector N) :
    spin (physicalContactMean Q σ) = contactReplicaMean Q (fun i => spin (σ i)) := by
  have hscale (a : ℝ) (x : Vector N) : spin (a • x) = a • spin x := by
    unfold spin
    rw [smul_smul, smul_smul, mul_comm]
  rw [physicalContactMean, hscale, spin_physicalMean, Real.sqrt_div hQ,
    physicalMeanNormSq_eq_unitMeanNormSq hN, Real.sqrt_sq (norm_nonneg _)]
  rw [contactReplicaMean, normalizedReplicaMean, smul_smul, div_eq_mul_inv]

theorem physicalMean_unitReplicas (hN : 1 ≤ N) (σ : Fin n → Vector N)
    (hσ : ∀ i, OnSphere (σ i)) : ∀ i, ‖spin (σ i)‖ ^ 2 = 1 := by
  intro i
  rw [spin_norm hN _ (hσ i), one_pow]

/-- First inequality of source mb-diagonal at the physical sphere
radius, with every diagonal term retained exactly. -/
theorem physicalMeanNormSq_error (hN : 1 ≤ N) (hn : 0 < n)
    (σ : Fin n → Vector N) (hσ : ∀ i, OnSphere (σ i))
    {Q θ : ℝ} (hθ : 0 ≤ θ)
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| ≤ θ) :
    |physicalMeanNormSq σ - correctedNormSq Q n| ≤ θ := by
  rw [physicalMeanNormSq_eq_unitMeanNormSq hN]
  exact replicaMean_norm_sq_error hn _ (physicalMean_unitReplicas hN σ hσ) hθ
    (by intro i j hij; simpa only [spin_inner hN] using hpair i j hij)

/-- Second inequality of source mb-diagonal for the actual physical
overlap with the empirical mean. -/
theorem physicalMean_row_error (hN : 1 ≤ N) (hn : 0 < n)
    (σ : Fin n → Vector N) (hσ : ∀ i, OnSphere (σ i))
    {Q θ : ℝ} (hθ : 0 ≤ θ)
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| ≤ θ) (i : Fin n) :
    |overlap (σ i) (physicalMean σ) - correctedNormSq Q n| ≤ θ := by
  rw [← spin_inner hN, spin_physicalMean]
  exact replicaMean_row_error hn _ (physicalMean_unitReplicas hN σ hσ) hθ
    (by intro i j hij; simpa only [spin_inner hN] using hpair i j hij) i

/-- The literal physical mean has positive squared normalized norm,
so the source contact-center rescaling is well defined. -/
theorem physicalMeanNormSq_pos (hN : 1 ≤ N) (hn : 0 < n)
    (σ : Fin n → Vector N) (hσ : ∀ i, OnSphere (σ i))
    {Q θ : ℝ} (hQ : Q ∈ Set.Ioo (0 : ℝ) 1) (hθ : 0 ≤ θ) (hθQ : θ < Q / 2)
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| ≤ θ) :
    0 < physicalMeanNormSq σ := by
  have herr := (abs_le.mp (physicalMeanNormSq_error hN hn σ hσ hθ hpair)).1
  have hqn := correctedNormSq_ge hQ.2.le hn
  linarith [hQ.1]

/-- The source contact center lies on the literal radius-sqrt(N*Q)
sphere, with no normalized-radius hypothesis supplied. -/
theorem physicalContactMean_norm_sq (hN : 1 ≤ N) (hn : 0 < n)
    (σ : Fin n → Vector N) (hσ : ∀ i, OnSphere (σ i))
    {Q θ : ℝ} (hQ : Q ∈ Set.Ioo (0 : ℝ) 1) (hθ : 0 ≤ θ) (hθQ : θ < Q / 2)
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| ≤ θ) :
    ‖physicalContactMean Q σ‖ ^ 2 = (N : ℝ) * Q := by
  have hmean := replicaMean_ne_zero hn (fun i => spin (σ i))
    (physicalMean_unitReplicas hN σ hσ) hQ.2.le hθ (by linarith [hQ.1])
    (by intro i j hij; simpa only [spin_inner hN] using hpair i j hij)
  have hs := contactReplicaMean_norm_sq hQ.1.le (fun i => spin (σ i)) hmean
  rw [← spin_physicalContactMean hN hQ.1.le, spin_norm_sq_eq hN] at hs
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  exact (div_eq_iff hNne).mp hs |>.trans (mul_comm _ _)

/-- All three bounds in source mb-diagonal, on the literal radius-sqrt-N
sphere, follow from the proved finite-vector geometry. -/
theorem source_mb_diagonal (hN : 1 ≤ N) (hn : 0 < n)
    (σ : Fin n → Vector N) (hσ : ∀ i, OnSphere (σ i))
    {Q θ : ℝ} (hQ : Q ∈ Set.Ioo (0 : ℝ) 1) (hθ : 0 ≤ θ) (hθQ : θ < Q / 2)
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| ≤ θ) :
    |physicalMeanNormSq σ - correctedNormSq Q n| ≤ θ ∧
      (∀ i, |overlap (σ i) (physicalMean σ) - correctedNormSq Q n| ≤ θ) ∧
      (∀ i, |overlap (σ i) (physicalContactMean Q σ) - Q| ≤
        (2 * Real.sqrt 2 + 1) * θ + 1 / (n : ℝ)) := by
  refine ⟨physicalMeanNormSq_error hN hn σ hσ hθ hpair,
    physicalMean_row_error hN hn σ hσ hθ hpair, ?_⟩
  intro i
  rw [← spin_inner hN, spin_physicalContactMean hN hQ.1.le]
  exact contactReplicaMean_row_error hn _ (physicalMean_unitReplicas hN σ hσ) hQ hθ hθQ
    (by intro i j hij; simpa only [spin_inner hN] using hpair i j hij) i

end SlowEquilibration.MixedCapturePhysicalReplicaGeometry
