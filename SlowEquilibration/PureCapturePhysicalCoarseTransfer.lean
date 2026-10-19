-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalDiagonalBridge
public import SlowEquilibration.MixedCapturePhysicalReplicaGeometry

/-! Finite-dimensional physical transfer in the proof of source Proposition 9.16.
The normalized empirical mean and the critical cap are literal source objects.
The overlap-array compactness, replicated-band energy bound, and high-energy
relocation probability remain separate analytic inputs. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalCoarseTransfer

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open SphericalBarycenter MixedCaptureReplicaGeometry
open PureCapturePhysicalDiagonalBridge
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The rescaled empirical mean of a fixed companion group, on the
original radius-square-N sphere. -/
def physicalTrainingCenter {N n : ℕ} (σ : Fin n → Vector N) : Vector N :=
  Real.sqrt (N : ℝ) • normalizedReplicaMean (fun i => spin (σ i))

theorem spin_physicalTrainingCenter {N n : ℕ} (hN : 1 ≤ N)
    (σ : Fin n → Vector N) :
    spin (physicalTrainingCenter σ) = normalizedReplicaMean (fun i => spin (σ i)) := by
  have hroot : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
  unfold physicalTrainingCenter spin
  rw [smul_smul, inv_mul_cancel₀ hroot, one_smul]

theorem physicalTrainingCenter_sphere {N n : ℕ} (hN : 1 ≤ N) (hn : 0 < n)
    (σ : Fin n → Vector N) (hσ : ∀ i, OnSphere (σ i))
    {Q θ : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) (hθ : 0 ≤ θ) (hθQ : θ < Q)
    (hpair : ∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| ≤ θ) :
    ‖physicalTrainingCenter σ‖ ^ 2 = (N : ℝ) := by
  have hunit (i : Fin n) : ‖spin (σ i)‖ ^ 2 = 1 := by
    rw [spin_norm hN _ (hσ i), one_pow]
  have hpair' : ∀ i j, i ≠ j →
      |inner ℝ (spin (σ i)) (spin (σ j)) - Q| ≤ θ := by
    intro i j hij
    simpa only [spin_inner hN] using hpair i j hij
  have hm := replicaMean_ne_zero hn (fun i => spin (σ i)) hunit hQ.2.le hθ hθQ hpair'
  rw [physicalTrainingCenter, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    normalizedReplicaMean_norm _ hm, mul_one, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- At a fixed group size, choose a positive overlap tolerance so every
physical companion group yields the strict source cap latitude. The exact
diagonal correction Q+(1-Q)/n is retained. -/
theorem exists_physicalTrainingCenter_query_tolerance {N n : ℕ}
    (hN : 1 ≤ N) (hn : 0 < n)
    {Q a₁ : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (ha₁ : a₁ < Q / Real.sqrt (correctedNormSq Q n)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Q ∧
      ∀ (x : Vector N) (σ : Fin n → Vector N),
        OnSphere x → (∀ i, OnSphere (σ i)) →
        (∀ i j, i ≠ j → |overlap (σ i) (σ j) - Q| < θ) →
        (∀ i, |overlap x (σ i) - Q| < θ) →
        ‖physicalTrainingCenter σ‖ ^ 2 = (N : ℝ) ∧
          a₁ < overlap x (physicalTrainingCenter σ) := by
  let b := (Q / Real.sqrt (correctedNormSq Q n) - a₁) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  obtain ⟨θ,hθ,hθQ,hcontrol⟩ :=
    exists_normalizedMean_query_tolerance (H := Vector N) hn hQ hb
  refine ⟨θ,hθ,hθQ,?_⟩
  intro x σ hx hσ hpair hquery
  have hunit (i : Fin n) : ‖spin (σ i)‖ ^ 2 = 1 := by
    rw [spin_norm hN _ (hσ i), one_pow]
  have hpair' : ∀ i j, i ≠ j →
      |inner ℝ (spin (σ i)) (spin (σ j)) - Q| ≤ θ := by
    intro i j hij
    simpa only [spin_inner hN] using (hpair i j hij).le
  have hquery' : ∀ i, |inner ℝ (spin x) (spin (σ i)) - Q| ≤ θ := by
    intro i
    simpa only [spin_inner hN] using (hquery i).le
  have hcontrol' := hcontrol (fun i => spin (σ i)) (spin x) hunit hpair' hquery'
  have hsphere := physicalTrainingCenter_sphere hN hn σ hσ hQ hθ.le hθQ
    (fun i j hij => (hpair i j hij).le)
  refine ⟨hsphere,?_⟩
  have hcenter := spin_physicalTrainingCenter hN σ
  have hqueryCenter : overlap x (physicalTrainingCenter σ) =
      inner ℝ (spin x) (normalizedReplicaMean (fun i => spin (σ i))) := by
    rw [← spin_inner hN, hcenter]
  rw [hqueryCenter]
  have habs := (abs_lt.mp hcontrol'.2).1
  dsimp [b] at habs
  linarith

/-- Moving a query's candidate center by at most r√N changes its
literal physical overlap by at most r. -/
theorem physical_overlap_sub_le_of_center_distance {N : ℕ} (hN : 1 ≤ N)
    (x w u : Vector N) (hx : OnSphere x) {r : ℝ}
    (hwu : ‖u - w‖ ≤ r * Real.sqrt (N : ℝ)) :
    overlap x w - overlap x u ≤ r := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hxnorm : ‖x‖ = Real.sqrt (N : ℝ) := by
    rw [← (onSphere_iff_norm_sq x).mp hx, Real.sqrt_sq (norm_nonneg x)]
  have hraw : |inner ℝ x (w - u)| ≤ ‖x‖ * ‖w - u‖ := abs_real_inner_le_norm _ _
  have hwu' : ‖w - u‖ ≤ r * Real.sqrt (N : ℝ) := by
    simpa only [norm_sub_rev] using hwu
  have hbound : inner ℝ x (w - u) ≤ r * (N : ℝ) := by
    calc
      inner ℝ x (w - u) ≤ |inner ℝ x (w - u)| := le_abs_self _
      _ ≤ ‖x‖ * ‖w - u‖ := hraw
      _ ≤ Real.sqrt (N : ℝ) * (r * Real.sqrt (N : ℝ)) := by
        rw [hxnorm]
        exact mul_le_mul_of_nonneg_left hwu' hroot.le
      _ = r * (N : ℝ) := by
        calc
          _ = r * (Real.sqrt (N : ℝ)) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hNpos.le]
  have heq : overlap x w - overlap x u = inner ℝ x (w - u) / (N : ℝ) := by
    unfold overlap
    rw [inner_sub_right]
    ring
  rw [heq]
  exact (div_le_iff₀ hNpos).mpr hbound

/-- Exact pointwise transfer used after the score, replicated-energy, and
relocation estimates: the original query spin belongs to an original-field
critical cap above the fixed source energy deficit. -/
theorem physical_training_group_mem_criticalCap {n k : ℕ}
    (μ : FiniteMixture) (J : Disorder (n+2) μ.maxDegree)
    {a a₁ r e τ : ℝ} (ha : a < a₁ - r)
    (x : Vector (n+2)) (hx : OnSphere x)
    (σ : Fin k → Vector (n+2))
    (hqueryCap : ‖physicalTrainingCenter σ‖ ^ 2 = (n+2 : ℕ) ∧
      a₁ < overlap x (physicalTrainingCenter σ))
    (henergy : (n+2 : ℕ) * (e-τ) ≤
      field (mixtureCoefficients μ) J (physicalTrainingCenter σ))
    (hrelocate : ∃ u : Vector (n+2),
      ‖u‖ ^ 2 = (n+2 : ℕ) ∧
      surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
      ‖u-physicalTrainingCenter σ‖ ≤ r * Real.sqrt (n+2 : ℕ) ∧
      field (mixtureCoefficients μ) J (physicalTrainingCenter σ) ≤
        field (mixtureCoefficients μ) J u) :
    x ∈ coarseCriticalCapCover n μ a e τ J := by
  obtain ⟨u,hu,hcrit,hdist,hvalue⟩ := hrelocate
  refine ⟨u,hu,hcrit,henergy.trans hvalue,?_⟩
  have hoverlap := physical_overlap_sub_le_of_center_distance
    (by omega : 1 ≤ n+2) x (physicalTrainingCenter σ) u hx hdist
  linarith [hqueryCap.2]

end SlowEquilibration.PureCapturePhysicalCoarseTransfer
