-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiCavityCovariance
public import SlowEquilibration.SphericalGuerraBound
public import SphericalAging.SphereInitialLaw
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

@[expose] public section

/-! Actual independent bulk/cavity Gaussian blocks and their transport to
the original normalized spherical reference measure. This is the genuine
spherical product representation; no Ising product law is substituted. -/

namespace SlowEquilibration.SphericalParisiGaussianBlocks

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalParisiCavityCovariance
open SphericalAging.SphereInitialLaw
open scoped InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def bulkProjection (N M : ℕ) : Vector (N+M) → Vector N := projectGaussian (Fin.castAdd M)
def cavityProjection (N M : ℕ) : Vector (N+M) → Vector M := projectGaussian (Fin.natAdd N)

theorem bulkProjection_measurable (N M : ℕ) : Measurable (bulkProjection N M) :=
  projectGaussian_measurable _

theorem cavityProjection_measurable (N M : ℕ) : Measurable (cavityProjection N M) :=
  projectGaussian_measurable _

theorem append_projections (N M : ℕ) (z : Vector (N+M)) :
    append (bulkProjection N M z) (cavityProjection N M z) = z := by
  apply PiLp.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [append_left, bulkProjection, projectGaussian]
  · simp only [append_right, cavityProjection, projectGaussian]

private theorem gaussianLaw_eq_standard (N : ℕ) :
    gaussianLaw N = SYK.standardGaussianMeasureOnEuclidean (Fin N) := by
  unfold gaussianLaw SYK.standardGaussianMeasureOnEuclidean
  exact map_pi_eq_stdGaussian.symm

theorem append_pair_continuous (N M : ℕ) :
    Continuous (fun z : Vector N × Vector M => append z.1 z.2) := by
  unfold append
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left,Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) j).comp
        (continuous_fst : Continuous (Prod.fst : Vector N × Vector M → Vector N))
  · simpa only [Fin.addCases_right,Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin M => ℝ) j).comp
        (continuous_snd : Continuous (Prod.snd : Vector N × Vector M → Vector M))

theorem append_pair_measurable (N M : ℕ) :
    Measurable (fun z : Vector N × Vector M => append z.1 z.2) :=
  (append_pair_continuous N M).measurable

/-- The physical Gaussian bulk/cavity blocks have the actual standard
Gaussian marginal laws, by injective coordinate projection. -/
theorem bulkProjection_hasLaw (N M : ℕ) :
    HasLaw (bulkProjection N M) (gaussianLaw N) (gaussianLaw (N+M)) := by
  rw [gaussianLaw_eq_standard, gaussianLaw_eq_standard]
  exact projectGaussian_hasLaw _ (by
    intro a b h
    apply Fin.ext
    have hv := congrArg (fun i : Fin (N+M) => i.val) h
    exact hv)

theorem cavityProjection_hasLaw (N M : ℕ) :
    HasLaw (cavityProjection N M) (gaussianLaw M) (gaussianLaw (N+M)) := by
  rw [gaussianLaw_eq_standard, gaussianLaw_eq_standard]
  exact projectGaussian_hasLaw _ (by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change N+a.val=N+b.val at hv
    omega)

/-- Zero true coordinate cross-covariance and the genuine joint Gaussian
law prove independence of the actual bulk and cavity blocks. -/
theorem gaussian_blocks_independent (N M : ℕ) :
    IndepFun (bulkProjection N M) (cavityProjection N M) (gaussianLaw (N+M)) := by
  let B : Vector (N+M) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : Fin (N+M) => ℝ) (Fin.castAdd M i))
  let C : Vector (N+M) →L[ℝ] (Fin M → ℝ) :=
    ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : Fin (N+M) => ℝ) (Fin.natAdd N i))
  have hjoint := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (Vector (N+M)))).map_fun (B.prod C)
  have hind : IndepFun (fun z : Vector (N+M) => fun i : Fin N => z (Fin.castAdd M i))
      (fun z => fun j : Fin M => z (Fin.natAdd N j)) (gaussianLaw (N+M)) := by
    apply hjoint.indepFun_of_covariance_eval
    intro i j
    have hij : Fin.castAdd M i ≠ Fin.natAdd N j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val=N+j.val at hv
      omega
    change cov[(fun z : Vector (N+M) => z (Fin.castAdd M i)),
      (fun z : Vector (N+M) => z (Fin.natAdd N j));stdGaussian (Vector (N+M))]=0
    simp_rw [← EuclideanSpace.basisFun_inner]
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      innerSL_apply_apply]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, hij]
  exact hind.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin M => ℝ)).symm.continuous.measurable

/-- Exact joint product law of the original generating Gaussian blocks. -/
theorem gaussian_blocks_joint_law (N M : ℕ) :
    (gaussianLaw (N+M)).map (fun z => (bulkProjection N M z, cavityProjection N M z)) =
      (gaussianLaw N).prod (gaussianLaw M) := by
  rw [(gaussian_blocks_independent N M).map_prod_eq_prod_map_map
    (bulkProjection_measurable N M).aemeasurable (cavityProjection_measurable N M).aemeasurable,
    (bulkProjection_hasLaw N M).map_eq, (cavityProjection_hasLaw N M).map_eq]

/-- Concatenating two genuine independent Gaussian blocks produces
the exact original full-dimensional Gaussian law. -/
theorem gaussian_append_law (N M : ℕ) :
    ((gaussianLaw N).prod (gaussianLaw M)).map (fun z => append z.1 z.2) = gaussianLaw (N+M) := by
  have hh := congrArg (fun μ : Measure (Vector N × Vector M) => μ.map (fun z => append z.1 z.2))
    (gaussian_blocks_joint_law N M)
  rw [Measure.map_map (append_pair_measurable N M)
    ((bulkProjection_measurable N M).prodMk (cavityProjection_measurable N M))] at hh
  have he : (fun z : Vector N × Vector M => append z.1 z.2) ∘
      (fun z : Vector (N+M) => (bulkProjection N M z, cavityProjection N M z)) = id := by
    funext z
    exact append_projections N M z
  rw [he, Measure.map_id] at hh
  exact hh.symm

/-- The actual full spherical reference measure is the normalization of
the true independent Gaussian block product, a concrete cavity representation. -/
theorem sphere_reference_gaussian_blocks (N M : ℕ) :
    SphericalAging.SphereInitialLaw.sphereLaw (N+M) = ((gaussianLaw N).prod (gaussianLaw M)).map
      (fun z => normalize (N+M) (append z.1 z.2)) := by
  unfold SphericalAging.SphereInitialLaw.sphereLaw
  rw [← gaussian_append_law N M, Measure.map_map (normalize_measurable (N+M))
    (append_pair_measurable N M)]
  rfl

end
end SlowEquilibration.SphericalParisiGaussianBlocks
