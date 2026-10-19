module

public import SphericalAging.SphereFisherDissipation
public import SphericalAging.SphereRotationGeometry
public import Mathlib.Analysis.Calculus.VectorField

public section

/-! Exact algebraic splitting of the constructed iterated carré du champ into
its diffusion and Hamiltonian drift contributions, and genuine differential
commutators of linear vector fields. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace SphericalAging.SphereGamma2Algebra

open FiniteModel SphericalIntegrationByParts SphereGeneratorIntegrationByParts
open SphereGeneratorAlgebra SphereFisherDissipation
open SphereRotationGeometry HardSphereDynamics
open scoped BigOperators

theorem lieDerivative_const_mul {N : ℕ} (A : Operator N) (c : ℝ)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 1 f) (x : Vector N) :
    lieDerivative A (fun y => c * f y) x = c * lieDerivative A f x := by
  unfold lieDerivative
  rw [fderiv_const_mul (hf.differentiable (by norm_num) x)]
  simp

theorem rotationGamma_const_mul_right {N : ℕ} {ι : Type*} [Fintype ι]
    (κ : ℝ) (A : ι → Operator N) (f : Vector N → ℝ) (c : ℝ)
    {g : Vector N → ℝ} (hg : ContDiff ℝ 1 g) (x : Vector N) :
    rotationGamma κ A f (fun y => c * g y) x = c * rotationGamma κ A f g x := by
  classical
  unfold rotationGamma
  simp_rw [lieDerivative_const_mul _ c hg, mul_left_comm _ c]
  rw [← Finset.mul_sum]
  ring

theorem rotationGenerator_drift_split {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    (f : Vector N → ℝ) (x : Vector N) :
    rotationGenerator κ β J A f x = rotationGenerator κ 0 J A f x +
      β * rotationGamma κ A (Hamiltonian N p J) f x := by
  classical
  unfold rotationGenerator rotationGamma
  simp only [zero_mul, add_zero]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc β, ← Finset.mul_sum]
  ring

theorem rotationGamma2_drift_split {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 3 f) (x : Vector N) :
    rotationGamma2 κ β J A f x = rotationGamma2 κ 0 J A f x +
      β * ((1/2) * rotationGamma κ A (Hamiltonian N p J) (rotationGamma κ A f f) x -
        rotationGamma κ A f (rotationGamma κ A (Hamiltonian N p J) f) x) := by
  have hL := rotationGenerator_contDiff_one κ 0 J A hf
  have hH : ContDiff ℝ 2 (Hamiltonian N p J) := (Hamiltonian_contDiff J).of_le (by simp)
  have hG : ContDiff ℝ 1 (rotationGamma κ A (Hamiltonian N p J) f) :=
    rotationGamma_contDiff_order κ A hH (hf.of_le (by norm_num))
  have he : rotationGenerator κ β J A f =
      (fun y => rotationGenerator κ 0 J A f y + β * rotationGamma κ A (Hamiltonian N p J) f y) :=
    funext (rotationGenerator_drift_split κ β J A f)
  unfold rotationGamma2
  rw [rotationGenerator_drift_split, he,
    rotationGamma_add_right κ A f hL (contDiff_const.mul hG),
    rotationGamma_const_mul_right κ A f β hG]
  ring

theorem lieDerivative_commutator {N : ℕ} (A B : Operator N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (x : Vector N) :
    lieDerivative A (lieDerivative B f) x - lieDerivative B (lieDerivative A f) x =
      lieDerivative (B.comp A - A.comp B) f x := by
  have hh := VectorField.fderiv_apply_lieBracket (x := x) (V := fun y => A y) (W := fun y => B y)
    hf.contDiffAt (by simp) B.differentiableAt A.differentiableAt
  unfold lieDerivative
  rw [← hh]
  simp [VectorField.lieBracket]

theorem lieDerivative_twice_fderiv {N : ℕ} (A B : Operator N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (x : Vector N) :
    lieDerivative A (lieDerivative B f) x =
      fderiv ℝ (fderiv ℝ f) x (A x) (B x) + fderiv ℝ f x (B (A x)) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ f)).differentiable (by norm_num) x
  unfold lieDerivative
  rw [fderiv_clm_apply hdf B.differentiableAt]
  simp [add_comm]

theorem coordinateRotation_commutator {N : ℕ} (i j k l : Fin N) :
    (coordinateRotation k l).comp (coordinateRotation i j) -
        (coordinateRotation i j).comp (coordinateRotation k l) =
      (if i = k then (1 : ℝ) else 0) • coordinateRotation j l +
        (if j = l then (1 : ℝ) else 0) • coordinateRotation i k -
        (if j = k then (1 : ℝ) else 0) • coordinateRotation i l -
        (if i = l then (1 : ℝ) else 0) • coordinateRotation j k := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply, coordinateRotation_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, basisVector, PiLp.single_apply]
  have hδ (a b : Fin N) : (if a = b then (1 : ℝ) else 0) =
      (if b = a then (1 : ℝ) else 0) := by
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hδ l i, hδ k i, hδ l j, hδ k j]
  module

theorem coordinate_lieDerivative_commutator {N : ℕ} (i j k l : Fin N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (x : Vector N) :
    lieDerivative (coordinateRotation i j) (lieDerivative (coordinateRotation k l) f) x -
        lieDerivative (coordinateRotation k l) (lieDerivative (coordinateRotation i j) f) x =
      (if i = k then (1 : ℝ) else 0) * lieDerivative (coordinateRotation j l) f x +
        (if j = l then (1 : ℝ) else 0) * lieDerivative (coordinateRotation i k) f x -
        (if j = k then (1 : ℝ) else 0) * lieDerivative (coordinateRotation i l) f x -
        (if i = l then (1 : ℝ) else 0) * lieDerivative (coordinateRotation j k) f x := by
  rw [lieDerivative_commutator _ _ hf, coordinateRotation_commutator]
  simp only [lieDerivative, sub_apply, add_apply, smul_apply, map_sub, map_add, map_smul,
    smul_eq_mul]

end SphericalAging.SphereGamma2Algebra
