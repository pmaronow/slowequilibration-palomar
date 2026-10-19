module

public import SphericalAging.SphereEntropyDissipation
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

/-! Actual coordinate rotations and the exact tangent metric they generate. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereRotationGeometry

open MeasureTheory Set FiniteModel SphereInitialLaw HardSphereDynamics
open SphericalIntegrationByParts SphereEntropyDissipation
open scoped InnerProductSpace BigOperators

/-- The actual skew-adjoint infinitesimal coordinate rotation. -/
@[expose] def coordinateRotation {N : ℕ} (i j : Fin N) : Operator N :=
  InnerProductSpace.rankOne ℝ (basisVector i) (basisVector j)-
    InnerProductSpace.rankOne ℝ (basisVector j) (basisVector i)

theorem coordinateRotation_skew {N : ℕ} (i j : Fin N) :
    star (coordinateRotation i j)=-coordinateRotation i j := by
  simp [coordinateRotation,ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne]

theorem coordinateRotation_apply {N : ℕ} (i j : Fin N) (x : Vector N) :
    coordinateRotation i j x=x j • basisVector i-x i • basisVector j := by
  simp only [coordinateRotation,sub_apply,InnerProductSpace.rankOne_apply]
  rw [real_inner_comm x (basisVector j),real_inner_comm x (basisVector i),basis_inner,basis_inner]

/-- The derivative of a function in the genuine coordinate-rotation direction. -/
theorem lieDerivative_coordinate {N : ℕ} (i j : Fin N) (f : Vector N → ℝ) (x : Vector N) :
    lieDerivative (coordinateRotation i j) f x=x j*gradient f x i-x i*gradient f x j := by
  unfold lieDerivative
  rw [← inner_gradient_left,coordinateRotation_apply]
  simp only [inner_sub_right,real_inner_smul_right,basis_inner]

/-- True coordinate expansion of the real Euclidean inner product. -/
theorem real_inner_coordinates {N : ℕ} (x z : Vector N) :
    ⟪x,z⟫_ℝ=∑ i : Fin N,x i*z i := by
  change (∑ i : Fin N,z i*x i)=(∑ i : Fin N,x i*z i)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual complete coordinate-rotation metric before imposing the sphere constraint. -/
theorem coordinate_rotation_square_sum {N : ℕ} (x z : Vector N) :
    (∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)^2)=
      2*(⟪x,x⟫_ℝ*⟪z,z⟫_ℝ-⟪x,z⟫_ℝ^2) := by
  have hh : (∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)^2)=
      ∑ i : Fin N,∑ j : Fin N,((z i)^2*(x j)^2-2*(x i*z i)*(x j*z j)+(x i)^2*(z j)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hh]
  simp_rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [coordinate_square_sum,coordinate_square_sum]
  rw [real_inner_coordinates x z]
  simp_rw [← Finset.sum_mul]
  rw [coordinate_square_sum,coordinate_square_sum]
  have hdot2 : (∑ i : Fin N,2*(x i*z i))=2*(∑ i : Fin N,x i*z i) := by
    rw [Finset.mul_sum]
  rw [hdot2]
  ring

/-- On the actual radius-sqrt-N sphere this equals the tangent projection norm. -/
theorem coordinate_rotation_metric {N : ℕ} (hN : 0<N) (x z : Vector N)
    (hx : OnSphere x) :
    (1/(2*(N : ℝ)))*(∑ i : Fin N,∑ j : Fin N,(x j*z i-x i*z j)^2)=
      ‖projection x z‖^2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [coordinate_rotation_square_sum,hx,← real_inner_self_eq_norm_sq]
  unfold projection
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_comm z x]
  rw [hx]
  field_simp
  ring

/-- Exact tangent score for the genuine Gibbs logarithmic ratio. -/
@[expose] def tangentScore {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) (x : Vector N) :=
  projection x (gradient (relativeLog β J ρ) x)

@[expose] def fisherInformation {N p : ℕ} (β : ℝ) (J : Disorder N p) (ρ : Vector N → ℝ) : ℝ :=
  ∫ x : Vector N,ρ x*‖tangentScore β J ρ x‖^2 ∂sphereLaw N

/-- The canonical rotation Fisher is exactly the manuscript's tangent-gradient Fisher. -/
theorem rotationFisher_eq_tangent {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x) :
    rotationFisher (1/(2*(N : ℝ))) β J (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) ρ=
      fisherInformation β J ρ := by
  classical
  have hfluxc (ij : Fin N × Fin N) : Continuous (fun x : Vector N =>
      (rotationFlux β J (coordinateRotation ij.1 ij.2) ρ x)^2/ρ x) :=
    ((rotationFlux_contDiff β J _ hρ).continuous.pow 2).div hρ.continuous (fun x => (hpos x).ne')
  unfold rotationFisher fisherInformation
  rw [← integral_finsetSum Finset.univ
    (fun ij _ => continuous_sphere_integrable hN (hfluxc ij)),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hsphere : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  have hmetric := coordinate_rotation_metric hN x (gradient (relativeLog β J ρ) x) hsphere
  simp only [Fintype.sum_prod_type] at *
  unfold tangentScore
  rw [← hmetric]
  have hterm (i j : Fin N) : (rotationFlux β J (coordinateRotation i j) ρ x)^2/ρ x=
      ρ x*(x j*gradient (relativeLog β J ρ) x i-x i*gradient (relativeLog β J ρ) x j)^2 := by
    have hs := relativeLog_lieDerivative β J (coordinateRotation i j) (hρ.of_le (by norm_num)) hpos x
    rw [lieDerivative_coordinate] at hs
    have he := (eq_div_iff (hpos x).ne').mp hs
    rw [← he]
    field_simp [(hpos x).ne']
  simp_rw [hterm,← Finset.mul_sum]
  ring

end SphericalAging.SphereRotationGeometry
