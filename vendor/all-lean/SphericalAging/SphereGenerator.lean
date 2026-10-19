module

public import SphericalAging.LocalSDE
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

/-! The exact coefficient generator identity `eq:generator` in Section 3.
This module proves the algebraic contraction of the actual projection noise
against actual first and second Fréchet derivatives. It does not assert a
general C² semimartingale Itô theorem or a Markov-semigroup construction. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace SphericalAging.SphereGenerator
open HardSphereDynamics LocalSDE
set_option maxHeartbeats 1200000
variable {N p : ℕ}

lemma noise_coordinate_transpose (x : State N) (i j : Fin N) :
    noiseColumn x j i = Real.sqrt 2 * (projection x (basisVector i)) j := by
  rw [noiseCoordinate_formula]
  simp only [projection,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    basisVector,PiLp.single_apply,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
  by_cases hij : i=j
  · simp only [hij,ite_true]; ring
  · simp only [hij,Ne.symm hij,ite_false]; ring

/-- The genuine diffusion coefficient has covariance `2 P_x` on the
physical sphere, including its off-diagonal entries. -/
theorem noise_covariance (hN : N ≠ 0) (x : State N) (hx : OnSphere x) (i k : Fin N) :
    (∑ j : Fin N, noiseColumn x j i * noiseColumn x j k) =
      2 * ((if i=k then 1 else 0) - x i * x k / N) := by
  have hs : (∑ j : Fin N, noiseColumn x j i * noiseColumn x j k) =
      2 * ⟪projection x (basisVector i),projection x (basisVector k)⟫_ℝ := by
    simp only [noise_coordinate_transpose,PiLp.inner_apply,RCLike.inner_apply,
      conj_trivial]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (Real.sqrt 2)^2 * ((projection x (basisVector k)) j *
          (projection x (basisVector i)) j) := by ring
      _ = _ := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hi := projection_self_adjoint x (projection x (basisVector i)) (basisVector k)
  rw [projection_idempotent hN x _ hx] at hi
  rw [hs,← hi,basis_inner]
  simp only [projection,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    basisVector,PiLp.single_apply,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
  by_cases hik : i=k
  · simp only [hik,ite_true]; ring
  · simp only [hik,Ne.symm hik,ite_false]; ring

lemma bilinear_coordinates (H : State N →L[ℝ] State N →L[ℝ] ℝ) (u v : State N) :
    H u v = ∑ i : Fin N, ∑ k : Fin N, u i * v k * H (basisVector i) (basisVector k) := by
  calc
    H u v = ∑ i : Fin N, u i * H (basisVector i) v := by
      conv_lhs => rw [← state_sum_basis u]
      simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => rw [← state_sum_basis v]
      simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum,mul_assoc]

/-- Actual noise contraction against an arbitrary bilinear Hessian. -/
theorem hessian_noise_contraction (hN : N ≠ 0) (x : State N) (hx : OnSphere x)
    (H : State N →L[ℝ] State N →L[ℝ] ℝ) :
    (1 / 2 : ℝ) * (∑ j : Fin N, H (noiseColumn x j) (noiseColumn x j)) =
      ∑ i : Fin N, ∑ k : Fin N,
        ((if i=k then 1 else 0) - x i * x k / N) * H (basisVector i) (basisVector k) := by
  rw [show (∑ j : Fin N, H (noiseColumn x j) (noiseColumn x j)) =
    ∑ j : Fin N, ∑ i : Fin N, ∑ k : Fin N,
      noiseColumn x j i * noiseColumn x j k * H (basisVector i) (basisVector k) from
        Finset.sum_congr rfl (fun j _ => bilinear_coordinates H _ _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ j : Fin N, (noiseColumn x j i * noiseColumn x j k) *
        ((1 / 2 : ℝ) * H (basisVector i) (basisVector k)) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    _ = _ := by rw [← Finset.sum_mul,noise_covariance hN x hx i k]; ring

lemma gradient_drift_pairing (hN : N ≠ 0) (x : State N) (hx : OnSphere x)
    (β : ℝ) (g : State N → State N) (F : State N → ℝ) :
    fderiv ℝ F x (drift β g x) = - kappa N * ⟪x,gradient F x⟫_ℝ +
      β * ⟪projection x (g x),projection x (gradient F x)⟫_ℝ := by
  rw [← inner_gradient_left]
  simp only [drift,inner_sub_right,real_inner_smul_right]
  have hp : ⟪projection x (g x),projection x (gradient F x)⟫_ℝ =
      ⟪projection x (g x),gradient F x⟫_ℝ := by
    rw [← projection_self_adjoint,projection_idempotent hN x _ hx]
  rw [hp,real_inner_comm (gradient F x) x,real_inner_comm (gradient F x) (projection x (g x))]
  ring

/-- The actual coefficient Itô generator, with the manuscript's `√2`
projection noise and gradient-ascent drift. -/
@[expose] def coefficientGenerator (β : ℝ) (J : FiniteModel.Disorder N p)
    (F : State N → ℝ) (x : State N) : ℝ :=
  fderiv ℝ F x (hamiltonianDrift β J x) +
    (1 / 2 : ℝ) * ∑ j : Fin N,
      fderiv ℝ (fderiv ℝ F) x (noiseColumn x j) (noiseColumn x j)

/-- Exact generator formula for actual Fréchet derivatives and actual
Hamiltonian coefficients, corresponding to `eq:generator`. -/
theorem coefficientGenerator_onSphere (hN : N ≠ 0) (β : ℝ)
    (J : FiniteModel.Disorder N p) (F : State N → ℝ) (x : State N) (hx : OnSphere x) :
    coefficientGenerator β J F x =
      (∑ i : Fin N, ∑ k : Fin N, ((if i=k then 1 else 0) - x i * x k / N) *
        fderiv ℝ (fderiv ℝ F) x (basisVector i) (basisVector k)) -
      kappa N * ⟪x,gradient F x⟫_ℝ +
      β * ⟪projection x (hamiltonianGradient J x),projection x (gradient F x)⟫_ℝ := by
  rw [coefficientGenerator,hessian_noise_contraction hN x hx,
    hamiltonianDrift,gradient_drift_pairing hN x hx]
  ring

end SphericalAging.SphereGenerator
