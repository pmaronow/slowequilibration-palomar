module

public import SphericalAging.GaussianLandscapeMoments
public import SphericalAging.HardSphereDynamics
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

public section

/-! Genuine derivatives of the manuscript Hamiltonian diagonal multilinear form. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace
open MeasureTheory
namespace SphericalAging.LandscapeDerivatives
open FiniteModel GaussianLandscape

@[expose] def diagonalDerivative {N p : ℕ} (f : TensorForm N p) (x : Vector N) :
    Vector N →L[ℝ] ℝ := ∑ i : Fin p, f.toContinuousLinearMap (fun _ => x) i

theorem diagonal_hasFDerivAt {N p : ℕ} (f : TensorForm N p) (x : Vector N) :
    HasFDerivAt (fun y => f (fun _ => y)) (diagonalDerivative f x) x := by
  simpa [diagonalDerivative] using
    (HasFDerivAt.multilinear_comp (f := f) (fun _ : Fin p => hasFDerivAt_id x))

theorem diagonalDerivative_apply {N p : ℕ} (f : TensorForm N p) (x y : Vector N) :
    diagonalDerivative f x y = ∑ i : Fin p, f (Function.update (fun _ => x) i y) := by
  simp [diagonalDerivative, ContinuousMultilinearMap.toContinuousLinearMap]

theorem updated_norm_product {N p : ℕ} (x y : Vector N) (i : Fin p) :
    (∏ j : Fin p, ‖Function.update (fun _ => x) i y j‖) = ‖y‖ * ‖x‖^(p-1) := by
  classical
  have he : (fun j : Fin p => ‖Function.update (fun _ => x) i y j‖) =
      Function.update (fun _ => ‖x‖) i ‖y‖ := by
    funext j
    by_cases hj : j=i <;> simp [hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.card_univ_sdiff]

theorem diagonalDerivative_apply_norm_le {N p : ℕ} (f : TensorForm N p)
    (x y : Vector N) : ‖diagonalDerivative f x y‖ ≤
      (p : ℝ)*‖f‖*‖x‖^(p-1)*‖y‖ := by
  rw [diagonalDerivative_apply]
  calc
    _ ≤ ∑ i : Fin p, ‖f (Function.update (fun _ => x) i y)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin p, ‖f‖*(‖y‖*‖x‖^(p-1)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [updated_norm_product] using f.le_opNorm (Function.update (fun _ => x) i y)
    _ = _ := by simp; ring

theorem diagonalDerivative_norm_le {N p : ℕ} (f : TensorForm N p) (x : Vector N) :
    ‖diagonalDerivative f x‖ ≤ (p : ℝ)*‖f‖*‖x‖^(p-1) :=
  (diagonalDerivative f x).opNorm_le_bound (by positivity) (diagonalDerivative_apply_norm_le f x)

@[expose] def diagonalL (N p : ℕ) : Vector N →L[ℝ] (Fin p → Vector N) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Vector N))

theorem diagonalL_norm_le (N p : ℕ) : ‖diagonalL N p‖ ≤ 1 := by
  apply (diagonalL N p).opNorm_le_bound (by norm_num)
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  simp [diagonalL]

theorem diagonal_iteratedFDeriv_norm_le {N p : ℕ} (f : TensorForm N p) (x : Vector N)
    (n : ℕ) : ‖iteratedFDeriv ℝ n (fun y => f (fun _ => y)) x‖ ≤
      (Nat.descFactorial p n : ℝ)*‖f‖*‖x‖^(p-n) := by
  have hid : (fun y : Vector N => f (fun _ => y)) = f ∘ diagonalL N p := rfl
  rw [hid, (diagonalL N p).iteratedFDeriv_comp_right (f.contDiff (n := ⊤)) x (by simp)]
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n f (diagonalL N p x)) (fun _ : Fin n => diagonalL N p)
  have hp : (∏ _ : Fin n, ‖diagonalL N p‖) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _; exact norm_nonneg _
    · intro i _; exact diagonalL_norm_le N p
  have hf := f.norm_iteratedFDeriv_le n (diagonalL N p x)
  simp only [Fintype.card_fin] at hf
  have hx : ‖diagonalL N p x‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    simp [diagonalL]
  exact (hc.trans (mul_le_of_le_one_right (norm_nonneg _) hp)).trans
    (hf.trans (by gcongr))

theorem gradient_derivative_norm {N : ℕ} (f : Vector N → ℝ) (x : Vector N) :
    ‖fderiv ℝ (gradient f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  change ‖fderiv ℝ ((InnerProductSpace.toDual ℝ (Vector N)).symm ∘ fderiv ℝ f) x‖ = _
  rw [LinearIsometryEquiv.comp_fderiv]
  change ‖(InnerProductSpace.toDual ℝ (Vector N)).symm.toLinearIsometry.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ f) x)‖ = _
  rw [LinearIsometry.norm_toContinuousLinearMap_comp]
  rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]

theorem Hamiltonian_eq_diagonal {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    Hamiltonian N p J x = normalization N p * tensorForm N p J (fun _ => x) := by
  rw [tensorForm_apply]
  rfl

theorem Hamiltonian_hasFDerivAt {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    HasFDerivAt (Hamiltonian N p J)
      (normalization N p • diagonalDerivative (tensorForm N p J) x) x := by
  have hh := (diagonal_hasFDerivAt (tensorForm N p J) x).const_smul (normalization N p)
  convert hh using 1
  funext y
  exact Hamiltonian_eq_diagonal J y

theorem Hamiltonian_iteratedFDeriv_norm_le {N p : ℕ} (J : Disorder N p) (x : Vector N)
    (n : ℕ) : ‖iteratedFDeriv ℝ n (Hamiltonian N p J) x‖ ≤
      normalization N p * (Nat.descFactorial p n : ℝ)*‖tensorForm N p J‖*‖x‖^(p-n) := by
  have hc : ContDiff ℝ n (fun y : Vector N => tensorForm N p J (fun _ => y)) :=
    (tensorForm N p J).contDiff.comp (diagonalL N p).contDiff
  have he : Hamiltonian N p J =
      fun y : Vector N => normalization N p • tensorForm N p J (fun _ => y) := by
    funext y
    exact Hamiltonian_eq_diagonal J y
  rw [he, iteratedFDeriv_const_smul_apply' hc.contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ normalization N p from
      Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact (mul_le_mul_of_nonneg_left (diagonal_iteratedFDeriv_norm_le (tensorForm N p J) x n)
    (show 0 ≤ normalization N p from Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans_eq (by ring)

theorem Hamiltonian_gradient_norm_le {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    ‖gradient (Hamiltonian N p J) x‖ ≤
      normalization N p * (p : ℝ)*‖tensorForm N p J‖*‖x‖^(p-1) := by
  rw [gradient, LinearIsometryEquiv.norm_map, (Hamiltonian_hasFDerivAt J x).fderiv,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ normalization N p from
      Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact (mul_le_mul_of_nonneg_left (diagonalDerivative_norm_le (tensorForm N p J) x)
    (show 0 ≤ normalization N p from Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans_eq (by ring)

theorem normalization_sqrt_power {N p : ℕ} (hN : 0 < N) :
    normalization N p * Real.sqrt (N : ℝ)^(p-1) = 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [normalization, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hNr.le, ← Real.rpow_add hNr]
  convert Real.rpow_zero (N : ℝ) using 1 <;> ring

theorem sphere_norm {N : ℕ} (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    ‖x‖ = Real.sqrt (N : ℝ) := by
  rw [← hx, Real.sqrt_sq (norm_nonneg x)]

theorem Hamiltonian_gradient_sphere_bound {N p : ℕ} (hN : 0 < N)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    ‖gradient (Hamiltonian N p J) x‖ / Real.sqrt (N : ℝ) ≤
      (p : ℝ)*landscapeNorm N p J := by
  have hr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  apply (div_le_iff₀ hr).mpr
  have hh := Hamiltonian_gradient_norm_le J x
  rw [sphere_norm x hx] at hh
  have he : normalization N p*(p : ℝ)*‖tensorForm N p J‖*
      Real.sqrt (N : ℝ)^(p-1) = (p : ℝ)*‖tensorForm N p J‖ := by
    calc
      _ = (p : ℝ)*‖tensorForm N p J‖*
          (normalization N p*Real.sqrt (N : ℝ)^(p-1)) := by ring
      _ = _ := by rw [normalization_sqrt_power hN]; ring
  rw [he] at hh
  unfold landscapeNorm
  convert hh using 1
  field_simp

theorem Hamiltonian_sphere_bound {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    |Hamiltonian N p J x| / (N : ℝ) ≤ landscapeNorm N p J := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr := Real.sqrt_pos.mpr hNr
  have hf := (tensorForm N p J).le_opNorm (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hf
  have hh : |Hamiltonian N p J x| ≤ normalization N p*‖tensorForm N p J‖*‖x‖^p := by
    rw [Hamiltonian_eq_diagonal, abs_mul,
      abs_of_nonneg (show 0 ≤ normalization N p from Real.rpow_nonneg hNr.le _)]
    exact (mul_le_mul_of_nonneg_left hf (show 0 ≤ normalization N p from Real.rpow_nonneg hNr.le _)).trans_eq (by ring)
  apply (div_le_iff₀ hNr).mpr
  rw [sphere_norm x hx] at hh
  have hp' : p=(p-1)+1 := by omega
  have he : normalization N p*‖tensorForm N p J‖*Real.sqrt (N : ℝ)^p =
      ‖tensorForm N p J‖*Real.sqrt (N : ℝ) := by
    calc
      _ = ‖tensorForm N p J‖*(normalization N p*
          Real.sqrt (N : ℝ)^(p-1))*Real.sqrt (N : ℝ) := by
            conv_lhs => arg 2; rw [hp', pow_succ]
            ring
      _ = _ := by rw [normalization_sqrt_power hN]; ring
  rw [he] at hh
  have hs := Real.mul_self_sqrt hNr.le
  unfold landscapeNorm
  convert hh using 1
  field_simp
  rw [pow_two, hs]

theorem Hamiltonian_hessian_sphere_bound {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    ‖fderiv ℝ (gradient (Hamiltonian N p J)) x‖ ≤
      (p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J := by
  rw [gradient_derivative_norm]
  have hh := Hamiltonian_iteratedFDeriv_norm_le J x 2
  rw [Nat.cast_descFactorial_two, sphere_norm x hx] at hh
  have hr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hs : normalization N p*Real.sqrt (N : ℝ)^(p-2) = (Real.sqrt (N : ℝ))⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff (ne_of_gt hr)).mpr
    have hpow : p-1=(p-2)+1 := by omega
    have hnorm := normalization_sqrt_power (p := p) hN
    rw [hpow, pow_succ] at hnorm
    simpa only [mul_assoc] using hnorm
  have he : normalization N p*((p : ℝ)*((p : ℝ)-1))*‖tensorForm N p J‖*
      Real.sqrt (N : ℝ)^(p-2) = (p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J := by
    calc
      _ = (p : ℝ)*((p : ℝ)-1)*‖tensorForm N p J‖*
        (normalization N p*Real.sqrt (N : ℝ)^(p-2)) := by ring
      _ = _ := by rw [hs]; unfold landscapeNorm; ring
  exact hh.trans_eq he

/-- Actual orthogonal tangent projection for the round sphere of radius √N. -/
@[expose] def tangentProjection {N : ℕ} (x : Vector N) : Vector N →L[ℝ] Vector N :=
  ContinuousLinearMap.id ℝ (Vector N) -
    (1/(N : ℝ)) • (innerSL ℝ x).smulRight x

@[simp] theorem tangentProjection_apply {N : ℕ} (x y : Vector N) :
    tangentProjection x y = HardSphereDynamics.projection x y := by
  simp [tangentProjection, HardSphereDynamics.projection, div_eq_mul_inv, smul_smul, mul_comm]

theorem tangentProjection_norm_le {N : ℕ} (hN : 0 < N) (x : Vector N)
    (hx : ‖x‖^2=(N : ℝ)) : ‖tangentProjection x‖ ≤ 1 := by
  apply (tangentProjection x).opNorm_le_bound (by norm_num)
  intro y
  rw [one_mul, tangentProjection_apply]
  exact HardSphereDynamics.projection_norm_le_onSphere (Nat.ne_of_gt hN) x y
    ((HardSphereDynamics.onSphere_iff_norm_sq x).mpr hx)

/-- The intrinsic Hessian written in its standard extrinsic tangent form. -/
@[expose] def sphericalHessian {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    Vector N →L[ℝ] Vector N :=
  (tangentProjection x).comp ((fderiv ℝ (gradient (Hamiltonian N p J)) x).comp
    (tangentProjection x)) -
    (inner ℝ x (gradient (Hamiltonian N p J) x)/(N : ℝ)) • tangentProjection x

theorem radial_gradient_sphere_bound {N p : ℕ} (hN : 0 < N)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    |inner ℝ x (gradient (Hamiltonian N p J) x)/(N : ℝ)| ≤
      (p : ℝ)*landscapeNorm N p J := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr := Real.sqrt_pos.mpr hNr
  rw [abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  have hg := (div_le_iff₀ hr).mp (Hamiltonian_gradient_sphere_bound hN J x hx)
  calc
    _ ≤ ‖x‖*‖gradient (Hamiltonian N p J) x‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (N : ℝ)*((p : ℝ)*landscapeNorm N p J*Real.sqrt (N : ℝ)) := by
      rw [sphere_norm x hx]
      exact mul_le_mul_of_nonneg_left hg hr.le
    _ = _ := by rw [mul_left_comm, Real.mul_self_sqrt hNr.le]

theorem sphericalHessian_sphere_bound {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    ‖sphericalHessian J x‖ ≤ (p : ℝ)^2*landscapeNorm N p J := by
  have hP := tangentProjection_norm_le hN x hx
  have hH := Hamiltonian_hessian_sphere_bound hN hp J x hx
  have hρ := radial_gradient_sphere_bound hN J x hx
  have hPHP : ‖(tangentProjection x).comp
      ((fderiv ℝ (gradient (Hamiltonian N p J)) x).comp (tangentProjection x))‖ ≤
      ‖fderiv ℝ (gradient (Hamiltonian N p J)) x‖ := by
    calc
      _ ≤ ‖tangentProjection x‖*‖(fderiv ℝ (gradient (Hamiltonian N p J)) x).comp
          (tangentProjection x)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1*‖(fderiv ℝ (gradient (Hamiltonian N p J)) x).comp (tangentProjection x)‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ ‖fderiv ℝ (gradient (Hamiltonian N p J)) x‖ := by
        rw [one_mul]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by simpa using mul_le_mul_of_nonneg_left hP (norm_nonneg _))
  have hρP : ‖(inner ℝ x (gradient (Hamiltonian N p J) x)/(N : ℝ)) • tangentProjection x‖ ≤
      (p : ℝ)*landscapeNorm N p J := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) hP).trans hρ
  unfold sphericalHessian
  exact (norm_sub_le _ _).trans ((add_le_add (hPHP.trans hH) hρP).trans_eq (by ring))

/-- The Laplace–Beltrami operator is the trace of the tangent Hessian. -/
@[expose] def sphericalLaplacian {N p : ℕ} (J : Disorder N p) (x : Vector N) : ℝ :=
  ∑ i : Fin N, inner ℝ (HardSphereDynamics.basisVector i)
    (sphericalHessian J x (HardSphereDynamics.basisVector i))

theorem sphericalLaplacian_sphere_bound {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    |sphericalLaplacian J x|/(N : ℝ) ≤ (p : ℝ)^2*landscapeNorm N p J := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  unfold sphericalLaplacian
  calc
    _ ≤ ∑ i : Fin N, |inner ℝ (HardSphereDynamics.basisVector i)
        (sphericalHessian J x (HardSphereDynamics.basisVector i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (p : ℝ)^2*landscapeNorm N p J := by
      apply Finset.sum_le_sum
      intro i _
      have he : ‖HardSphereDynamics.basisVector i‖ = 1 := by
        simp [HardSphereDynamics.basisVector]
      have hi := abs_real_inner_le_norm (HardSphereDynamics.basisVector i)
        (sphericalHessian J x (HardSphereDynamics.basisVector i))
      rw [he, one_mul] at hi
      exact hi.trans (((sphericalHessian J x).le_opNorm _).trans
        (by rw [he, mul_one]; exact sphericalHessian_sphere_bound hN hp J x hx))
    _ = _ := by simp; ring

/-- All five deterministic inequalities of manuscript Lemma 3.6. -/
theorem landscape_derivative_bounds {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (J : Disorder N p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    |Hamiltonian N p J x|/(N : ℝ) ≤ landscapeNorm N p J ∧
    ‖gradient (Hamiltonian N p J) x‖/Real.sqrt (N : ℝ) ≤ (p : ℝ)*landscapeNorm N p J ∧
    ‖fderiv ℝ (gradient (Hamiltonian N p J)) x‖ ≤
      (p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J ∧
    |sphericalLaplacian J x|/(N : ℝ) ≤ (p : ℝ)^2*landscapeNorm N p J ∧
    ‖sphericalHessian J x‖ ≤ (p : ℝ)^2*landscapeNorm N p J :=
  ⟨Hamiltonian_sphere_bound hN (by omega) J x hx,
    Hamiltonian_gradient_sphere_bound hN J x hx,
    Hamiltonian_hessian_sphere_bound hN hp J x hx,
    sphericalLaplacian_sphere_bound hN hp J x hx,
    sphericalHessian_sphere_bound hN hp J x hx⟩

/-- The full manuscript landscape lemma, with actual Gaussian moments,
the exact sphere supremum Q_N, and actual Euclidean/extrinsic sphere derivatives. -/
theorem landscape_lemma (p : ℕ) (hp : 3 ≤ p) :
    (∀ k : ℝ, 0 ≤ k → ∃ M : ℝ, ∀ N : ℕ, 1 ≤ N →
      MeasureTheory.Integrable (fun J : Disorder N p => (landscapeNorm N p J)^k) (disorderLaw N p) ∧
        (∫ J : Disorder N p, (landscapeNorm N p J)^k ∂disorderLaw N p) ≤ M) ∧
    (∀ b : ℝ, ∃ M : ℝ, ∀ N : ℕ, 1 ≤ N →
      MeasureTheory.Integrable (fun J : Disorder N p => Real.exp (b*landscapeNorm N p J)) (disorderLaw N p) ∧
        (∫ J : Disorder N p, Real.exp (b*landscapeNorm N p J) ∂disorderLaw N p) ≤ M) ∧
    (∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
      (disorderLaw N p).real {J | A < landscapeNorm N p J} ≤ Real.exp (-c*N)) ∧
    (∀ N : ℕ, 0 < N → ∀ J : Disorder N p, ∀ x : Vector N, ‖x‖^2=(N : ℝ) →
      |Hamiltonian N p J x|/(N : ℝ) ≤ landscapeNorm N p J ∧
      ‖gradient (Hamiltonian N p J) x‖/Real.sqrt (N : ℝ) ≤ (p : ℝ)*landscapeNorm N p J ∧
      ‖fderiv ℝ (gradient (Hamiltonian N p J)) x‖ ≤
        (p : ℝ)*((p : ℝ)-1)*landscapeNorm N p J ∧
      |sphericalLaplacian J x|/(N : ℝ) ≤ (p : ℝ)^2*landscapeNorm N p J ∧
      ‖sphericalHessian J x‖ ≤ (p : ℝ)^2*landscapeNorm N p J) := by
  obtain ⟨hpow,hexp,htail⟩ := GaussianLandscapeMoments.landscape_probabilistic_bounds p (by omega)
  exact ⟨hpow,hexp,htail,fun _ hN J x hx => landscape_derivative_bounds hN (by omega) J x hx⟩

end SphericalAging.LandscapeDerivatives
