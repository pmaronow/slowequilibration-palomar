-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1GeneratorSubsolution
public import SlowEquilibration.SphericalForm

/-! Actual exponential-overlap generator and moment bounds for the physical
C1-gradient spherical diffusion. The only field size input is its genuine
uniform gradient norm bound on the sphere. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalOverlapExponential
open MeasureTheory ProbabilityTheory Set Filter
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalC1Dynamics SphericalReversibility.Ito MultivariateTaylor
open scoped NNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def overlapLinear (u : State N) : State N →L[ℝ] ℝ := (N : ℝ)⁻¹ • innerSL ℝ u
def overlapValue (u x : State N) : ℝ := overlapLinear u x
def expLinear (L : State N →L[ℝ] ℝ) (x : State N) : ℝ := Real.exp (L x)
def expOverlap (u : State N) (ell : ℝ) : State N → ℝ := expLinear (ell • overlapLinear u)

lemma overlapValue_eq (u x : State N) : overlapValue u x = inner ℝ u x / (N : ℝ) := by
  simp only [overlapValue,overlapLinear,_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,div_eq_inv_mul]

lemma expLinear_contDiff (L : State N →L[ℝ] ℝ) : ContDiff ℝ 2 (expLinear L) :=
  L.contDiff.exp

lemma fderiv_expLinear (L : State N →L[ℝ] ℝ) (x : State N) :
    fderiv ℝ (expLinear L) x = Real.exp (L x) • L :=
  L.hasFDerivAt.exp.fderiv

lemma hessian_expLinear (L : State N →L[ℝ] ℝ) (x v w : State N) :
    Hessian (expLinear L) x v w = Real.exp (L x) * L v * L w := by
  have he : fderiv ℝ (expLinear L) = fun y => Real.exp (L y) • L :=
    funext (fderiv_expLinear L)
  unfold Hessian
  rw [he,(L.hasFDerivAt.exp.smul_const L).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply,_root_.smul_apply,smul_eq_mul]

lemma generator_expLinear (β : ℝ) (g : State N → State N)
    (L : State N →L[ℝ] ℝ) (x : State N) :
    coefficientGenerator β g (expLinear L) x =
      Real.exp (L x) * (L (drift β g x) + (1 / 2 : ℝ) * ∑ j : Fin N, (L (noiseColumn x j)) ^ 2) := by
  unfold coefficientGenerator
  rw [fderiv_expLinear]
  simp only [_root_.smul_apply,smul_eq_mul]
  simp_rw [hessian_expLinear,mul_assoc]
  rw [← Finset.mul_sum]
  simp only [pow_two]
  ring

lemma overlapValue_abs_le_one (hN : N ≠ 0) (u x : State N)
    (hu : OnSphere u) (hx : OnSphere x) : |overlapValue u x| ≤ 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hnu := LandscapeDerivatives.sphere_norm u ((onSphere_iff_norm_sq u).mp hu)
  have hnx := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  rw [overlapValue_eq,abs_div,abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  have hi := abs_real_inner_le_norm u x
  rw [hnu,hnx,← pow_two,Real.sq_sqrt hNr.le] at hi
  simpa only [one_mul] using hi

lemma kappa_mem (hN : N ≠ 0) : kappa N ∈ Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
  unfold kappa
  constructor
  · exact div_nonneg (by linarith) hNr.le
  · apply (div_le_iff₀ hNr).mpr
    linarith

lemma drift_norm_le (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (_hC : 0 ≤ C)
    (g : State N → State N) (hgrad : ∀ x,OnSphere x → ‖g x‖ ≤ C * Real.sqrt (N : ℝ))
    (x : State N) (hx : OnSphere x) :
    ‖drift β g x‖ ≤ (1 + β * C) * Real.sqrt (N : ℝ) := by
  have hk := kappa_mem hN
  have hnx := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  have hg := (projection_norm_le_onSphere hN x (g x) hx).trans (hgrad x hx)
  have hd := norm_sub_le (β • projection x (g x)) (kappa N • x)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hβ,abs_of_nonneg hk.1,hnx] at hd
  have h1 := mul_le_mul_of_nonneg_left hg hβ
  have h2 := mul_le_mul_of_nonneg_right hk.2 (Real.sqrt_nonneg (N : ℝ))
  unfold drift
  nlinarith

lemma overlap_drift_abs_le (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hgrad : ∀ x,OnSphere x → ‖g x‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) :
    |overlapLinear u (drift β g x)| ≤ 1 + β * C := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hnu := LandscapeDerivatives.sphere_norm u ((onSphere_iff_norm_sq u).mp hu)
  have hd := drift_norm_le hN hβ hC g hgrad x hx
  change |overlapValue u (drift β g x)| ≤ _
  rw [overlapValue_eq,abs_div,abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  have hi := (abs_real_inner_le_norm u (drift β g x)).trans
    (mul_le_mul_of_nonneg_left hd (norm_nonneg u))
  rw [hnu] at hi
  have he : Real.sqrt (N : ℝ) * ((1 + β * C) * Real.sqrt (N : ℝ)) = (1 + β * C) * (N : ℝ) := by
    calc
      _ = (1 + β * C) * (Real.sqrt (N : ℝ)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hNr.le]
  rw [he] at hi
  exact hi

lemma noise_inner (u x : State N) (j : Fin N) :
    inner ℝ u (noiseColumn x j) = Real.sqrt 2 * (projection x u) j := by
  rw [noiseColumn,real_inner_smul_right,← projection_self_adjoint x u (basisVector j)]
  simp [basisVector,EuclideanSpace.inner_single_right]

lemma overlap_noise_sq_sum_le (hN : N ≠ 0) (u x : State N)
    (hu : OnSphere u) (hx : OnSphere x) :
    (1 / 2 : ℝ) * (∑ j : Fin N,(overlapLinear u (noiseColumn x j)) ^ 2) ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hp := (sq_le_sq₀ (norm_nonneg (projection x u)) (norm_nonneg u)).mpr
    (projection_norm_le_onSphere hN x u hx)
  rw [(onSphere_iff_norm_sq u).mp hu,EuclideanSpace.real_norm_sq_eq] at hp
  have he (j : Fin N) : (overlapLinear u (noiseColumn x j)) ^ 2 =
      2 / (N : ℝ) ^ 2 * ((projection x u) j) ^ 2 := by
    change (overlapValue u (noiseColumn x j)) ^ 2 = _
    rw [overlapValue_eq,noise_inner,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have ht := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 / (N : ℝ) ^ 2)
  calc
    _ ≤ (1 / 2 : ℝ) * ((2 / (N : ℝ) ^ 2) * (N : ℝ)) := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = _ := by field_simp

lemma expOverlap_generator_le (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hgrad : ∀ x,OnSphere x → ‖g x‖ ≤ C * Real.sqrt (N : ℝ))
    (u : State N) (hu : OnSphere u) (ell : ℝ) (x : State N) (hx : OnSphere x) :
    coefficientGenerator β g (expOverlap u ell) x ≤
      (|ell| * (1 + β * C) + ell ^ 2 / (N : ℝ)) * expOverlap u ell x := by
  have hd := overlap_drift_abs_le hN hβ hC g hgrad u x hu hx
  have hn := overlap_noise_sq_sum_le hN u x hu hx
  rw [expOverlap,generator_expLinear]
  simp only [_root_.smul_apply,smul_eq_mul,mul_pow]
  rw [← Finset.mul_sum]
  have hdl : ell * overlapLinear u (drift β g x) ≤ |ell| * (1 + β * C) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hd (abs_nonneg ell))
  have hnq := mul_le_mul_of_nonneg_left hn (sq_nonneg ell)
  have hnq' : (1 / 2 : ℝ) * (ell ^ 2 * ∑ j : Fin N,(overlapLinear u (noiseColumn x j)) ^ 2) ≤
      ell ^ 2 / (N : ℝ) := by
    convert hnq using 1 <;> ring
  have hinner : ell * overlapLinear u (drift β g x) + (1 / 2 : ℝ) *
      (ell ^ 2 * ∑ j : Fin N,(overlapLinear u (noiseColumn x j)) ^ 2) ≤
      |ell| * (1 + β * C) + ell ^ 2 / (N : ℝ) := add_le_add hdl hnq'
  exact (mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le).trans_eq (by simp only [expLinear,_root_.smul_apply,smul_eq_mul]; ring)

/-- Genuine overlap exponential moment for the original C1 sphere process. -/
theorem overlap_increment_mgf (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ x,OnSphere x → ‖g x‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) (ell : ℝ) (t : ℝ≥0) :
    (∫ omega,Real.exp (ell * (overlapValue u (process β g hg x t omega) - overlapValue u x))
      ∂VectorBrownian.law N) ≤
      Real.exp ((|ell| * (1 + β * C) + ell ^ 2 / (N : ℝ)) * (t : ℝ)) := by
  have hf := expLinear_contDiff (ell • overlapLinear u)
  have hi := expectation_le_exp_mul hN β g hg x hx hf
    (|ell| * (1 + β * C) + ell ^ 2 / (N : ℝ))
    (fun y hy => expOverlap_generator_le hN hβ hC g hgrad u hu ell y hy) t
  change expectation β g hg t (expOverlap u ell) x ≤
    Real.exp ((|ell| * (1 + β * C) + ell ^ 2 / (N : ℝ)) * (t : ℝ)) * expOverlap u ell x at hi
  have he : (∫ omega,Real.exp (ell * (overlapValue u (process β g hg x t omega) - overlapValue u x))
      ∂VectorBrownian.law N) = Real.exp (-ell * overlapValue u x) * expectation β g hg t (expOverlap u ell) x := by
    unfold expectation
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun omega => by
      simp only [expOverlap,expLinear,_root_.smul_apply,smul_eq_mul,overlapValue]
      rw [← Real.exp_add]
      congr 1
      ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hi (Real.exp_pos (-ell * overlapValue u x)).le
  have hc : Real.exp (-ell * overlapValue u x) *
      (Real.exp ((|ell| * (1 + β * C) + ell ^ 2 / (N : ℝ)) * (t : ℝ)) * expOverlap u ell x) =
      Real.exp ((|ell| * (1 + β * C) + ell ^ 2 / (N : ℝ)) * (t : ℝ)) := by
    unfold expOverlap expLinear overlapValue
    simp only [_root_.smul_apply,smul_eq_mul]
    rw [mul_left_comm,← Real.exp_add]
    simp
  rw [hc] at hm
  exact hm

lemma expOverlap_generator_ge (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hgrad : ∀ x,OnSphere x → ‖g x‖ ≤ C * Real.sqrt (N : ℝ))
    (u : State N) (hu : OnSphere u) (ell : ℝ) (x : State N) (hx : OnSphere x) :
    (-|ell| * (1 + β * C)) * expOverlap u ell x ≤ coefficientGenerator β g (expOverlap u ell) x := by
  have hd := overlap_drift_abs_le hN hβ hC g hgrad u x hu hx
  have hab : |ell * overlapLinear u (drift β g x)| ≤ |ell| * (1 + β * C) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hd (abs_nonneg ell)
  have hl := (abs_le.mp hab).1
  have hq : 0 ≤ (1 / 2 : ℝ) * ∑ j : Fin N,((ell • overlapLinear u) (noiseColumn x j)) ^ 2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [expOverlap,generator_expLinear]
  simp only [expLinear,_root_.smul_apply,smul_eq_mul] at hq ⊢
  have hi : -|ell| * (1 + β * C) ≤ ell * overlapLinear u (drift β g x) +
      (1 / 2 : ℝ) * ∑ j : Fin N,(ell * overlapLinear u (noiseColumn x j)) ^ 2 := by linarith
  calc
    _ = Real.exp (ell * overlapLinear u x) * (-|ell| * (1 + β * C)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (Real.exp_pos (ell * overlapLinear u x)).le

theorem expectation_expOverlap_lower (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ x,OnSphere x → ‖g x‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) (ell : ℝ) (t : ℝ≥0) :
    Real.exp ((-|ell| * (1 + β * C)) * (t : ℝ)) * expOverlap u ell x ≤
      expectation β g hg t (expOverlap u ell) x :=
  expectation_ge_exp_mul hN β g hg x hx (expLinear_contDiff (ell • overlapLinear u))
    (-|ell| * (1 + β * C)) (fun y hy => expOverlap_generator_ge hN hβ hC g hgrad u hu ell y hy) t

end SlowEquilibration.SphericalOverlapExponential
