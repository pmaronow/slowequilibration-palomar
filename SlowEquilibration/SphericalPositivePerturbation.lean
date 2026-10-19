-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationResponse
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-! # Literal finite tensor perturbation for spherical overlap positivity

The degree-one-through-K tensor coefficients are actual finite Gaussian
coordinates. The proved feature Gram kernel is the ordinary overlap-power
covariance, and each selected degree has its literal diagonal energy. This
constructs the perturbation used in the GG argument without assuming its
positivity or moment identities.
-/

namespace SlowEquilibration.SphericalPositivePerturbation
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

abbrev TensorCoordinate (N K : ℕ) := (p : Fin K) × TensorIndex N (p.val+1)
abbrev PerturbationDisorder (N K : ℕ) := EuclideanSpace ℝ (TensorCoordinate N K)

def feature {N K : ℕ} (a : Fin K → ℝ) (z : Vector N) : PerturbationDisorder N K :=
  WithLp.toLp 2 (fun i => a i.1*tensorMonomial z i.2)

def linear {N K : ℕ} (a : Fin K → ℝ) (z : Vector N) : PerturbationDisorder N K →L[ℝ] ℝ :=
  innerSL ℝ (feature a z)

theorem feature_continuous {N K : ℕ} (a : Fin K → ℝ) : Continuous (feature (N := N) a) := by
  unfold feature tensorMonomial
  fun_prop

theorem linear_measurable {N K : ℕ} (a : Fin K → ℝ) : Measurable (linear (N := N) a) :=
  ((innerSL ℝ).continuous.comp (feature_continuous a)).measurable

/-- The actual Gaussian feature kernel includes all odd degrees and the
linear perturbation degree. -/
theorem feature_inner {N K : ℕ} (a b : Fin K → ℝ) (z y : Vector N) :
    inner ℝ (feature a z) (feature b y) =
      ∑ p : Fin K, a p*b p*(inner ℝ z y)^(p.val+1) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,feature,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  have heq : (fun I : TensorIndex N (p.val+1) =>
      (b p*tensorMonomial y I)*(a p*tensorMonomial z I)) =
      fun I => (a p*b p)*(tensorMonomial z I*tensorMonomial y I) := by
    funext I;ring
  rw [heq,← Finset.mul_sum,tensorMonomial_gram]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]

theorem feature_norm_sq {N K : ℕ} (a : Fin K → ℝ) (z : Vector N) (hz : ‖z‖=1) :
    ‖feature a z‖^2 = ∑ p : Fin K, (a p)^2 := by
  rw [← real_inner_self_eq_norm_sq,feature_inner,real_inner_self_eq_norm_sq,hz]
  simp only [one_pow,mul_one,pow_two]

theorem feature_norm_le {N K : ℕ} (a : Fin K → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ha : (∑ p : Fin K,(a p)^2) ≤ B^2) (z : Vector N) (hz : ‖z‖=1) :
    ‖feature a z‖ ≤ B := by
  apply (sq_le_sq₀ (norm_nonneg _) hB).mp
  rw [feature_norm_sq a z hz]
  exact ha

theorem linear_coordinate {N K : ℕ} (a : Fin K → ℝ) (z : Vector N) (i : TensorCoordinate N K) :
    linear a z (EuclideanSpace.single i 1)=a i.1*tensorMonomial z i.2 := by
  simp only [linear,innerSL_apply_apply,EuclideanSpace.inner_single_right,feature,conj_trivial,one_mul]

def degreeLabel {N K : ℕ} (p : Fin K) (i : TensorCoordinate N K) : Bool := decide (i.1=p)

/-- The selected-coordinate diagonal is the actual pure-degree tensor
energy, proved from the ordinary monomial Gram identity. -/
theorem active_diagonal {N K : ℕ} (a : Fin K → ℝ) (p : Fin K)
    (z : Vector N) (hz : ‖z‖=1) :
    (∑ i : TensorCoordinate N K, if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable (linear a) i z)^2 else 0) = (a p)^2 := by
  classical
  simp only [GaussianSpinComparison.coordinateObservable,linear_coordinate,degreeLabel,decide_eq_true_eq,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true,mul_pow,← Finset.mul_sum]
    have heq : (∑ I : TensorIndex N (p.val+1),(tensorMonomial z I)^2) = 1 := by
      simp only [pow_two]
      rw [tensorMonomial_gram,real_inner_self_eq_norm_sq,hz]
      simp
    rw [heq,mul_one]
  · intro j _ hj
    simp [hj]
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

/-- The genuine geometric coefficient budget does not grow with the
number of tensor degrees. -/
theorem geometric_budget (K : ℕ) :
    (∑ p : Fin K,(1/4 : ℝ)^(p.val+1)) ≤ (1/3 : ℝ) := by
  have h := geom_sum_mul_neg (1/4 : ℝ) K
  have heq : (∑ p : Fin K,(1/4 : ℝ)^(p.val+1)) =
      (1/4 : ℝ)*(∑ i ∈ Finset.range K,(1/4 : ℝ)^i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (1/4 : ℝ)^(i+1))]
    simp only [pow_succ,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _;ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) K]

def coefficients {K : ℕ} (v : ℝ) (x : Fin K → ℝ) (p : Fin K) : ℝ :=
  v*(1/2 : ℝ)^(p.val+1)*x p

theorem coefficients_budget {K : ℕ} (v : ℝ) (x : Fin K → ℝ)
    (hx : ∀ p, |x p| ≤ 2) :
    (∑ p : Fin K,(coefficients v x p)^2) ≤ (2*v)^2 := by
  have hs : (∑ p : Fin K,(coefficients v x p)^2) ≤
      (4*v^2)*(∑ p : Fin K,(1/4 : ℝ)^(p.val+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    have hxp : (x p)^2 ≤ 4 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr (hx p)
      simpa only [sq_abs,show (2 : ℝ)^2=4 by norm_num] using hh
    have hpow : ((1/2 : ℝ)^(p.val+1))^2=(1/4 : ℝ)^(p.val+1) := by
      rw [← pow_mul,pow_mul',show (1/2 : ℝ)^2=1/4 by norm_num]
    dsimp [coefficients]
    rw [mul_pow,mul_pow,hpow]
    nlinarith [mul_le_mul_of_nonneg_left hxp (mul_nonneg (sq_nonneg v)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) (p.val+1)))]
  have hg := mul_le_mul_of_nonneg_left (geometric_budget K) (by positivity : 0 ≤ 4*v^2)
  nlinarith

/-- The actual finite positivity perturbation has feature norm at most
2v uniformly on the unit sphere and uniformly in its number of degrees. -/
theorem perturbation_linear_bound {N K : ℕ} {v : ℝ} (hv : 0 ≤ v) (x : Fin K → ℝ)
    (hx : ∀ p, |x p| ≤ 2) (z : Vector N) (hz : ‖z‖=1) :
    ‖linear (coefficients v x) z‖ ≤ 2*v := by
  rw [linear,innerSL_apply_norm]
  exact feature_norm_le _ (by positivity) (coefficients_budget v x hx) z hz

end
end SlowEquilibration.SphericalPositivePerturbation
