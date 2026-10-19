-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteTensorMixtureMaximum
public import SlowEquilibration.GaussianCompactFeatureComparison

@[expose] public section

/-! Literal finite spin-label Gaussian fields for a positive-lower-atom
one-step spherical upper comparison. The original field, scalar label
compensation, common linear field and independent label linear fields are
actual disjoint standard Gaussian coordinate banks. No cascade or Ising
physical equivalence is used. -/

namespace SlowEquilibration.SphericalParisiLabeledCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum GaussianCompactFeatureComparison
open PureTensorJetBounds
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1000000

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def xi (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) : ℝ := ∑ i,c i*r^(d i)
def xi1 (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) : ℝ :=
  ∑ i,c i*(d i : ℝ)*r^(d i-1)
def theta (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) : ℝ := r*xi1 d c r-xi d c r
def bregmanGap (d : σ → ℕ) (c : σ → ℝ) (r q : ℝ) : ℝ :=
  xi d c r-xi d c q-xi1 d c q*(r-q)

omit [DecidableEq σ] in
theorem xi1_nonnegative (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ xi1 d c r :=
  Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (hc i) (Nat.cast_nonneg _)) (pow_nonneg hr _))

omit [DecidableEq σ] in
theorem xi1_monotone_positive (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : xi1 d c r ≤ xi1 d c s := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs _)
    (mul_nonneg (hc i) (Nat.cast_nonneg _))

omit [DecidableEq σ] in
theorem theta_eq_positive_polynomial (d : σ → ℕ) (c : σ → ℝ)
    (hd : ∀ i,1 ≤ d i) (r : ℝ) :
    theta d c r=∑ i,c i*((d i-1 : ℕ) : ℝ)*r^(d i) := by
  unfold theta xi1 xi
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : r*r^(d i-1)=r^(d i) := by
    rw [← pow_succ',Nat.sub_add_cancel (hd i)]
  rw [Nat.cast_sub (hd i)]
  norm_num only [Nat.cast_one]
  calc
    _ = c i*(d i : ℝ)*(r*r^(d i-1))-c i*r^(d i) := by ring
    _ = _ := by rw [hp];ring

omit [DecidableEq σ] in
theorem theta_monotone_positive (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : theta d c r ≤ theta d c s := by
  rw [theta_eq_positive_polynomial d c hd,theta_eq_positive_polynomial d c hd]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs _)
    (mul_nonneg (hc i) (Nat.cast_nonneg _))

def taggedVector {N k : ℕ} (a : Fin k) (x : Vector N) : EuclideanSpace ℝ (Fin k × Fin N) :=
  WithLp.toLp 2 (fun i => if i.1=a then x i.2 else 0)

/-- The actual label coordinate banks are orthogonal, with the precise
physical linear covariance on each label. -/
theorem taggedVector_inner {N k : ℕ} (a b : Fin k) (x y : Vector N) :
    inner ℝ (taggedVector a x) (taggedVector b y) =
      if a=b then inner ℝ x y else 0 := by
  simp only [taggedVector,PiLp.inner_apply,Fintype.sum_prod_type,RCLike.inner_apply,conj_trivial]
  by_cases hab : a=b
  · subst b
    simp
  · simp [hab]

private theorem sumJoin_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : EuclideanSpace ℝ ι) (u v : EuclideanSpace ℝ κ) :
    inner ℝ (sumJoin (x,u)) (sumJoin (y,v))=inner ℝ x y+inner ℝ u v := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

/-- Actual original tensor field together with an independent scalar
Gaussian for each label. -/
def originalFeature {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (Δ : ℝ)
    (z : UnitSphere N × Fin k) :
    EuclideanSpace ℝ (Coordinate N d ⊕ Fin k) :=
  sumJoin (feature d c z.1.val,(Real.sqrt (N : ℝ)*Real.sqrt Δ) • EuclideanSpace.single z.2 (1 : ℝ))

/-- Actual common and independent-per-label linear Gaussian fields. -/
def trialFeature {N k : ℕ} (a b : ℝ) (z : UnitSphere N × Fin k) :
    EuclideanSpace ℝ (Fin N ⊕ (Fin k × Fin N)) :=
  sumJoin ((Real.sqrt (N : ℝ)*Real.sqrt a) • z.1.val,
    (Real.sqrt (N : ℝ)*Real.sqrt b) • taggedVector z.2 z.1.val)

theorem originalFeature_inner {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) {Δ : ℝ} (hΔ : 0 ≤ Δ) (z w : UnitSphere N × Fin k) :
    inner ℝ (originalFeature d c Δ z) (originalFeature d c Δ w) =
      (N : ℝ)*(xi d c (inner ℝ z.1.val w.1.val)+if z.2=w.2 then Δ else 0) := by
  rw [originalFeature,originalFeature,sumJoin_inner,feature_inner d c hc]
  simp only [real_inner_smul_left,real_inner_smul_right]
  have hs : (Real.sqrt (N : ℝ)*Real.sqrt Δ)^2=(N : ℝ)*Δ := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hΔ]
  by_cases hz : z.2=w.2
  · simp only [hz,ite_true,EuclideanSpace.inner_single_left,PiLp.single_apply,mul_one,map_one]
    unfold xi
    calc
      _ = (N : ℝ)*(∑ i,c i*(inner ℝ z.1.val w.1.val)^(d i))+
          (Real.sqrt (N : ℝ)*Real.sqrt Δ)^2 := by ring
      _ = _ := by rw [hs];ring
  · simp only [EuclideanSpace.inner_single_left,PiLp.single_apply,
      ite_false,mul_zero,add_zero,hz]
    rfl

theorem trialFeature_inner {N k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z w : UnitSphere N × Fin k) :
    inner ℝ (trialFeature a b z) (trialFeature a b w)=
      (N : ℝ)*(inner ℝ z.1.val w.1.val)*(a+if z.2=w.2 then b else 0) := by
  rw [trialFeature,trialFeature,sumJoin_inner]
  simp only [real_inner_smul_left,real_inner_smul_right,taggedVector_inner]
  have ha' : (Real.sqrt (N : ℝ)*Real.sqrt a)^2=(N : ℝ)*a := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt ha]
  have hb' : (Real.sqrt (N : ℝ)*Real.sqrt b)^2=(N : ℝ)*b := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hb]
  calc
    _ = (Real.sqrt (N : ℝ)*Real.sqrt a)^2*(inner ℝ z.1.val w.1.val)+
        (Real.sqrt (N : ℝ)*Real.sqrt b)^2*(if z.2=w.2 then inner ℝ z.1.val w.1.val else 0) := by ring
    _ = _ := by rw [ha',hb'];split_ifs <;> ring

/-- Exact one-step Guerra kernel with an arbitrary positive lower overlap
atom. Its covariance is computed from the original Gaussian coordinate
banks. The constant theta(q0) cancels from the diagonal/pair trace. -/
theorem actual_labeled_covariance_difference {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (q0 q1 : ℝ)
    (ha : 0 ≤ xi1 d c q0) (hb : 0 ≤ xi1 d c q1-xi1 d c q0)
    (hΔ : 0 ≤ theta d c q1-theta d c q0) (z w : UnitSphere N × Fin k) :
    inner ℝ (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z)
      (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) w)-
    inner ℝ (originalFeature d c (theta d c q1-theta d c q0) z)
      (originalFeature d c (theta d c q1-theta d c q0) w) =
      (N : ℝ)*(theta d c q0-
        bregmanGap d c (inner ℝ z.1.val w.1.val) (if z.2=w.2 then q1 else q0)) := by
  rw [trialFeature_inner ha hb,originalFeature_inner d c hc hΔ]
  split_ifs <;> simp only [theta,bregmanGap] <;> ring

/-- All Gaussian variance inputs for the true labeled one-step model are
derived from the original nonnegative polynomial coefficients, allowing
linear and odd degrees. -/
theorem actual_labeled_covariance_difference_of_positive_coefficients {N k : ℕ}
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    {q0 q1 : ℝ} (hq0 : 0 ≤ q0) (hqq : q0 ≤ q1) (z w : UnitSphere N × Fin k) :
    inner ℝ (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z)
      (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) w)-
    inner ℝ (originalFeature d c (theta d c q1-theta d c q0) z)
      (originalFeature d c (theta d c q1-theta d c q0) w) =
      (N : ℝ)*(theta d c q0-
        bregmanGap d c (inner ℝ z.1.val w.1.val) (if z.2=w.2 then q1 else q0)) :=
  actual_labeled_covariance_difference d c hc q0 q1 (xi1_nonnegative d c hc hq0)
    (sub_nonneg.mpr (xi1_monotone_positive d c hc hq0 hqq))
    (sub_nonneg.mpr (theta_monotone_positive d c hc hd hq0 hqq)) z w

end
end SlowEquilibration.SphericalParisiLabeledCovariance
