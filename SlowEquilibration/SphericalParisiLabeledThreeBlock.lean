-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledCovariance
public import SlowEquilibration.SphericalPositivePerturbation
public import SlowEquilibration.GaussianThreeBlockComparison

@[expose] public section

/-! Actual original/linear-trial/held-perturbation Gaussian banks on the
literal finite spherical spin-label space. The perturbation is unchanged
under the real Gaussian rotation and cancels from the signed covariance.
All tensor and tagged coordinates remain the original finite coordinates. -/

namespace SlowEquilibration.SphericalParisiLabeledThreeBlock

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance GaussianCompactFeatureComparison
open scoped RealInnerProductSpace BigOperators
set_option maxHeartbeats 1000000

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev OriginalCoordinate (N k : ℕ) (d : σ → ℕ) := Coordinate N d ⊕ Fin k
abbrev TrialCoordinate (N k : ℕ) := Fin N ⊕ (Fin k × Fin N)
abbrev BaseCoordinate (N k : ℕ) (d : σ → ℕ) := OriginalCoordinate N k d ⊕ TrialCoordinate N k
abbrev ThreeCoordinate (N k K : ℕ) (d : σ → ℕ) :=
  BaseCoordinate N k d ⊕ SphericalPositivePerturbation.TensorCoordinate N K

instance threeCoordinate_decidableEq (N k K : ℕ) (d : σ → ℕ) :
    DecidableEq (ThreeCoordinate N k K d) := Classical.decEq _

private theorem sumJoin_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) (i : ι) :
    sumJoin (u,w) (Sum.inl i)=u i := rfl

private theorem sumJoin_inr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) (i : κ) :
    sumJoin (u,w) (Sum.inr i)=w i := rfl

def threeLabel {N k K : ℕ} {d : σ → ℕ} : ThreeCoordinate N k K d → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

def threeFeature {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) (z : UnitSphere N × Fin k) :
    EuclideanSpace ℝ (ThreeCoordinate N k K d) :=
  sumJoin (sumJoin
    (β • originalFeature d c (theta d c q1-theta d c q0) z,
      β • trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z),
    SphericalPositivePerturbation.feature (SphericalPositivePerturbation.coefficients v x) z.1.val)

def threeLinear {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) (z : UnitSphere N × Fin k) :
    EuclideanSpace ℝ (ThreeCoordinate N k K d) →L[ℝ] ℝ :=
  innerSL ℝ (threeFeature d c β q0 q1 v x z)

omit [DecidableEq σ] in
theorem actual_three_coordinate {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) (z : UnitSphere N × Fin k)
    (i : ThreeCoordinate N k K d) :
    GaussianThreeBlockComparison.coordinateObservable (threeLinear d c β q0 q1 v x) i z =
      threeFeature d c β q0 q1 v x z i := by
  rw [GaussianThreeBlockComparison.coordinateObservable,threeLinear,
    innerSL_apply_apply,EuclideanSpace.inner_single_right]
  simp only [conj_trivial,one_mul]

omit [DecidableEq σ] in
/-- The actual held tensor perturbation has zero covariance sign. -/
theorem actual_three_signedKernel_difference {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) (z w : UnitSphere N × Fin k) :
    GaussianThreeBlockComparison.signedKernel (threeLinear d c β q0 q1 v x) threeLabel z w =
      β^2*(inner ℝ
        (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z)
        (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) w)-
      inner ℝ (originalFeature d c (theta d c q1-theta d c q0) z)
        (originalFeature d c (theta d c q1-theta d c q0) w)) := by
  unfold GaussianThreeBlockComparison.signedKernel
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [actual_three_coordinate,
    GaussianThreeBlockComparison.covarianceSign,threeLabel,threeFeature,
    sumJoin_inl,sumJoin_inr,PiLp.smul_apply,smul_eq_mul]
  simp only [ite_true,show (0 : Fin 3) ≠ 1 by decide,
    show (1 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false,neg_one_mul,one_mul,zero_mul,
    Finset.sum_const_zero]
  change (∑ i : OriginalCoordinate N k d,
      -(β*originalFeature d c (theta d c q1-theta d c q0) z i*
        (β*originalFeature d c (theta d c q1-theta d c q0) w i)))+
      (∑ i : TrialCoordinate N k,
        β*trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z i*
          (β*trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) w i))+0 = _
  have hA : (∑ i : OriginalCoordinate N k d,
      -(β*originalFeature d c (theta d c q1-theta d c q0) z i*
        (β*originalFeature d c (theta d c q1-theta d c q0) w i)))=
      -β^2*inner ℝ (originalFeature d c (theta d c q1-theta d c q0) z)
        (originalFeature d c (theta d c q1-theta d c q0) w) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hB : (∑ i : TrialCoordinate N k,
        β*trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z i*
          (β*trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) w i))=
      β^2*inner ℝ
        (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z)
        (trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) w) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hA,hB]
  ring

/-- Literal all-parity one-step kernel on the actual spin-label space,
with every positivity input derived from actual polynomial coefficients. -/
theorem actual_three_signedKernel {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    (β v : ℝ) {q0 q1 : ℝ} (hq0 : 0 ≤ q0) (hqq : q0 ≤ q1)
    (x : Fin K → ℝ) (z w : UnitSphere N × Fin k) :
    GaussianThreeBlockComparison.signedKernel (threeLinear d c β q0 q1 v x) threeLabel z w =
      (N : ℝ)*β^2*(theta d c q0-
        bregmanGap d c (inner ℝ z.1.val w.1.val) (if z.2=w.2 then q1 else q0)) := by
  rw [actual_three_signedKernel_difference d c β q0 q1 v x z w,
    actual_labeled_covariance_difference_of_positive_coefficients d c hc hd hq0 hqq]
  ring

/-- The literal interpolation diagonal is independent of all coefficient
parameters and labels, because each true unit spin has overlap one. -/
theorem actual_three_signedKernel_diagonal {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    (β v : ℝ) {q0 q1 : ℝ} (hq0 : 0 ≤ q0) (hqq : q0 ≤ q1)
    (x : Fin K → ℝ) (z : UnitSphere N × Fin k) :
    GaussianThreeBlockComparison.signedKernel (threeLinear d c β q0 q1 v x) threeLabel z z =
      (N : ℝ)*β^2*(theta d c q0-bregmanGap d c 1 q1) := by
  rw [actual_three_signedKernel d c hc hd β v hq0 hqq x z z,
    real_inner_self_eq_norm_sq,unit_norm,one_pow,ite_eq_left rfl]

end
end SlowEquilibration.SphericalParisiLabeledThreeBlock
