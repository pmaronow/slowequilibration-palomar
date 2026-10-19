-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSharpAbsoluteMaximum

/-! Actual aggregate ordered-tensor features retain the square root of the sum
of degree-weighted variances in the sharp supremum bound. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.FiniteTensorMixtureMaximum
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators
open SphericalAging.FiniteModel PureTensorJetFeatures PureTensorJetBounds
open GaussianSharpAbsoluteMaximum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev Coordinate (N : ℕ) (d : σ → ℕ) := (i : σ) × TensorIndex N (d i)

def feature {N : ℕ} (d : σ → ℕ) (c : σ → ℝ) (x : Vector N) :
    EuclideanSpace ℝ (Coordinate N d) :=
  WithLp.toLp 2 (fun I => Real.sqrt N * Real.sqrt (c I.1) *
    tensorFeature (fun _ : Fin (d I.1) => x) I.2)

theorem feature_continuous {N : ℕ} (d : σ → ℕ) (c : σ → ℝ) :
    Continuous (feature (N := N) d c) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro I
  change Continuous (fun x : Vector N => Real.sqrt N * Real.sqrt (c I.1) *
    ∏ k : Fin (d I.1), x (I.2 k))
  fun_prop

@[simp] theorem feature_apply {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (x : Vector N) (I : Coordinate N d) : feature d c x I =
      Real.sqrt N * Real.sqrt (c I.1) * tensorFeature (fun _ : Fin (d I.1) => x) I.2 := rfl

theorem feature_inner {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0≤c i) (x y : Vector N) :
    inner ℝ (feature d c x) (feature d c y) =
      (N:ℝ)*∑ i,(c i)*(inner ℝ x y)^(d i) := by
  simp only [PiLp.inner_apply,Fintype.sum_sigma,feature_apply,
    RCLike.inner_apply,conj_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh := tensorFeature_inner (fun _ : Fin (d i) => x) (fun _ : Fin (d i) => y)
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin] at hh
  calc
    _ = (Real.sqrt N)^2*(Real.sqrt (c i))^2 *
      ∑ I : TensorIndex N (d i),tensorFeature (fun _ : Fin (d i) => y) I*
        tensorFeature (fun _ : Fin (d i) => x) I := by rw [Finset.mul_sum];congr 1;ext I;ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt (hc i),hh];ring

theorem feature_norm_sq {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0≤c i) (x : UnitSphere N) :
    ‖feature d c x.val‖^2=(N:ℝ)*∑ i,c i := by
  rw [← real_inner_self_eq_norm_sq,feature_inner d c hc]
  simp [real_inner_self_eq_norm_sq,unit_norm x]

theorem feature_increment_sq_le {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0≤c i) (x y : UnitSphere N) :
    ‖feature d c x.val-feature d c y.val‖^2 ≤
      ((N:ℝ)*∑ i,(d i:ℝ)*c i)*‖x.val-y.val‖^2 := by
  have hi (i : σ) : 1+1-2*(inner ℝ x.val y.val)^(d i) ≤
      (d i:ℝ)*‖x.val-y.val‖^2 := by
    have h := tensorFeature_increment_sq_le
      (fun _ : Fin (d i) => x.val) (fun _ : Fin (d i) => y.val)
      (fun _ => unit_norm x) (fun _ => unit_norm y)
    rw [norm_sub_sq_real,tensorFeature_norm_sq_of_unit _ (fun _ => unit_norm x),
      tensorFeature_norm_sq_of_unit _ (fun _ => unit_norm y),tensorFeature_inner] at h
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.sum_const,nsmul_eq_mul] at h
    linarith
  rw [norm_sub_sq_real,feature_norm_sq d c hc x,feature_norm_sq d c hc y,feature_inner d c hc]
  have hh : ∑ i,c i*(1+1-2*(inner ℝ x.val y.val)^(d i)) ≤
      ∑ i,c i*((d i:ℝ)*‖x.val-y.val‖^2) := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hc i))
  have hsum : (∑ i,c i*(1+1-2*(inner ℝ x.val y.val)^(d i))) =
      2*(∑ i,c i)-2*∑ i,c i*(inner ℝ x.val y.val)^(d i) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum2 : (∑ i,c i*((d i:ℝ)*‖x.val-y.val‖^2)) =
      (∑ i,(d i:ℝ)*c i)*‖x.val-y.val‖^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum,hsum2] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N : (0:ℝ)≤N)]

/-- Sharp finite aggregate bound, on its actual standard tensor coordinates. -/
theorem expected_absoluteSupremum_le {N : ℕ} (hN : 0<N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0≤c i) (hd : ∀ i,1≤d i) :
    (∫ g, absoluteSupremum (fun x : UnitSphere N => feature d c x.val) g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
      2*N*Real.sqrt (∑ i,(d i:ℝ)*c i) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let s : ℝ := ∑ i,(d i:ℝ)*c i
  have hs : 0≤s := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hc i)
  have hvar : (∑ i,c i)≤s := Finset.sum_le_sum (fun i _ => by
    have hdi : (1:ℝ)≤d i := by exact_mod_cast hd i
    nlinarith [hc i])
  have h := expected_absoluteSupremum_le_twice
    (fun x : UnitSphere N => feature d c x.val) (fun x : UnitSphere N => x.val)
    ((feature_continuous d c).comp continuous_subtype_val) continuous_subtype_val
    (L := Real.sqrt N*Real.sqrt s) (by positivity)
    (fun x => by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [feature_norm_sq d c hc,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hs]
      exact mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg N))
    unit_norm
    (fun x y => by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hs]
      exact feature_increment_sq_le d c hc x y)
  simp only [Fintype.card_fin] at h
  convert h using 1
  change 2*N*Real.sqrt s=2*(Real.sqrt N*Real.sqrt s)*Real.sqrt N
  calc
    _ = 2*(Real.sqrt N)^2*Real.sqrt s := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    _ = _ := by ring

end SlowEquilibration.FiniteTensorMixtureMaximum
