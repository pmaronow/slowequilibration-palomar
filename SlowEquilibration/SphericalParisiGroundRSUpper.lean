-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteTensorMixtureMaximum
public import SlowEquilibration.GaussianNormConcentration

@[expose] public section

/-! Actual spherical ground-energy upper bounds for arbitrary finite
nonnegative ordered-tensor coefficients, including linear and odd degrees.
The sharp constant-profile (alpha=0) Huang--Sellke trial is derived from true
Gaussian increment comparison; it does not supply the still missing general
piecewise-affine one-step trial used in the retained-center filter. -/

namespace SlowEquilibration.SphericalParisiGroundRSUpper

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum GaussianCompactMaximum
open GaussianSharpAbsoluteMaximum
open PureTensorJetFeatures PureTensorJetBounds
open scoped InnerProductSpace BigOperators Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The actual maximum of the original finite iid ordered-tensor field
on the genuine unit-sphere parameterization of the physical sphere. -/
def actualMaximum {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : ℝ :=
  ⨆ x : UnitSphere N, inner ℝ (feature d c x.val) g

theorem actualMaximum_integrable {N : ℕ} (hN : 0 < N) (d : σ → ℕ) (c : σ → ℝ) :
    Integrable (actualMaximum (N := N) d c)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) := by
  let : NeZero N := ⟨hN.ne'⟩
  exact supremum_integrable_of_continuous (fun x : UnitSphere N => innerSL ℝ (feature d c x.val))
    ((innerSL ℝ).continuous.comp ((feature_continuous d c).comp continuous_subtype_val))

/-- A true sharp expected ground upper for every finite mixture with
degrees at least one. No covariance parity or physical-limit hypothesis. -/
theorem actual_expected_maximum_le {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 1 ≤ d i) :
    (∫ g, actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
        (N : ℝ)*Real.sqrt (∑ i, (d i : ℝ)*c i) := by
  let : NeZero N := ⟨hN.ne'⟩
  let s : ℝ := ∑ i, (d i : ℝ)*c i
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hc i)
  have hvar : (∑ i, c i) ≤ s := Finset.sum_le_sum (fun i _ => by
    have hi : (1 : ℝ) ≤ d i := by exact_mod_cast hd i
    nlinarith [hc i])
  have hp := expected_positiveSupremum_le
    (fun x : UnitSphere N => feature d c x.val) (fun x : UnitSphere N => x.val)
    ((feature_continuous d c).comp continuous_subtype_val) continuous_subtype_val
    (L := Real.sqrt (N : ℝ)*Real.sqrt s) (by positivity)
    (fun x => by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [feature_norm_sq d c hc, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt hs]
      exact mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg N))
    unit_norm
    (fun x y => by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt hs]
      exact feature_increment_sq_le d c hc x y)
  have hm := integral_mono (actualMaximum_integrable hN d c)
    (positiveSupremum_integrable (fun x : UnitSphere N => feature d c x.val)
      ((feature_continuous d c).comp continuous_subtype_val)) (fun g => by
        apply ciSup_le
        intro x
        exact le_positiveSupremum _ ((feature_continuous d c).comp continuous_subtype_val) g (.inr x))
  apply (hm.trans hp).trans_eq
  simp only [Fintype.card_fin]
  calc
    _ = (Real.sqrt (N : ℝ))^2*Real.sqrt s := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The literal constant-profile Huang--Sellke value, for every positive L.
This is a genuine physical bound, with its alpha=0 scope explicit. -/
theorem actual_constant_profile_ground_upper {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    {L : ℝ} (hL : 0 < L) :
    (∫ g, actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
        (N : ℝ)*(L*(∑ i, (d i : ℝ)*c i)+1/L)/2 := by
  have hs : 0 ≤ ∑ i, (d i : ℝ)*c i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hc i)
  have hroot := Real.sq_sqrt hs
  have hsq := sq_nonneg (L*Real.sqrt (∑ i, (d i : ℝ)*c i)-1)
  have htrial : Real.sqrt (∑ i, (d i : ℝ)*c i) ≤
      (L*(∑ i, (d i : ℝ)*c i)+1/L)/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have he : (L*(∑ i, (d i : ℝ)*c i)+1/L)*L =
        L^2*(∑ i, (d i : ℝ)*c i)+1 := by field_simp [hL.ne']
    have hw := congrArg (fun a : ℝ => L^2*a) hroot
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith [hw]
  have hh := mul_le_mul_of_nonneg_left htrial (Nat.cast_nonneg N)
  exact (actual_expected_maximum_le hN d c hc hd).trans (by simpa only [mul_div_assoc] using hh)

/-- Actual Gaussian maximum concentration upgrades the sharp constant
profile trial to a finite exponential physical ground-energy upper tail. -/
theorem actual_constant_profile_ground_upper_tail {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (hvar : 0 < ∑ i, c i) {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g | (N : ℝ)*(L*(∑ i, (d i : ℝ)*c i)+1/L)/2+(N : ℝ)*t ≤
        actualMaximum d c g} ≤
          Real.exp (-(N : ℝ)*t^2/(2*∑ i, c i)) := by
  let : NeZero N := ⟨hN.ne'⟩
  let B : ℝ := Real.sqrt ((N : ℝ)*∑ i, c i)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hb (x : UnitSphere N) : ‖innerSL ℝ (feature d c x.val)‖ ≤ B := by
    rw [innerSL_apply_norm]
    apply (sq_le_sq₀ (norm_nonneg _) hB).mp
    rw [feature_norm_sq d c hc, Real.sq_sqrt
      (mul_nonneg (Nat.cast_nonneg N) hvar.le)]
  have hLip : LipschitzWith B.toNNReal (actualMaximum (N := N) d c) :=
    field_supremum_lipschitz (fun x : UnitSphere N => innerSL ℝ (feature d c x.val)) hb
  have hs : 0 ≤ (N : ℝ)*t := mul_nonneg (Nat.cast_nonneg N) ht
  have hp := GaussianNormConcentration.centered_lipschitz_upper_tail
    (actualMaximum (N := N) d c) hB hLip hs
  have hmean := actual_constant_profile_ground_upper hN d c hc hd hL
  have hm : (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g | (N : ℝ)*(L*(∑ i, (d i : ℝ)*c i)+1/L)/2+(N : ℝ)*t ≤
        actualMaximum d c g} ≤
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (∫ y, actualMaximum d c y
            ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+(N : ℝ)*t ≤
          actualMaximum d c g} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro g hg
    have hg' : (N : ℝ)*(L*(∑ i, (d i : ℝ)*c i)+1/L)/2+(N : ℝ)*t ≤
      actualMaximum d c g := hg
    exact (add_le_add hmean (le_refl ((N : ℝ)*t))).trans hg'
  refine (hm.trans hp).trans_eq ?_
  unfold B
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hvar.le)]
  congr 1
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hv : (∑ i, c i) ≠ 0 := hvar.ne'
  field_simp [hn,hv]

open Filter in
/-- The literal source Huang--Sellke probability statement is closed for
the alpha=0 constant-profile subfamily, with linear/odd degrees admitted. -/
theorem actual_constant_profile_ground_probability_tendsto
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (hvar : 0 < ∑ i, c i) {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    Tendsto (fun N : ℕ =>
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(L*(∑ i, (d i : ℝ)*c i)+1/L)/2+(N : ℝ)*t <
          actualMaximum d c g}) atTop (𝓝 (0 : ℝ)) := by
  have hrate : 0 < t^2/(2*∑ i, c i) := div_pos (sq_pos_of_pos ht) (mul_pos (by norm_num) hvar)
  have hlim : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)*t^2/(2*∑ i, c i)))
      atTop (𝓝 (0 : ℝ)) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hrate) using 1
    funext N
    congr 1
    ring
  refine squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hp := actual_constant_profile_ground_upper_tail (N := N) (by omega) d c hc hd hvar hL ht.le
  refine (measureReal_mono (fun g hg => ?_)).trans hp
  have hg' : (N : ℝ)*(L*(∑ i, (d i : ℝ)*c i)+1/L)/2+(N : ℝ)*t <
    actualMaximum d c g := hg
  exact hg'.le

end
end SlowEquilibration.SphericalParisiGroundRSUpper
