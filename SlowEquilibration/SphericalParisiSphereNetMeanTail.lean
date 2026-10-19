-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiSphereNetGround

/-! Generic genuine Gaussian mean-to-upper-tail transfer for the actual
ordered-tensor sphere maximum, including constant, linear and odd blocks.
This reduction keeps its input mean estimate explicit; physical consumers
derive that estimate from their literal trial before invoking the reduction. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory ProbabilityTheory Set Filter
open SphericalAging.FiniteModel PureTensorJetBounds FiniteTensorMixtureMaximum
open SphericalParisiGroundRSUpper GaussianCompactMaximum
open scoped InnerProductSpace BigOperators Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Literal Gaussian-coordinate Lipschitz constant of the actual maximum.
No degree restriction, ground upper or concentration conclusion is input. -/
theorem actualMaximum_lipschitz_all_degrees {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) :
    LipschitzWith (Real.sqrt ((N : ℝ)*∑ i,c i)).toNNReal (actualMaximum (N := N) d c) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hv : 0 ≤ ∑ i,c i := Finset.sum_nonneg fun i _ => hc i
  have hb (x : UnitSphere N) :
      ‖innerSL ℝ (feature d c x.val)‖ ≤ Real.sqrt ((N : ℝ)*∑ i,c i) := by
    rw [innerSL_apply_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [feature_norm_sq d c hc,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hv)]
  exact field_supremum_lipschitz (fun x : UnitSphere N => innerSL ℝ (feature d c x.val)) hb

/-- Genuine finite normalized Gaussian concentration about the actual
mean, with the literal full variance including any random constant block. -/
theorem actualMaximum_centered_upper_tail_all_degrees {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g | (∫ y,actualMaximum (N := N) d c y
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+(N : ℝ)*t ≤
        actualMaximum d c g} ≤ Real.exp (-(N : ℝ)*t^2/(2*∑ i,c i)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hv : 0 ≤ ∑ i,c i := Finset.sum_nonneg fun i _ => hc i
  by_cases hz : (∑ i,c i)=0
  · simp only [hz,mul_zero,div_zero,Real.exp_zero]
    exact measureReal_le_one
  have HP := GaussianNormConcentration.centered_lipschitz_upper_tail
    (actualMaximum (N := N) d c) (Real.sqrt_nonneg ((N : ℝ)*∑ i,c i))
    (actualMaximum_lipschitz_all_degrees hN d c hc) (mul_nonneg hNr.le ht)
  apply HP.trans_eq
  rw [Real.sq_sqrt (mul_nonneg hNr.le hv)]
  congr 1
  field_simp [hNr.ne',hz]

/-- Generic finite reduction from an explicitly supplied actual mean
upper to the true Gaussian upper probability. Its degree scope is unrestricted. -/
theorem actual_ground_mean_upper_tail_all_degrees {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) {R t : ℝ}
    (hmean : (∫ g,actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤ R)
    (ht : 0 ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g | (N : ℝ)*R+(N : ℝ)*t ≤ actualMaximum d c g} ≤
        Real.exp (-(N : ℝ)*t^2/(2*∑ i,c i)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm : (∫ g,actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤ (N : ℝ)*R :=
    (div_le_iff₀ hNr).mp hmean |>.trans_eq (by ring)
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (actualMaximum_centered_upper_tail_all_degrees hN d c hc ht)
  intro g hg
  change (∫ y,actualMaximum (N := N) d c y
    ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+(N : ℝ)*t ≤
    actualMaximum d c g
  change (N : ℝ)*R+(N : ℝ)*t ≤ actualMaximum d c g at hg
  linarith

/-- Generic thermodynamic mean-to-probability reduction for the actual
Gaussian maximum. The physical mean estimate is an explicit input; the
Gaussian concentration, full variance, and zero-field case are derived here. -/
theorem actual_ground_mean_upper_probability_tendsto (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) {R : ℝ} (hR : 0 ≤ R)
    (hmean : ∀ ε : ℝ,0 < ε → ∀ᶠ N : ℕ in atTop,
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤ R+ε)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(R+δ) < actualMaximum d c g}) atTop (𝓝 (0 : ℝ)) := by
  by_cases hvar : 0 < ∑ i,c i
  · have hrate : 0 < (δ/2)^2/(2*∑ i,c i) := by positivity
    have hlim : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)*(δ/2)^2/(2*∑ i,c i)))
        atTop (𝓝 (0 : ℝ)) := by
      convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hrate) using 1
      funext N
      congr 1
      ring
    refine squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
    filter_upwards [hmean (δ/2) (by positivity),eventually_gt_atTop (0 : ℕ)] with N hM hN
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
      (actual_ground_mean_upper_tail_all_degrees hN d c hc hM
        (t := δ/2) (by positivity))
    intro g hg
    change (N : ℝ)*(R+δ/2)+(N : ℝ)*(δ/2) ≤ actualMaximum d c g
    change (N : ℝ)*(R+δ) < actualMaximum d c g at hg
    nlinarith
  have hs : (∑ i,c i)=0 := le_antisymm (not_lt.mp hvar) (Finset.sum_nonneg (fun i _ => hc i))
  have hc0 (i : σ) : c i=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hc j)).mp hs i (Finset.mem_univ i)
  have hEvent : ∀ᶠ N : ℕ in atTop,
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(R+δ) < actualMaximum d c g}=0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hset : {g : EuclideanSpace ℝ (Coordinate N d) |
        (N : ℝ)*(R+δ) < actualMaximum d c g}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hg' : (N : ℝ)*(R+δ) < actualMaximum d c g := hg
      rw [actualMaximum_eq_zero_of_coefficients_zero hN d c hc0] at hg'
      exact (not_lt_of_ge (by positivity)) hg'
    rw [hset]
    simp only [measureReal_empty]
  exact tendsto_const_nhds.congr' (hEvent.mono (fun _ h => h.symm))

end SlowEquilibration.SphericalParisiSphereNet
