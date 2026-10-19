-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiSphereNetReference
public import SlowEquilibration.SphericalParisiOneStepDualPressureLimit

/-! Physical Gaussian ground-energy transfer from the genuine finite
one-step pressure upper through internally constructed sphere nets. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory ProbabilityTheory Set Filter
open SphericalAging.FiniteModel PureTensorJetBounds FiniteTensorMixtureMaximum
open SphericalParisiGroundRSUpper SphericalParisiLabeledOriginalEndpoint
open SphericalParisiLabeledCovariance SphericalParisiOneStepDualScalar
open SphericalParisiOneStepDualPressureLimit
open GaussianCompactMaximum
open scoped InnerProductSpace BigOperators Topology
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The literal Gaussian spherical maximum satisfies every positive-mass
one-step dual trial asymptotically. Nets, entropy, derivative bounds, true
Gaussian pressures and the scalar REM cancellation are proved internally. -/
theorem eventual_actual_ground_oneStepDual_upper (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    {α κ q : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (∫ g,actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
        oneStepDual d c α q κ+δ := by
  let C := derivativeConstant d c
  have hC : 0 ≤ C := derivativeConstant_nonneg d c
  let ε := δ/(3*(C+1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hApprox : C*ε ≤ δ/3 := by
    have H : 3*(C+1)*ε=δ := by unfold ε;field_simp
    nlinarith
  let L := Real.log (1+2/ε)
  let β := max α (3*L/δ)+1
  have hαβ : α ≤ β := by have := le_max_left α (3*L/δ);unfold β;linarith
  have hβ : 0 < β := hα.trans_le hαβ
  have hEntropy : L/β ≤ δ/3 := by
    have H := (div_le_iff₀ hδ).mp (le_max_right α (3*L/δ))
    apply (div_le_iff₀ hβ).mpr
    unfold β
    nlinarith
  obtain ⟨μ,hμ,hGround⟩ := exists_actual_netReference_family d c hd hε hβ
  have hPressure := eventual_spin_pressure_oneStepDual_upper d c hc hd μ hμ
    hα hαβ hq hq1 hmargin (δ/3) (by positivity)
  filter_upwards [hPressure,eventually_gt_atTop (0 : ℕ)] with N hP hN
  have hG := hGround N hN
  change (∫ g,actualMaximum (N := N) d c g
    ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))/(N : ℝ) ≤
    originalSpinPressure (μ N) d c β/(β*(N : ℝ))+L/β+C*ε at hG
  linarith

/-- The genuine finite Gaussian concentration bound gives a vanishing
upper probability above each positive-mass one-step dual trial. -/
theorem actual_ground_oneStepDual_probability_tendsto (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i) (hvar : 0 < ∑ i,c i)
    {α κ q δ : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q)) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g})
      atTop (𝓝 (0 : ℝ)) := by
  have hmean := eventual_actual_ground_oneStepDual_upper d c hc hd hα hq hq1 hmargin
    (δ := δ/2) (by positivity)
  have hrate : 0 < (δ/2)^2/(2*∑ i,c i) := by positivity
  have hlim : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)*(δ/2)^2/(2*∑ i,c i)))
      atTop (𝓝 (0 : ℝ)) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hrate) using 1
    funext N
    congr 1
    ring
  refine squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  filter_upwards [hmean,eventually_gt_atTop (0 : ℕ)] with N hM hN
  let : NeZero N := ⟨hN.ne'⟩
  let B := Real.sqrt ((N : ℝ)*∑ i,c i)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hb (x : UnitSphere N) : ‖innerSL ℝ (feature d c x.val)‖ ≤ B := by
    rw [innerSL_apply_norm]
    apply (sq_le_sq₀ (norm_nonneg _) hB).mp
    rw [feature_norm_sq d c hc,Real.sq_sqrt (mul_nonneg hNr.le hvar.le)]
  have hLip : LipschitzWith B.toNNReal (actualMaximum (N := N) d c) :=
    field_supremum_lipschitz (fun x : UnitSphere N => innerSL ℝ (feature d c x.val)) hb
  have hp := GaussianNormConcentration.centered_lipschitz_upper_tail
    (actualMaximum (N := N) d c) hB hLip (mul_nonneg hNr.le (by positivity : 0 ≤ δ/2))
  have hMean : (∫ g,actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
      (N : ℝ)*(oneStepDual d c α q κ+δ/2) := by
    exact (div_le_iff₀ hNr).mp hM |>.trans_eq (by ring)
  have hm : (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g | (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g} ≤
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (∫ y,actualMaximum (N := N) d c y
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+(N : ℝ)*(δ/2) ≤
          actualMaximum d c g} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro g hg
    have hg' : (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g := hg
    change (∫ y,actualMaximum (N := N) d c y
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+(N : ℝ)*(δ/2) ≤
      actualMaximum d c g
    nlinarith
  refine (hm.trans hp).trans_eq ?_
  unfold B
  rw [Real.sq_sqrt (mul_nonneg hNr.le hvar.le)]
  congr 1
  field_simp [hNr.ne',hvar.ne']

omit [DecidableEq σ] in
theorem actualMaximum_eq_zero_of_coefficients_zero {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc0 : ∀ i,c i=0)
    (g : EuclideanSpace ℝ (Coordinate N d)) : actualMaximum d c g=0 := by
  let : NeZero N := ⟨hN.ne'⟩
  have hf (x : UnitSphere N) : feature d c x.val=0 := by
    ext I
    simp only [feature_apply,hc0,Real.sqrt_zero,mul_zero,zero_mul,PiLp.zero_apply]
  simp only [actualMaximum,hf,inner_zero_left,ciSup_const]

/-- The actual upper probability statement includes the degenerate zero
mixture, whose field is proved identically zero from the coefficient data. -/
theorem actual_ground_oneStepDual_probability_tendsto_all_variances
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    {α κ q δ : ℝ} (hα : 0 < α) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ-α*(xi1 d c 1-xi1 d c q)) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g})
      atTop (𝓝 (0 : ℝ)) := by
  by_cases hvar : 0 < ∑ i,c i
  · exact actual_ground_oneStepDual_probability_tendsto d c hc hd hvar hα hq hq1 hmargin hδ
  have hs : (∑ i,c i)=0 := le_antisymm (not_lt.mp hvar) (Finset.sum_nonneg (fun i _ => hc i))
  have hc0 (i : σ) : c i=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hc j)).mp hs i (Finset.mem_univ i)
  have hx (r : ℝ) : xi d c r=0 := by simp only [xi,hc0,zero_mul,Finset.sum_const_zero]
  have hx1 (r : ℝ) : xi1 d c r=0 := by simp only [xi1,hc0,zero_mul,Finset.sum_const_zero]
  have hκ : 0 < κ := by simpa only [hx1,sub_self,mul_zero,sub_zero] using hmargin
  have hD : oneStepDual d c α q κ=κ/2 := by
    simp only [oneStepDual,theta,hx,hx1,mul_zero,sub_zero,sub_self,div_self hκ.ne',
      Real.log_one,zero_div,add_zero]
  have hEvent : ∀ᶠ N : ℕ in atTop,
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
        {g | (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g}=0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hset : {g : EuclideanSpace ℝ (Coordinate N d) |
        (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hg' : (N : ℝ)*(oneStepDual d c α q κ+δ) < actualMaximum d c g := hg
      rw [hD,actualMaximum_eq_zero_of_coefficients_zero hN d c hc0] at hg'
      exact (not_lt_of_ge (by positivity)) hg'
    rw [hset]
    simp only [measureReal_empty]
  exact tendsto_const_nhds.congr' (hEvent.mono (fun _ h => h.symm))

end SlowEquilibration.SphericalParisiSphereNet
