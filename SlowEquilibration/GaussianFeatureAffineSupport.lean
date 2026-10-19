-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.TruncatedGramSplit

@[expose] public section

/-! Genuine affine lower supports of the actual exponential partition. The
spin truncation is fixed at the reference disorder, so no derivative of an
indicator is used. The proof integrates the elementary exponential tangent
inequality, which is Jensen's inequality in unnormalized form. -/

noncomputable section
namespace SlowEquilibration.GaussianFeatureAffineSupport
open MeasureTheory Set Filter
open scoped RealInnerProductSpace
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

theorem bounded_feature_exp_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → H) (hA : Measurable A) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ᵐx ∂μ,‖A x‖ ≤ M) (g : H) :
    Integrable (fun x => Real.exp (inner ℝ g (A x))) μ := by
  apply (integrable_const (Real.exp (‖g‖*M))).mono'
    ((hA.const_inner (c:=g)).exp.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg g))

/-- Actual finite-measure feature partition lower support from any Borel spin
truncation whose reference partition is positive. -/
theorem log_partition_lower_support (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → H) (hA : Measurable A) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐx ∂μ,‖A x‖ ≤ M) (T : Set X) (hT : MeasurableSet T)
    (g h : H)
    (hz : 0<(∫x,T.indicator (fun y => Real.exp (inner ℝ g (A y))) x ∂μ)) :
    Real.log (∫x,T.indicator (fun y => Real.exp (inner ℝ g (A y))) x ∂μ)+
      inner ℝ (h-g) (∫x,T.indicator (fun y => Real.exp (inner ℝ g (A y)) • A y) x ∂μ)/
        (∫x,T.indicator (fun y => Real.exp (inner ℝ g (A y))) x ∂μ) ≤
      Real.log (∫x,Real.exp (inner ℝ h (A x)) ∂μ) := by
  let W := fun x => Real.exp (inner ℝ g (A x))
  let f := T.indicator W
  let z := ∫x,f x ∂μ
  let V : X → H := fun x => f x • A x
  let v := ∫x,V x ∂μ
  let b := fun x => inner ℝ (h-g) (A x)
  let m := inner ℝ (h-g) v/z
  have hW : Integrable W μ := bounded_feature_exp_integrable μ A hA hM hbound g
  have hf : Integrable f μ := hW.indicator hT
  have hf0 : ∀x,0 ≤ f x := fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hV : Integrable V μ := TruncatedGramSplit.weighted_feature_integrable μ A hA hM hbound f hf
  have hB : Integrable (fun x => f x*b x) μ := by
    convert (innerSL ℝ (h-g)).integrable_comp hV using 1
    funext x
    simp only [V,b,innerSL_apply_apply,real_inner_smul_right]
  have hBmean : (∫x,f x*b x ∂μ)=inner ℝ (h-g) v := by
    have hh := (innerSL ℝ (h-g)).integral_comp_comm hV
    change (∫x,inner ℝ (h-g) (V x) ∂μ)=inner ℝ (h-g) v at hh
    simpa only [V,b,real_inner_smul_right] using hh
  have hvEq : v=∫x,T.indicator (fun y => W y • A y) x ∂μ := by
    apply integral_congr_ae
    exact .of_forall fun x => by by_cases hx : x∈T <;> simp [V,f,hx]
  have hz0 : 0<z := hz
  have hWh : Integrable (fun x => Real.exp (inner ℝ h (A x))) μ :=
    bounded_feature_exp_integrable μ A hA hM hbound h
  let U := fun x => Real.exp m*(f x+f x*b x-m*f x)
  have hU : Integrable U μ := ((hf.add hB).sub (hf.const_mul m)).const_mul (Real.exp m)
  have hUmean : (∫x,U x ∂μ)=z*Real.exp m := by
    rw [integral_const_mul,
      integral_sub (f:=fun x => f x+f x*b x) (g:=fun x => m*f x)
        (hf.add hB) (hf.const_mul m),
      integral_add (f:=f) (g:=fun x => f x*b x) hf hB,integral_const_mul,hBmean]
    have hmz : m*z=inner ℝ (h-g) v := by dsimp [m]; exact div_mul_cancel₀ _ hz0.ne'
    change Real.exp m*(z+inner ℝ (h-g) v-m*z)=z*Real.exp m
    rw [hmz]
    ring
  have hle : z*Real.exp m ≤ ∫x,Real.exp (inner ℝ h (A x)) ∂μ := by
    rw [← hUmean]
    apply integral_mono hU hWh
    intro x
    change U x ≤ Real.exp (inner ℝ h (A x))
    by_cases hx : x∈T
    · have htan := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b x-m)) (Real.exp_pos m).le
      rw [← Real.exp_add,show m+(b x-m)=b x by ring] at htan
      have hh := mul_le_mul_of_nonneg_left htan (Real.exp_pos (inner ℝ g (A x))).le
      have hexp : W x*Real.exp (b x)=Real.exp (inner ℝ h (A x)) := by
        dsimp only [W]
        rw [← Real.exp_add]
        congr 1
        dsimp [b]
        rw [inner_sub_left]
        ring
      rw [← hexp]
      dsimp [U]
      rw [show f x=W x from by simp [f,hx]]
      convert hh using 1
      dsimp [W]
      ring
    · simp only [U,f,Set.indicator_of_notMem hx,zero_add,zero_mul,mul_zero,sub_zero]
      exact (Real.exp_pos _).le
  have hlog := Real.log_le_log (mul_pos hz0 (Real.exp_pos m)) hle
  rw [Real.log_mul hz0.ne' (Real.exp_ne_zero m),Real.log_exp] at hlog
  change Real.log z+inner ℝ (h-g) (∫x,T.indicator (fun y => W y • A y) x ∂μ)/z ≤ _
  rw [← hvEq]
  exact hlog

end SlowEquilibration.GaussianFeatureAffineSupport
