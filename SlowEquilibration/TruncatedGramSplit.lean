-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Tactic

@[expose] public section

/-! An actual vector-valued Huang--Sellke split. Its left side is the true
Bochner feature barycenter. Bounded-feature integrability and the mean-Gram
identity are derived internally; the far-row condition is the literal
integrated-band truncation condition. -/

noncomputable section
namespace SlowEquilibration.TruncatedGramSplit
open MeasureTheory Set Filter
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

/-- Actual scalar-weighted bounded features are Bochner integrable. -/
theorem weighted_feature_integrable (μ : Measure X) (A : X → H)
    (hA : Measurable A) {M : ℝ} (_hM : 0 ≤ M) (hbound : ∀ᵐx ∂μ,‖A x‖ ≤ M)
    (W : X → ℝ) (hW : Integrable W μ) :
    Integrable (fun x => W x • A x) μ := by
  apply ((hW.norm).mul_const M).mono'
    (hW.aestronglyMeasurable.smul hA.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖W x • A x‖ ≤ ‖W x‖*M
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- The true weighted feature mean has the deterministic mass bound. -/
theorem norm_weighted_feature_integral_le (μ : Measure X) (A : X → H)
    (hA : Measurable A) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐx ∂μ,‖A x‖ ≤ M)
    (W : X → ℝ) (hWi : Integrable W μ) (hW0 : ∀ᵐx ∂μ,0 ≤ W x) :
    ‖∫x,W x • A x ∂μ‖ ≤ M*(∫x,W x ∂μ) := by
  have hi := weighted_feature_integrable μ A hA hM hbound W hWi
  calc
    _ ≤ ∫x,‖W x • A x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫x,M*W x ∂μ := by
      apply integral_mono_ae hi.norm (hWi.const_mul M)
      filter_upwards [hbound,hW0] with x hx hw
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw]
      nlinarith [mul_le_mul_of_nonneg_left hx hw]
    _ = _ := integral_const_mul _ _

/-- A literal two-spin Gram split controls the true truncated feature mean. -/
theorem feature_mean_sq_le (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → H) (hA : Measurable A) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐx ∂μ,‖A x‖ ≤ M)
    (W : X → ℝ) (hWm : Measurable W) (hWi : Integrable W μ)
    (hW0 : ∀x,0 ≤ W x) (T : Set X) (hT : MeasurableSet T)
    (S : Set (X×X)) (hS : MeasurableSet S) {L : ℝ} (hL : 0 ≤ L)
    (hfar : ∀ᵐu ∂μ,u∈T →
      (∫v,Sᶜ.indicator (fun p : X×X => W p.2) (u,v) ∂μ) ≤ L) :
    ‖∫x,T.indicator (fun y => W y • A y) x ∂μ‖^2 ≤ 
      (∫p : X×X,S.indicator (fun z => |inner ℝ (A z.1) (A z.2)| * W z.1*W z.2) p ∂μ.prod μ)+
        M^2*L*(∫x,W x ∂μ) := by
  let F : X → H := T.indicator (fun x => W x • A x)
  let f : X → ℝ := T.indicator W
  let K : X×X → ℝ := fun p => inner ℝ (A p.1) (A p.2)
  let B : X×X → ℝ := S.indicator (fun p => |K p| * W p.1*W p.2)
  let V : X×X → ℝ := fun p => f p.1*Sᶜ.indicator (fun z : X×X => W z.2) p
  have hiF : Integrable F μ := (weighted_feature_integrable μ A hA hM hbound W hWi).indicator hT
  have hif : Integrable f μ := hWi.indicator hT
  have hf0 : ∀x,0 ≤ f x := fun x => Set.indicator_nonneg (fun _ _ => hW0 _) x
  have hF (x : X) : F x=f x • A x := by
    by_cases hx : x∈T <;> simp [F,f,hx]
  have hpairBound : ∀ᵐp : X×X ∂μ.prod μ,|K p| ≤ M^2 := by
    have hpair : ∀ᵐp : X×X ∂μ.prod μ,‖A p.1‖ ≤ M ∧ ‖A p.2‖ ≤ M := by
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_le (hA.comp measurable_fst).norm measurable_const).inter
          (measurableSet_le (hA.comp measurable_snd).norm measurable_const))).mpr
      filter_upwards [hbound] with x hx
      filter_upwards [hbound] with y hy
      exact ⟨hx,hy⟩
    filter_upwards [hpair] with p hp
    dsimp [K]
    exact (abs_real_inner_le_norm _ _).trans (by
      have hh := mul_le_mul hp.1 hp.2 (norm_nonneg _) hM
      simpa only [pow_two] using hh)
  have hiWW := hWi.mul_prod hWi
  have hiB : Integrable B (μ.prod μ) := by
    apply (hiWW.const_mul (M^2)).mono'
    · dsimp [B,K]
      have hk : Measurable (fun p : X×X => inner ℝ (A p.1) (A p.2)) :=
        (hA.comp measurable_fst).inner (hA.comp measurable_snd)
      exact ((continuous_abs.measurable.comp hk).mul
        (hWm.comp measurable_fst) |>.mul (hWm.comp measurable_snd)).aestronglyMeasurable.indicator hS
    · filter_upwards [hpairBound] with p hp
      by_cases hps : p∈S
      · simp only [B,Set.indicator_of_mem hps]
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (hW0 p.1)) (hW0 p.2))]
        nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg (hW0 p.1) (hW0 p.2))]
      · simp only [B,Set.indicator_of_notMem hps,norm_zero]
        exact mul_nonneg (sq_nonneg M) (mul_nonneg (hW0 p.1) (hW0 p.2))
  have hiV : Integrable V (μ.prod μ) := by
    have hv : V=(Sᶜ.indicator (fun p : X×X => f p.1*W p.2)) := by
      funext p
      by_cases hp : p∈Sᶜ <;> simp [V,hp]
    rw [hv]
    exact (hif.mul_prod hWi).indicator hS.compl
  have hiK : Integrable (fun p : X×X => inner ℝ (F p.1) (F p.2)) (μ.prod μ) :=
    hiF.op_fst_snd (by fun_prop) ⟨1,by
      intro x y
      simpa only [Real.norm_eq_abs,one_mul] using abs_real_inner_le_norm x y⟩ hiF
  have hnorm : ‖∫x,F x ∂μ‖^2=
      ∫p : X×X,inner ℝ (F p.1) (F p.2) ∂μ.prod μ := by
    symm
    have hh := integral_prod_bilin (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) hiF hiF
    change (∫p : X×X,inner ℝ (F p.1) (F p.2) ∂μ.prod μ)=
      inner ℝ (∫x,F x ∂μ) (∫x,F x ∂μ) at hh
    simpa only [real_inner_self_eq_norm_sq] using hh
  have hB0 : ∀p,0 ≤ B p := fun p => Set.indicator_nonneg
    (fun z _ => mul_nonneg (mul_nonneg (abs_nonneg _) (hW0 z.1)) (hW0 z.2)) p
  have hV0 : ∀p,0 ≤ V p := fun p => mul_nonneg (hf0 _)
    (Set.indicator_nonneg (fun z _ => hW0 z.2) p)
  have hpoint : ∀ᵐp : X×X ∂μ.prod μ,
      inner ℝ (F p.1) (F p.2) ≤ B p+M^2*V p := by
    filter_upwards [hpairBound] with p hp
    rw [hF,hF,real_inner_smul_left,real_inner_smul_right]
    change f p.1*(f p.2*K p) ≤ B p+M^2*V p
    by_cases hpu : p.1∈T
    · by_cases hpv : p.2∈T
      · simp only [f,Set.indicator_of_mem hpu,Set.indicator_of_mem hpv]
        by_cases hps : p∈S
        · simp only [B,V,Set.indicator_of_mem hps,
            Set.indicator_of_notMem (show p∉Sᶜ from notMem_compl_iff.mpr hps),mul_zero,add_zero,f,
            Set.indicator_of_mem hpu]
          nlinarith [mul_le_mul_of_nonneg_right (le_abs_self (K p))
            (mul_nonneg (hW0 p.1) (hW0 p.2))]
        · simp only [B,V,Set.indicator_of_notMem hps,
            Set.indicator_of_mem (show p∈Sᶜ from hps),zero_add,f,Set.indicator_of_mem hpu]
          nlinarith [mul_le_mul_of_nonneg_right ((le_abs_self (K p)).trans hp)
            (mul_nonneg (hW0 p.1) (hW0 p.2))]
      · rw [show f p.2=0 from by simp [f,hpv],zero_mul,mul_zero]
        exact add_nonneg (hB0 p) (mul_nonneg (sq_nonneg M) (hV0 p))
    · rw [show f p.1=0 from by simp [f,hpu],zero_mul]
      exact add_nonneg (hB0 p) (mul_nonneg (sq_nonneg M) (hV0 p))
  have hV : (∫p,V p ∂μ.prod μ) ≤ L*(∫x,W x ∂μ) := by
    rw [integral_prod _ hiV]
    have hrow (u : X) : (∫v,V (u,v) ∂μ)=
        f u*(∫v,Sᶜ.indicator (fun p : X×X => W p.2) (u,v) ∂μ) := by
      change (∫v,f u*Sᶜ.indicator (fun p : X×X => W p.2) (u,v) ∂μ)=_
      exact integral_const_mul _ _
    have hiRow := hiV.integral_prod_left
    simp_rw [hrow] at hiRow ⊢
    calc
      _  ≤  ∫u,L*W u ∂μ := by
        apply integral_mono_ae hiRow (hWi.const_mul L)
        filter_upwards [hfar] with u hu
        by_cases hut : u∈T
        · rw [show f u=W u from by simp [f,hut]]
          nlinarith [mul_le_mul_of_nonneg_left (hu hut) (hW0 u)]
        · rw [show f u=0 from by simp [f,hut],zero_mul]
          exact mul_nonneg hL (hW0 u)
      _ = _ := integral_const_mul _ _
  change ‖∫x,F x ∂μ‖^2 ≤ _
  rw [hnorm]
  have hh := integral_mono_ae hiK (hiB.add (hiV.const_mul (M^2))) hpoint
  dsimp only [Pi.add_apply] at hh
  rw [integral_add hiB (hiV.const_mul _),integral_const_mul] at hh
  simpa only [B,K,mul_assoc] using
    hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hV (sq_nonneg M)))

end SlowEquilibration.TruncatedGramSplit
