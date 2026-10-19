-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacWeight

/-! The actual bounded killing path expectation has the coefficient
generator `L - κ` on the genuine C² core.  The killing term is obtained by
dominated difference quotients along the actual physical paths. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging WeightedDriftSums
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E Ω : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E]
  [SecondCountableTopology E]
  [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem correction_hasDerivWithinAt_zero
    (κ : E → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ‖κ x‖ ≤ K)
    (X : ℝ≥0 → Ω → E) (hXm : Measurable (Function.uncurry X))
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (x : E) (hX0 : X 0 =ᵐ[P] fun _ => x)
    (f : E → ℝ) (hf : Continuous f) (C : ℝ) (_hC0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P, ∀ t, ‖f (X t ω)‖ ≤ C) :
    HasDerivWithinAt
      (fun r : ℝ => ∫ ω, (survival κ X r.toNNReal ω - 1) * f (X r.toNNReal ω) ∂P)
      (-κ x * f x) (Ici 0) 0 := by
  let G (r : ℝ) (ω : Ω) := r⁻¹ * (survival κ X r.toNNReal ω - 1) * f (X r.toNNReal ω)
  have hG (r : ℝ) : AEStronglyMeasurable (G r) P := by
    exact ((((survival_stronglyMeasurable κ hκ.measurable X hXm r.toNNReal).sub
      stronglyMeasurable_const).const_mul r⁻¹).mul
      (hf.comp_stronglyMeasurable (hXm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)).aestronglyMeasurable
  have hb (r : ℝ) (hr : 0 < r) : ∀ᵐ ω ∂P, ‖G r ω‖ ≤ K * C := by
    filter_upwards [hC] with ω hω
    have hw := survival_defect_le κ hκ0 K hK X r.toNNReal ω
    rw [Real.coe_toNNReal r hr.le] at hw
    dsimp only [G]
    rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    calc
      r⁻¹ * ‖survival κ X r.toNNReal ω - 1‖ * ‖f (X r.toNNReal ω)‖
          ≤ r⁻¹ * (K*r) * C := by gcongr; exact hω _
      _ = K*C := by field_simp
  have ht : ∀ᵐ ω ∂P, Tendsto (fun r => G r ω)
      (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 (-κ x * f x)) := by
    filter_upwards [hXc,hX0] with ω hc h0
    have hw := hasDerivWithinAt_iff_tendsto_slope.mp
      ((survival_hasDerivWithinAt_zero κ hκ X ω hc).sub_const 1)
    have hfc : Continuous (fun r : ℝ => f (X r.toNNReal ω)) :=
      hf.comp (hc.comp continuous_real_toNNReal)
    have hfl : Tendsto (fun r : ℝ => f (X r.toNNReal ω))
        (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 (f x)) := by
      simpa only [Real.toNNReal_zero,h0] using
        (hfc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hh := hw.mul hfl
    simpa only [G,slope_def_module,sub_zero,smul_eq_mul,Real.toNNReal_zero,survival_zero,
      sub_self,sub_zero,h0] using hh
  have hI : Tendsto (fun r => ∫ ω, G r ω ∂P)
      (𝓝[Ici (0 : ℝ) \ {0}] 0) (𝓝 (-κ x * f x)) := by
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      tendsto_integral_filter_of_dominated_convergence
        (fun _ => K*C) (.of_forall hG)
        (show ∀ᶠ r in 𝓝[Ici (0 : ℝ) \ {0}] 0,
          ∀ᵐ ω ∂P, ‖G r ω‖ ≤ K*C from by
          filter_upwards [self_mem_nhdsWithin] with r hr
          exact hb r (lt_of_le_of_ne hr.1 (Ne.symm hr.2)))
        (integrable_const _) ht
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  convert hI using 1
  funext r
  simp only [slope_def_module,sub_zero,smul_eq_mul,Real.toNNReal_zero,
    survival_zero,sub_self,zero_mul,integral_zero,sub_zero]
  rw [← integral_const_mul]
  congr 1
  funext ω
  dsimp only [G]
  ring

/-- This bridge assumes only the ordinary physical core derivative; the
additional killing derivative is proved from its literal path integral. -/
theorem killedExpectation_hasDerivWithinAt_zero
    (κ : E → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ‖κ x‖ ≤ K)
    (X : ℝ≥0 → Ω → E) (hXm : Measurable (Function.uncurry X))
    (hXc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (x : E) (hX0 : X 0 =ᵐ[P] fun _ => x)
    (f : E → ℝ) (hf : Continuous f) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ᵐ ω ∂P, ∀ t, ‖f (X t ω)‖ ≤ C) (Lf : ℝ)
    (hd : HasDerivWithinAt (fun r : ℝ => ∫ ω, f (X r.toNNReal ω) ∂P)
      Lf (Ici 0) 0) :
    HasDerivWithinAt (fun r : ℝ => killedExpectation P κ X r.toNNReal f)
      (Lf - κ x * f x) (Ici 0) 0 := by
  have hc := correction_hasDerivWithinAt_zero P κ hκ hκ0 K hK0 hK
    X hXm hXc x hX0 f hf C hC0 hC
  have he (t : ℝ≥0) : killedExpectation P κ X t f =
      (∫ ω, f (X t ω) ∂P) + ∫ ω, (survival κ X t ω-1)*f (X t ω) ∂P := by
    have hfm : StronglyMeasurable (fun ω => f (X t ω)) :=
      hf.comp_stronglyMeasurable (hXm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
    have hfi : Integrable (fun ω => f (X t ω)) P :=
      Integrable.of_bound hfm.aestronglyMeasurable C (hC.mono (fun _ h => h t))
    have hci : Integrable (fun ω => (survival κ X t ω-1)*f (X t ω)) P := by
      apply Integrable.of_bound
        (((survival_stronglyMeasurable κ hκ.measurable X hXm t).sub
          stronglyMeasurable_const).mul hfm).aestronglyMeasurable (K*t*C)
      filter_upwards [hC] with ω hω
      change ‖(survival κ X t ω-1)*f (X t ω)‖ ≤ K*t*C
      rw [norm_mul]
      exact mul_le_mul (survival_defect_le κ hκ0 K hK X t ω) (hω t)
        (norm_nonneg _) (mul_nonneg hK0 t.coe_nonneg)
    rw [← integral_add hfi hci]
    apply integral_congr_ae
    exact .of_forall (fun _ => by ring)
  convert (hd.add hc).congr_of_eventuallyEq (.of_forall (fun r => he r.toNNReal))
    (by simpa only [Pi.add_apply,Real.toNNReal_zero] using he 0) using 1; ring

end SlowEquilibration.ConditionedEntrance.FeynmanKac
