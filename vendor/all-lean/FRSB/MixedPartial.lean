module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

/-! A bounded-derivative FTC proof of mixed partial differentiation.
No mixed differentiability premise is hidden in the result. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FRSB

/-- Differentiate a scalar interval integral in an external spatial parameter.
The derivative is bounded on the integration interval, uniformly in space. -/
theorem hasDerivAt_intervalIntegral_parameter
    (F G : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) (a b x : ℝ) (B : ℝ)
    (hb : ∀ t ∈ uIcc a b, ∀ y, ‖G t y‖ ≤ B)
    (hd : ∀ t ∈ uIcc a b, ∀ y, HasDerivAt (F t) (G t y) y) :
    HasDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, G t x) x := by
  have hsection (y : ℝ) : Continuous (fun t => F t y) := hF.comp (continuous_id.prodMk continuous_const)
  have hgsection : Continuous (fun t => G t x) := hG.comp (continuous_id.prodMk continuous_const)
  let P : Measure ℝ := volume.restrict (uIoc a b)
  have : IsFiniteMeasure P := by
    dsimp [P, uIoc]
    infer_instance
  have hmeas : ∀ᶠ y in nhds x, AEStronglyMeasurable (fun t => F t y) P :=
    .of_forall fun y => (hsection y).aestronglyMeasurable
  have hi : Integrable (fun t => F t x) P :=
    (intervalIntegrable_iff.mp ((hsection x).intervalIntegrable a b))
  have hdm : AEStronglyMeasurable (fun t => G t x) P := hgsection.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂P, ∀ y ∈ (univ : Set ℝ), ‖G t y‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht y _
    exact hb t (uIoc_subset_uIcc ht) y
  have hdiff : ∀ᵐ t ∂P, ∀ y ∈ (univ : Set ℝ), HasDerivAt (F t) (G t y) y := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht y _
    exact hd t (uIoc_subset_uIcc ht) y
  have hbi : Integrable (fun _ : ℝ => B) P := integrable_const B
  have hout := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t => F t y) (F' := fun y t => G t y) (s := univ)
    (by simp) hmeas hi hdm hbound hbi hdiff).2
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul] using
    hout.const_mul (if a ≤ b then (1 : ℝ) else -1)

/-- A continuous bounded derivative of the time derivative suffices to commute
one spatial derivative with a time derivative on an open interval. -/
theorem hasDerivAt_time_spatial_of_FTC
    (u ux ut utx : ℝ → ℝ → ℝ)
    (hut : Continuous (Function.uncurry ut)) (hutx : Continuous (Function.uncurry utx))
    (a b : ℝ) (B : ℝ)
    (htime : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => u s x) (ut t x) t)
    (hspace : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hutspace : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (ut t) (utx t x) x)
    (hbound : ∀ t ∈ Ioo a b, ∀ x, ‖utx t x‖ ≤ B)
    {t x : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ux s x) (utx t x) t := by
  have hlocal : ∀ᶠ r in nhds t, r ∈ Ioo a b := isOpen_Ioo.mem_nhds ht
  have heq : (fun r => ux r x) =ᶠ[nhds t]
      (fun r => ux t x + ∫ s in t..r, utx s x) := by
    filter_upwards [hlocal] with r hr
    have hsub : uIcc t r ⊆ Ioo a b := by
      intro s hs
      rcases mem_uIcc.mp hs with hs | hs
      · exact ⟨ht.1.trans_le hs.1, hs.2.trans_lt hr.2⟩
      · exact ⟨hr.1.trans_le hs.1, hs.2.trans_lt ht.2⟩
    have hFTC (y : ℝ) : u r y = u t y + ∫ s in t..r, ut s y := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => htime s (hsub hs) y)
        ((hut.comp (by fun_prop : Continuous (fun s : ℝ => (s,y)))).intervalIntegrable t r)
      linarith
    have hdint := hasDerivAt_intervalIntegral_parameter ut utx hut hutx t r x B
      (fun s hs y => hbound s (hsub hs) y)
      (fun s hs y => hutspace s (hsub hs) y)
    have hdeq : HasDerivAt (u r) (ux t x + ∫ s in t..r, utx s x) x := by
      have hfun : u r = fun y => u t y + ∫ s in t..r, ut s y := funext hFTC
      rw [hfun]
      exact (hspace t ht x).add hdint
    exact ((hspace r hr x).unique hdeq)
  have hcont : Continuous (fun s => utx s x) := hutx.comp (continuous_id.prodMk continuous_const)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable t t)
    (hcont.stronglyMeasurableAtFilter volume (nhds t)) hcont.continuousAt).const_add (ux t x)
  exact hd.congr_of_eventuallyEq heq

end FRSB
