module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

/-! Higher differentiability of a genuine parameter integral from locally
integrable bounds on its actual iterated derivatives. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxSynthPendingDepth 64

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} [MeasurableSpace α]

theorem integrable_clm_of_norm_bound {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure α) (v : α → E →L[ℝ] G) (B : α → ℝ)
    (hB : Integrable B μ) (hv : AEStronglyMeasurable v μ) (hb : ∀ z,‖v z‖ ≤ B z) :
    Integrable v μ := hB.mono' hv (Eventually.of_forall hb)

theorem iteratedFDeriv_fderiv_eq_curry {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fderiv ℝ f) x =
      continuousMultilinearCurryRightEquiv' ℝ j E F (iteratedFDeriv ℝ (j+1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

theorem contDiff_integral_of_dominated_derivatives {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (N : ℕ) (μ : Measure α) (f : E → α → F)
    (hf : ∀ z,ContDiff ℝ N (fun x => f x z))
    (hmeas : ∀ j, j ≤ N → ∀ x,AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => f y z) x) μ)
    (hbound : ∀ x,∃ s ∈ 𝓝 x,∃ B : ℕ → α → ℝ,
      (∀ j,j ≤ N → Integrable (B j) μ) ∧
      ∀ j,j ≤ N → ∀ y ∈ s,∀ z,‖iteratedFDeriv ℝ j (fun u => f u z) y‖ ≤ B j z) :
    ContDiff ℝ N (fun x => ∫ z,f x z ∂μ) := by
  induction N generalizing F with
  | zero =>
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨s,hs,B,hBi,hB⟩ := hbound x
    have hm (y : E) : AEStronglyMeasurable (f y) μ := by
      have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
        (hmeas 0 (le_refl _) y)
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply] using hh
    exact continuousAt_of_dominated (Eventually.of_forall hm)
      (Filter.Eventually.mono hs fun y hy => Eventually.of_forall fun z => by
        simpa only [norm_iteratedFDeriv_zero] using hB 0 (le_refl _) y hy z)
      (hBi 0 (le_refl _)) (Eventually.of_forall fun z => (hf z).continuous.continuousAt)
  | succ N ih =>
    let g : E → α → E →L[ℝ] F := fun x z => fderiv ℝ (fun y => f y z) x
    have hg (z : α) : ContDiff ℝ N (fun x => g x z) :=
      (hf z).fderiv_right (by norm_cast)
    have hgm (j : ℕ) (hj : j ≤ N) (x : E) : AEStronglyMeasurable
        (fun z => iteratedFDeriv ℝ j (fun y => g y z) x) μ := by
      have hh := (continuousMultilinearCurryRightEquiv' ℝ j E F).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) (by omega) x)
      simpa only [g,iteratedFDeriv_fderiv_eq_curry] using hh
    have hgb (x : E) : ∃ s ∈ 𝓝 x,∃ B : ℕ → α → ℝ,
        (∀ j,j ≤ N → Integrable (B j) μ) ∧
        ∀ j,j ≤ N → ∀ y ∈ s,∀ z,‖iteratedFDeriv ℝ j (fun u => g u z) y‖ ≤ B j z := by
      obtain ⟨s,hs,B,hBi,hB⟩ := hbound x
      refine ⟨s,hs,fun j => B (j+1),fun j hj => hBi _ (by omega),?_⟩
      intro j hj y hy z
      simpa only [g,norm_iteratedFDeriv_fderiv] using hB (j+1) (by omega) y hy z
    refine contDiff_succ_iff_hasFDerivAt.mpr ⟨fun x => ∫ z,g x z ∂μ,
      ih g hg hgm hgb,?_⟩
    intro x
    obtain ⟨s,hs,B,hBi,hB⟩ := hbound x
    have hm (y : E) : AEStronglyMeasurable (f y) μ := by
      have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
        (hmeas 0 (by omega) y)
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply] using hh
    have hi : Integrable (f x) μ := (hBi 0 (by omega)).mono' (hm x)
      (Eventually.of_forall fun z => by
        simpa only [norm_iteratedFDeriv_zero] using hB 0 (by omega) x (mem_of_mem_nhds hs) z)
    have hgm0 : AEStronglyMeasurable (g x) μ := by
      have hh := (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).continuous.comp_aestronglyMeasurable
        (hgm 0 (Nat.zero_le _) x)
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply] using hh
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Eventually.of_forall hm) hi hgm0
      (bound := B 1)
    · exact Eventually.of_forall fun z y hy => by
        simpa only [g,norm_iteratedFDeriv_one] using hB 1 (by omega) y hy z
    · exact hBi 1 (by omega)
    · exact Eventually.of_forall fun z y hy => ((hf z).differentiable (by norm_num)) y |>.hasFDerivAt

set_option backward.isDefEq.respectTransparency false in
theorem iteratedFDeriv_integral_of_dominated_derivatives {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (N : ℕ) (μ : Measure α) (f : E → α → F)
    (hf : ∀ z,ContDiff ℝ N (fun x => f x z))
    (hmeas : ∀ j, j ≤ N → ∀ x,AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => f y z) x) μ)
    (hbound : ∀ x,∃ s ∈ 𝓝 x,∃ B : ℕ → α → ℝ,
      (∀ j,j ≤ N → Integrable (B j) μ) ∧
      ∀ j,j ≤ N → ∀ y ∈ s,∀ z,‖iteratedFDeriv ℝ j (fun u => f u z) y‖ ≤ B j z)
    (j : ℕ) (hj : j ≤ N) (x : E) :
    iteratedFDeriv ℝ j (fun y => ∫ z,f y z ∂μ) x =
      ∫ z,iteratedFDeriv ℝ j (fun y => f y z) x ∂μ := by
  induction j generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih =>
    let F₀ := fun y z => iteratedFDeriv ℝ j (fun u => f u z) y
    let F₁ := fun y z => fderiv ℝ (fun u => F₀ u z) y
    have he : iteratedFDeriv ℝ j (fun y => ∫ z,f y z ∂μ) = fun y => ∫ z,F₀ y z ∂μ :=
      funext fun y => ih (by omega) y
    obtain ⟨s,hs,B,hBi,hB⟩ := hbound x
    have hF₀ (y : E) : AEStronglyMeasurable (F₀ y) μ := hmeas j (by omega) y
    have hF₁ : AEStronglyMeasurable (F₁ x) μ := by
      have hh := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) F).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) hj x)
      simpa only [F₀,F₁,fderiv_iteratedFDeriv,Function.comp_apply] using hh
    have hi : Integrable (F₀ x) μ := (hBi j (by omega)).mono' (hF₀ x)
      (Eventually.of_forall fun z => hB j (by omega) x (mem_of_mem_nhds hs) z)
    have hd : HasFDerivAt (fun y => ∫ z,F₀ y z ∂μ) (∫ z,F₁ x z ∂μ) x :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Eventually.of_forall hF₀) hi hF₁
        (bound := B (j+1))
        (Eventually.of_forall fun z y hy => by
          simpa only [F₀,F₁,norm_fderiv_iteratedFDeriv] using hB (j+1) hj y hy z)
        (hBi (j+1) hj)
        (Eventually.of_forall fun z y hy =>
          ((hf z).differentiable_iteratedFDeriv (by norm_cast) y).hasFDerivAt)
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,he,hd.fderiv]
    have hi₁ := integrable_clm_of_norm_bound μ (F₁ x) (B (j+1)) (hBi (j+1) hj) hF₁
      (fun z => by
        simpa only [F₀,F₁,norm_fderiv_iteratedFDeriv]
          using hB (j+1) hj x (mem_of_mem_nhds hs) z)
    have hij : Integrable (fun z => iteratedFDeriv ℝ (j+1) (fun y => f y z) x) μ :=
      (hBi (j+1) hj).mono' (hmeas (j+1) hj x)
        (Eventually.of_forall fun z => hB (j+1) hj x (mem_of_mem_nhds hs) z)
    ext v
    change (∫ z,F₁ x z ∂μ) (v 0) (Fin.tail v) = _
    rw [ContinuousLinearMap.integral_apply hi₁,ContinuousMultilinearMap.integral_apply hij]
    rw [ContinuousMultilinearMap.integral_apply (hi₁.apply_continuousLinearMap (v 0))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [F₀,F₁,iteratedFDeriv_succ_apply_left]

end QuantitativePaper
