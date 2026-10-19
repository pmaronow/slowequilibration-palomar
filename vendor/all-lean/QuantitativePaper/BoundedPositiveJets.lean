module
public import QuantitativePaper.VectorSmooth

@[expose] public section

/-! Closure of actual smooth functions with globally bounded positive-order
jets under finite linear combinations. The function itself may have linear
growth, as the physical vector potential does. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundedPositiveJets (f : E → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ j,1 ≤ j → ∃ B : ℝ,0 ≤ B ∧ ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ B

theorem boundedPositiveJets_const (c : ℝ) : BoundedPositiveJets (fun _ : E => c) := by
  refine ⟨contDiff_const,fun j hj => ⟨0,le_rfl,fun x => ?_⟩⟩
  rw [iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,norm_zero]

theorem BoundedPositiveJets.add {f g : E → ℝ} (hf : BoundedPositiveJets f)
    (hg : BoundedPositiveJets g) : BoundedPositiveJets (fun x => f x+g x) := by
  refine ⟨hf.1.add hg.1,?_⟩
  intro j hj
  obtain ⟨B,hB,hfb⟩ := hf.2 j hj
  obtain ⟨C,hC,hgb⟩ := hg.2 j hj
  refine ⟨B+C,add_nonneg hB hC,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ j (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.1.of_le (by simp)).contDiffAt (hg.1.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hfb x) (hgb x))

theorem BoundedPositiveJets.const_mul {f : E → ℝ} (hf : BoundedPositiveJets f)
    (c : ℝ) : BoundedPositiveJets (fun x => c*f x) := by
  refine ⟨contDiff_const.mul hf.1,?_⟩
  intro j hj
  obtain ⟨B,hB,hfb⟩ := hf.2 j hj
  refine ⟨|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ j (fun x => c • f x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.1.of_le (by simp)).contDiffAt,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg _)

theorem BoundedPositiveJets.neg {f : E → ℝ} (hf : BoundedPositiveJets f) :
    BoundedPositiveJets (fun x => -f x) := by simpa using hf.const_mul (-1)

theorem boundedPositiveJets_finite_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S,BoundedPositiveJets (f i)) : BoundedPositiveJets (fun x => ∑ i ∈ S,f i x) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using boundedPositiveJets_const (E := E) 0
  | @insert i S hi ih =>
    have hh := (hf i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh

theorem boundedPositiveJets_linear (l : E →L[ℝ] ℝ) : BoundedPositiveJets (l : E → ℝ) := by
  refine ⟨l.contDiff,fun j hj => ⟨(max 1 ‖l‖)^j,by positivity,fun x => ?_⟩⟩
  exact norm_iteratedFDeriv_linear_le l _ (le_max_left _ _) (le_max_right _ _) hj x

theorem BoundedPositiveJets.fderiv_apply {f : E → ℝ} (hf : BoundedPositiveJets f) (w : E) :
    BoundedPositiveJets (fun x => fderiv ℝ f x w) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.1.fderiv_right (by simp)
  refine ⟨hd.clm_apply contDiff_const,?_⟩
  intro j hj
  obtain ⟨B,hB,hBound⟩ := hf.2 (j+1) (by omega)
  refine ⟨‖w‖*B,mul_nonneg (norm_nonneg _) hB,fun x => ?_⟩
  apply (norm_iteratedFDeriv_clm_apply_const hd.contDiffAt (by simp)).trans
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hBound x) (norm_nonneg _)

theorem BoundedPositiveJets.comp_linear {f : E → ℝ} (hf : BoundedPositiveJets f)
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] (L : A →L[ℝ] E) :
    BoundedPositiveJets (f ∘ L) := by
  refine ⟨hf.1.comp L.contDiff,?_⟩
  intro j hj
  obtain ⟨B,hB,hBound⟩ := hf.2 j hj
  refine ⟨B*‖L‖^j,mul_nonneg hB (pow_nonneg (norm_nonneg _) _),fun x => ?_⟩
  rw [L.iteratedFDeriv_comp_right hf.1 x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hBound (L x)) (pow_nonneg (norm_nonneg _) _)

end QuantitativePaper
