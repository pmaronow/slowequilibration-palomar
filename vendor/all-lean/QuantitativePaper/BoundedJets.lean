module
public import QuantitativePaper.BoundedPositiveJets

@[expose] public section

/-! Closure of uniformly bounded smooth observables and all their actual jets. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundedJets (f : E → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ j,∃ B : ℝ,0 ≤ B ∧ ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ B

theorem BoundedPositiveJets.boundedJets {f : E → ℝ} (hf : BoundedPositiveJets f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x,‖f x‖ ≤ B) : BoundedJets f := by
  refine ⟨hf.1,fun j => ?_⟩
  by_cases hj : j=0
  · subst j
    refine ⟨B,hB,fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_zero] using hb x
  · exact hf.2 j (by omega)

theorem BoundedJets.positive {f : E → ℝ} (hf : BoundedJets f) : BoundedPositiveJets f :=
  ⟨hf.1,fun j _ => hf.2 j⟩

theorem BoundedPositiveJets.boundedJets_fderiv_apply {f : E → ℝ}
    (hf : BoundedPositiveJets f) (w : E) : BoundedJets (fun x => fderiv ℝ f x w) := by
  obtain ⟨B,hB,hBound⟩ := hf.2 1 le_rfl
  apply (hf.fderiv_apply w).boundedJets (B*‖w‖) (mul_nonneg hB (norm_nonneg _))
  intro x
  apply (fderiv ℝ f x).le_opNorm w |>.trans
  rw [←norm_iteratedFDeriv_one]
  exact mul_le_mul_of_nonneg_right (hBound x) (norm_nonneg _)

theorem BoundedJets.fderiv_apply {f : E → ℝ} (hf : BoundedJets f) (w : E) :
    BoundedJets (fun x => fderiv ℝ f x w) := hf.positive.boundedJets_fderiv_apply w

theorem BoundedJets.comp_linear {f : E → ℝ} (hf : BoundedJets f)
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] (L : A →L[ℝ] E) :
    BoundedJets (f ∘ L) := by
  obtain ⟨B,hB,hBound⟩ := hf.2 0
  apply (hf.positive.comp_linear L).boundedJets B hB
  intro x
  simpa only [norm_iteratedFDeriv_zero,Function.comp_apply] using hBound (L x)

theorem boundedJets_const (c : ℝ) : BoundedJets (fun _ : E => c) :=
  (boundedPositiveJets_const c).boundedJets ‖c‖ (norm_nonneg _) (fun _ => le_rfl)

theorem BoundedJets.add {f g : E → ℝ} (hf : BoundedJets f) (hg : BoundedJets g) :
    BoundedJets (fun x => f x+g x) := by
  refine ⟨hf.1.add hg.1,?_⟩
  intro j
  obtain ⟨B,hB,hfb⟩ := hf.2 j
  obtain ⟨C,hC,hgb⟩ := hg.2 j
  refine ⟨B+C,add_nonneg hB hC,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ j (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.1.of_le (by simp)).contDiffAt (hg.1.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hfb x) (hgb x))

theorem BoundedJets.const_mul {f : E → ℝ} (hf : BoundedJets f) (c : ℝ) :
    BoundedJets (fun x => c*f x) := by
  refine ⟨contDiff_const.mul hf.1,?_⟩
  intro j
  obtain ⟨B,hB,hfb⟩ := hf.2 j
  refine ⟨|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ j (fun x => c • f x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.1.of_le (by simp)).contDiffAt,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg _)

theorem BoundedJets.mul {f g : E → ℝ} (hf : BoundedJets f) (hg : BoundedJets g) :
    BoundedJets (fun x => f x*g x) := by
  refine ⟨hf.1.mul hg.1,?_⟩
  choose B hB hfb using hf.2
  choose C hC hgb using hg.2
  intro j
  let D := ∑ i ∈ Finset.range (j+1),(j.choose i : ℝ)*B i*C (j-i)
  refine ⟨D,Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hC (j-i))),fun x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le hf.1 hg.1 x (by simp)).trans
  exact Finset.sum_le_sum fun i _ => by
    have hbc : ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (j-i) g x‖ ≤ B i*C (j-i) :=
      mul_le_mul (hfb i x) (hgb (j-i) x) (norm_nonneg _) (hB i)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbc (Nat.cast_nonneg (j.choose i))

theorem boundedJets_finite_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S,BoundedJets (f i)) : BoundedJets (fun x => ∑ i ∈ S,f i x) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using boundedJets_const (E := E) 0
  | @insert i S hi ih =>
    have hh := (hf i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh

end QuantitativePaper
