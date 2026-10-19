module

public import FourPapersCommon.GaussianLinearProductWick

@[expose] public section

/-! Complete finite Gaussian Wick contractions, with distinct labeled
positions allowed to carry identical projection directions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

def gaussianLinearWickSum (u : κ → EuclideanSpace ℝ ι) (I : Finset κ) : ℝ :=
  if hI : I.Nonempty then
    let i := hI.choose
    ∑ j ∈ I.erase i, inner ℝ (u j) (u i)*gaussianLinearWickSum u ((I.erase i).erase j)
  else 1
termination_by I.card
decreasing_by
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hI.choose_spec)

theorem integral_gaussian_linear_product_eq_wick
    (I : Finset κ) (u : κ → EuclideanSpace ℝ ι) :
    (∫ z, (∏ i ∈ I, inner ℝ (u i) z) ∂stdGaussian (EuclideanSpace ℝ ι)) =
      gaussianLinearWickSum u I := by
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases hI : I.Nonempty
  · let i := hI.choose
    have hi : i ∈ I := hI.choose_spec
    rw [gaussianLinearWickSum,dif_pos hI]
    have he (z : EuclideanSpace ℝ ι) :
        (∏ j ∈ I, inner ℝ (u j) z) =
          inner ℝ z (u i)*(∏ j ∈ I.erase i, inner ℝ (u j) z) := by
      rw [←Finset.insert_erase hi,Finset.prod_insert (Finset.notMem_erase i I),
        real_inner_comm]
      simp
    simp_rw [he]
    rw [integral_gaussian_linear_product_stein]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih ((I.erase i).erase j) (Finset.ssubset_iff_subset_ne.mpr ⟨
      (Finset.erase_subset _ _).trans (Finset.erase_subset _ _),by
        intro hEq
        have hh : i ∈ (I.erase i).erase j := hEq.symm ▸ hi
        exact (Finset.notMem_erase i I) (Finset.mem_of_mem_erase hh)⟩)]
  · have he : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    simp [gaussianLinearWickSum]

end FourPapersCommon
