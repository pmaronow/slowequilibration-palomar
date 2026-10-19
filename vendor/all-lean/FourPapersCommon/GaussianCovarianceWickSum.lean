module

public import FourPapersCommon.GaussianLinearWickSum

@[expose] public section

/-! The complete finite Wick polynomial depends only on the genuine
pair covariance. Each label is used exactly once in the recursive
pair contraction, and coincident directions retain distinct labels. -/
noncomputable section
open scoped BigOperators
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 700000
variable {κ ι : Type} [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def covarianceWickSum (C : κ→κ→ℝ) (I : Finset κ) : ℝ :=
  if hI : I.Nonempty then
    let i := hI.choose
    ∑ j ∈ I.erase i, C j i*covarianceWickSum C ((I.erase i).erase j)
  else 1
termination_by I.card
decreasing_by
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hI.choose_spec)

theorem gaussianLinearWickSum_eq_covariance (u : κ→EuclideanSpace ℝ ι) (I : Finset κ) :
    gaussianLinearWickSum u I=covarianceWickSum (fun i j => inner ℝ (u i) (u j)) I := by
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases hI : I.Nonempty
  · rw [gaussianLinearWickSum,covarianceWickSum,dif_pos hI,dif_pos hI]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih ((I.erase hI.choose).erase j) (Finset.ssubset_iff_subset_ne.mpr ⟨
      (Finset.erase_subset _ _).trans (Finset.erase_subset _ _),by
        intro hEq
        have hh : hI.choose ∈ (I.erase hI.choose).erase j := hEq.symm ▸ hI.choose_spec
        exact (Finset.notMem_erase hI.choose I) (Finset.mem_of_mem_erase hh)⟩)]
  · rw [gaussianLinearWickSum,covarianceWickSum,dif_neg hI,dif_neg hI]

theorem covarianceWickSum_congr (C D : κ→κ→ℝ) (I : Finset κ)
    (h : ∀ i∈I,∀ j∈I,C i j=D i j) : covarianceWickSum C I=covarianceWickSum D I := by
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases hI : I.Nonempty
  · rw [covarianceWickSum,covarianceWickSum,dif_pos hI,dif_pos hI]
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j (Finset.mem_of_mem_erase hj) hI.choose hI.choose_spec]
    congr 1
    apply ih ((I.erase hI.choose).erase j)
    · exact Finset.ssubset_iff_subset_ne.mpr ⟨
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _),by
          intro hEq
          have hh : hI.choose ∈ (I.erase hI.choose).erase j := hEq.symm ▸ hI.choose_spec
          exact (Finset.notMem_erase hI.choose I) (Finset.mem_of_mem_erase hh)⟩
    · intro i hi j hj
      exact h i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
        j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
  · rw [covarianceWickSum,covarianceWickSum,dif_neg hI,dif_neg hI]

end FourPapersCommon
