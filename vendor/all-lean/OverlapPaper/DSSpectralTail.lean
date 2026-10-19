module

public import OverlapPaper.DSFiniteGram
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-! Dimension-independent spectral tails for the empirical Gram construction.
The estimate is the reason coordinate limits can preserve off-diagonal Gram
laws. It is a deterministic spectral estimate, not an assumption of the
directing-measure representation. -/
noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators
namespace OverlapPaper
set_option maxHeartbeats 800000

theorem antitone_nonneg_coordinate_bound {n : ℕ} (eig : Fin n → ℝ)
    (heig : Antitone eig) (h0 : ∀ i,0 ≤ eig i) (hsum : ∑ i,eig i ≤ 1) (k : Fin n) :
    ((k.val+1:ℕ):ℝ)*eig k ≤ 1 := by
  have hprefix : ∑ i ∈ Finset.Iic k,eig k ≤ ∑ i ∈ Finset.Iic k,eig i := by
    apply Finset.sum_le_sum
    intro i hi
    exact heig (Finset.mem_Iic.mp hi)
  have hsub : ∑ i ∈ Finset.Iic k,eig i ≤ ∑ i,eig i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => h0 i)
  simpa only [Finset.sum_const,Fin.card_Iic,nsmul_eq_mul] using hprefix.trans (hsub.trans hsum)

theorem antitone_nonneg_spectral_tail {n : ℕ} (eig : Fin n → ℝ)
    (heig : Antitone eig) (h0 : ∀ i,0 ≤ eig i) (hsum : ∑ i,eig i ≤ 1) (M : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => M ≤ i.val),(eig i)^2 ≤
      1/((M+1:ℕ):ℝ) := by
  have hpos : 0 < ((M+1:ℕ):ℝ) := by positivity
  have hbound (i : Fin n) (hi : M ≤ i.val) : eig i ≤ 1/((M+1:ℕ):ℝ) := by
    apply (le_div_iff₀ hpos).mpr
    have hc : ((M+1:ℕ):ℝ) ≤ ((i.val+1:ℕ):ℝ) := by exact_mod_cast Nat.add_le_add_right hi 1
    calc
      _ = ((M+1:ℕ):ℝ)*eig i := mul_comm _ _
      _ ≤ ((i.val+1:ℕ):ℝ)*eig i := mul_le_mul_of_nonneg_right hc (h0 i)
      _ ≤ 1 := antitone_nonneg_coordinate_bound eig heig h0 hsum i
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => M ≤ i.val),
        (1/((M+1:ℕ):ℝ))*eig i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hbound i (Finset.mem_filter.mp hi).2) (h0 i)
    _ = (1/((M+1:ℕ):ℝ))*(∑ i ∈ Finset.univ.filter (fun i : Fin n => M ≤ i.val),eig i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (1/((M+1:ℕ):ℝ))*1 := mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => h0 i)).trans hsum)
      (by positivity)
    _ = _ := mul_one _

end OverlapPaper
