module

public import OverlapPaper.DSFiniteGram
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Genuine continuous relabeling of off-diagonal overlap arrays, finite
permutation extension, and closedness of weak exchangeability. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology MatrixOrder
namespace OverlapPaper
set_option maxHeartbeats 500000

theorem completeArray_mem_Icc (R : OverlapArray) (i j : ℕ) : completeArray R i j∈Icc (-1:ℝ) 1 := by
  unfold completeArray
  split_ifs
  · exact (R _).2
  · exact (R _).2
  · norm_num

theorem completeArray_of_lt (R : OverlapArray) {i j : ℕ} (hij : i < j) :
    completeArray R i j=(R ⟨(i,j),hij⟩ : ℝ) := by simp [completeArray,hij]

theorem completeArray_of_gt (R : OverlapArray) {i j : ℕ} (hij : j < i) :
    completeArray R i j=(R ⟨(j,i),hij⟩ : ℝ) := by
  simp [completeArray,hij,not_lt_of_ge hij.le]

theorem completeArray_symm (R : OverlapArray) (i j : ℕ) : completeArray R i j=completeArray R j i := by
  by_cases hij : i < j
  · rw [completeArray_of_lt R hij,completeArray_of_gt R hij]
  · by_cases hji : j < i
    · rw [completeArray_of_gt R hji,completeArray_of_lt R hji]
    · have he : i=j := by omega
      subst j
      rfl

@[simp] theorem completeArray_self (R : OverlapArray) (i : ℕ) : completeArray R i i=1 := by
  simp [completeArray]

def arrayRelabel (σ : Equiv.Perm ℕ) (R : OverlapArray) : OverlapArray := fun ij =>
  ⟨completeArray R (σ ij.1.1) (σ ij.1.2),completeArray_mem_Icc R _ _⟩

theorem completeArray_arrayRelabel (σ : Equiv.Perm ℕ) (R : OverlapArray) (i j : ℕ) :
    completeArray (arrayRelabel σ R) i j=completeArray R (σ i) (σ j) := by
  by_cases hij : i < j
  · rw [completeArray_of_lt _ hij]
    rfl
  · by_cases hji : j < i
    · rw [completeArray_of_gt _ hji]
      exact completeArray_symm R _ _
    · have he : i=j := by omega
      subst j
      simp

theorem continuous_arrayRelabel (σ : Equiv.Perm ℕ) : Continuous (arrayRelabel σ) := by
  apply continuous_pi
  intro ij
  apply Continuous.subtype_mk
  exact continuous_completeArray (σ ij.1.1) (σ ij.1.2)

theorem arrayRelabel_refl (R : OverlapArray) : arrayRelabel (Equiv.refl ℕ) R=R := by
  funext ij
  apply Subtype.ext
  simp [arrayRelabel,completeArray,ij.2]

theorem completeArray_finiteIndex_posSemidef (R : OverlapArray) (hR : R∈GramArrays)
    {m : ℕ} (f : Fin m→ℕ) : (Matrix.of (fun i j => completeArray R (f i) (f j))).PosSemidef := by
  let N := Finset.univ.sup f+1
  have hb (i : Fin m) : f i<N := Nat.lt_succ_of_le (Finset.le_sup (f := f) (Finset.mem_univ i))
  let b : Fin m→Fin N := fun i => ⟨f i,hb i⟩
  exact (hR N).submatrix b

theorem arrayRelabel_mem_GramArrays (σ : Equiv.Perm ℕ) (R : OverlapArray)
    (hR : R∈GramArrays) : arrayRelabel σ R∈GramArrays := by
  intro m
  have he : principalMatrix (arrayRelabel σ R) m=
      Matrix.of (fun i j : Fin m => completeArray R (σ i.val) (σ j.val)) := by
    ext i j
    exact completeArray_arrayRelabel σ R i.val j.val
  rw [he]
  exact completeArray_finiteIndex_posSemidef R hR (fun i : Fin m => σ i.val)

def WeaklyExchangeableOverlapLaw (ν : ProbabilityMeasure OverlapArray) : Prop :=
  ∀σ : Equiv.Perm ℕ,({i | σ i≠i}:Set ℕ).Finite → ν.map (arrayRelabel σ)=ν

theorem isClosed_weaklyExchangeableOverlapLaws :
    IsClosed {ν : ProbabilityMeasure OverlapArray | WeaklyExchangeableOverlapLaw ν} := by
  have he : {ν : ProbabilityMeasure OverlapArray | WeaklyExchangeableOverlapLaw ν}=
      ⋂σ : Equiv.Perm ℕ,⋂_ : ({i | σ i≠i}:Set ℕ).Finite,
        {ν : ProbabilityMeasure OverlapArray | ν.map (arrayRelabel σ)=ν} := by
    ext ν
    simp [WeaklyExchangeableOverlapLaw]
  rw [he]
  apply isClosed_iInter
  intro σ
  apply isClosed_iInter
  intro _
  exact isClosed_eq (ProbabilityMeasure.continuous_map (continuous_arrayRelabel σ)) continuous_id

theorem weaklyExchangeableOverlapLaw_of_tendsto {ν : ProbabilityMeasure OverlapArray}
    {νn : ℕ→ProbabilityMeasure OverlapArray} (hlim : Tendsto νn atTop (𝓝 ν))
    (hex : ∀ᶠn in atTop,WeaklyExchangeableOverlapLaw (νn n)) : WeaklyExchangeableOverlapLaw ν :=
  isClosed_weaklyExchangeableOverlapLaws.mem_of_tendsto hlim hex

def extendFinitePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ :=
  (finSumNatEquiv n).symm.trans ((Equiv.sumCongr σ (Equiv.refl ℕ)).trans (finSumNatEquiv n))

@[simp] theorem extendFinitePermutation_apply_fin {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendFinitePermutation σ i.val=(σ i).val := by
  simp [extendFinitePermutation,finSumNatEquiv_symm_apply_of_lt i.isLt]

theorem extendFinitePermutation_apply_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : ℕ} (hi : n ≤ i) :
    extendFinitePermutation σ i=i := by
  simp [extendFinitePermutation,finSumNatEquiv_symm_apply_of_ge hi,Nat.add_sub_cancel' hi]

theorem extendFinitePermutation_finite_moves {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ({i | extendFinitePermutation σ i≠i}:Set ℕ).Finite := by
  apply (Finset.finite_toSet (Finset.range n)).subset
  intro i hi
  simp only [Finset.mem_coe,Finset.mem_range]
  by_contra hh
  have hge : n ≤ i := Nat.le_of_not_gt hh
  exact hi (extendFinitePermutation_apply_ge (i := i) σ hge)

end OverlapPaper
