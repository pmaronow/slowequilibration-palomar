-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalProjectionMatrixFeature
public import SlowEquilibration.OrderedTensorSingleProjectedTrace

/-! Actual ordered coefficient features x^⊗q ⊗ Π_x^⊗j. Their pair block
contractions are literal original coordinate sums, so value and one-gradient
rows at the same conditioning axis can be annihilated before any posterior
law transport. -/

@[expose] public section
namespace SlowEquilibration.PairedTensorProjectionFeatures
noncomputable section
open SphericalAging.FiniteModel SphericalProjectionMatrixFeature
open OrderedTensorTraceGaussianBank PureTensorJetFeatures
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def freeSlot (q j : ℕ) (k : Fin q) : Fin (q+j+j) := Fin.castAdd j (Fin.castAdd j k)
def leftPairSlot (q j : ℕ) (k : Fin j) : Fin (q+j+j) := Fin.castAdd j (Fin.natAdd q k)
def rightPairSlot (q j : ℕ) (k : Fin j) : Fin (q+j+j) := Fin.natAdd (q+j) k

def pairedTensorFeature (N q j : ℕ) (x : Vector N) : EuclideanSpace ℝ (TensorIndex N (q+j+j)) :=
  WithLp.toLp 2 (fun I => (∏ k : Fin q,x (I (freeSlot q j k)))*
    ∏ k : Fin j,projectionMatrixFeature x (I (leftPairSlot q j k),I (rightPairSlot q j k)))

theorem pairedTensorFeature_apply_full {N q j : ℕ} (x : Vector N)
    (a : TensorIndex N q) (b c : TensorIndex N j) :
    pairedTensorFeature N q j x (fullTensorIndex a b c)=
      (∏ k : Fin q,x (a k))*∏ k : Fin j,projectionMatrixFeature x (b k,c k) := by
  simp only [pairedTensorFeature,freeSlot,leftPairSlot,rightPairSlot,fullTensorIndex,
    Fin.addCases_left,Fin.addCases_right]

theorem tensorFeature_apply_full {N q j : ℕ} (v : Fin (q+j+j) → Vector N)
    (a : TensorIndex N q) (b c : TensorIndex N j) :
    tensorFeature v (fullTensorIndex a b c)=
      (∏ k : Fin q,v (freeSlot q j k) (a k))*
      (∏ k : Fin j,v (leftPairSlot q j k) (b k))*
      ∏ k : Fin j,v (rightPairSlot q j k) (c k) := by
  rw [tensorFeature_apply,Fin.prod_univ_add,Fin.prod_univ_add]
  simp only [fullTensorIndex,Fin.addCases_left,Fin.addCases_right,
    freeSlot,leftPairSlot,rightPairSlot]

/-- Genuine repeated coordinate sum for all independent ordered pair slots. -/
theorem sum_twoTensorIndex_product (N j : ℕ) (F : Fin j → Fin N → Fin N → ℝ) :
    (∑ b : TensorIndex N j,∑ c : TensorIndex N j,∏ k : Fin j,F k (b k) (c k))=
      ∏ k : Fin j,∑ i : Fin N,∑ l : Fin N,F k i l := by
  calc
    _=∑ b : TensorIndex N j,∏ k : Fin j,∑ l : Fin N,F k (b k) l := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (Fintype.prod_sum (fun k l => F k (b k) l)).symm
    _=_ := (Fintype.prod_sum (fun k i => ∑ l : Fin N,F k i l)).symm

/-- Literal coefficient contraction with every original ordered tensor
product; paired rows remain actual Π_x matrix entries. -/
theorem pairedTensorFeature_tensorFeature_inner {N q j : ℕ} (x : Vector N)
    (v : Fin (q+j+j) → Vector N) :
    inner ℝ (pairedTensorFeature N q j x) (tensorFeature v)=
      (∏ k : Fin q,inner ℝ x (v (freeSlot q j k)))*
      ∏ k : Fin j,inner ℝ (projectionMatrixFeature x)
        (outerFeature (v (leftPairSlot q j k)) (v (rightPairSlot q j k))) := by
  let f : Fin q → Fin N → ℝ := fun k i => x i*v (freeSlot q j k) i
  let F : Fin j → Fin N → Fin N → ℝ := fun k i l =>
    projectionMatrixFeature x (i,l)*v (leftPairSlot q j k) i*v (rightPairSlot q j k) l
  have he (a : TensorIndex N q) (b c : TensorIndex N j) :
      tensorFeature v (fullTensorIndex a b c)*pairedTensorFeature N q j x (fullTensorIndex a b c)=
        (∏ k : Fin q,f k (a k))*(∏ k : Fin j,F k (b k) (c k)) := by
    rw [tensorFeature_apply_full,pairedTensorFeature_apply_full]
    dsimp only [f,F]
    simp only [Finset.prod_mul_distrib]
    ring
  have hfree (k : Fin q) : (∑ i : Fin N,f k i)=inner ℝ x (v (freeSlot q j k)) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,f]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpair (k : Fin j) : (∑ i : Fin N,∑ l : Fin N,F k i l)=
      inner ℝ (projectionMatrixFeature x)
        (outerFeature (v (leftPairSlot q j k)) (v (rightPairSlot q j k))) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,outerFeature,Fintype.sum_prod_type,F]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro l hl
    ring
  change (∑ I,tensorFeature v I*pairedTensorFeature N q j x I)=_
  rw [sum_original_tensorIndex N q j]
  simp_rw [he,←Finset.mul_sum,←Finset.sum_mul]
  rw [sum_twoTensorIndex_product]
  rw [←Fintype.prod_sum]
  simp only [hfree,hpair]

/-- A same-axis paired block kills value and arbitrary directional rows,
using only the literal projection entries, before any covariance premise. -/
theorem pairedTensorFeature_inner_zero_of_axis_pair {N q j : ℕ} (hN : 0 < N)
    (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) (v : Fin (q+j+j) → Vector N)
    (hpair : ∃ k : Fin j,v (leftPairSlot q j k)=x ∨ v (rightPairSlot q j k)=x) :
    inner ℝ (pairedTensorFeature N q j x) (tensorFeature v)=0 := by
  obtain ⟨k,hk⟩ := hpair
  rw [pairedTensorFeature_tensorFeature_inner]
  have hz : inner ℝ (projectionMatrixFeature x)
      (outerFeature (v (leftPairSlot q j k)) (v (rightPairSlot q j k)))=0 := by
    rcases hk with hl|hr
    · rw [hl]
      exact projectionMatrixFeature_outer_axis_inner hN x _ hx
    · rw [hr]
      exact projectionMatrixFeature_outer_axis_inner_right hN x _ hx
  rw [Finset.prod_eq_zero (Finset.mem_univ k) hz,mul_zero]

/-- Exact orthogonality to the original value/radial tensor direction. -/
theorem pairedTensorFeature_value_inner_zero {N : ℕ} (hN : 0 < N) (q j : ℕ) (hj : 0 < j)
    (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    inner ℝ (pairedTensorFeature N q j x) (tensorFeature (fun _ => x))=0 :=
  pairedTensorFeature_inner_zero_of_axis_pair hN x hx _ ⟨⟨0,hj⟩,Or.inl rfl⟩

theorem leftPairSlot_ne_rightPairSlot {q j : ℕ} (hj : 0 < j) (k : Fin j) :
    leftPairSlot q j k≠rightPairSlot q j k := by
  intro h
  have hv := congrArg Fin.val h
  simp only [leftPairSlot,rightPairSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Every original one-gradient insertion leaves an axis factor in a
paired slot, so the true directional gradient row is orthogonal. -/
theorem pairedTensorFeature_insertion_inner_zero {N : ℕ} (hN : 0 < N) (q j : ℕ) (hj : 0 < j)
    (x h : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    inner ℝ (pairedTensorFeature N q j x)
      (insertionFeature (p := q+j+j) (Fin.cons x (fun _ : Fin 1 => h)))=0 := by
  classical
  unfold insertionFeature
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro e he
  apply pairedTensorFeature_inner_zero_of_axis_pair hN x hx
  let k : Fin j := ⟨0,hj⟩
  by_cases hL : leftPairSlot q j k∈Set.range e
  · have hR : rightPairSlot q j k∉Set.range e := by
      rintro ⟨b,hb⟩
      obtain ⟨a,ha⟩ := hL
      have hab : a=b := Subsingleton.elim _ _
      rw [hab] at ha
      exact leftPairSlot_ne_rightPairSlot hj k (ha.symm.trans hb)
    refine ⟨k,Or.inr ?_⟩
    simp only [Function.comp_apply,insertionSlot,dite_eq_right hR,Fin.cons_zero]
  · refine ⟨k,Or.inl ?_⟩
    simp only [Function.comp_apply,insertionSlot,dite_eq_right hL,Fin.cons_zero]

/-- The literal original ordered Hamiltonian of this coefficient feature
vanishes at its own physical axis, including all higher trace orders. -/
theorem pairedTensorFeature_Hamiltonian_axis_zero {N : ℕ} (hN : 0 < N) (q j : ℕ) (hj : 0 < j)
    (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    Hamiltonian N (q+j+j) (fun I => pairedTensorFeature N q j x I) x=0 := by
  have hv := pairedTensorFeature_value_inner_zero hN q j hj x hx
  rw [real_inner_comm] at hv
  change (∑ I,pairedTensorFeature N q j x I*tensorMonomial x I)=0 at hv
  unfold Hamiltonian
  rw [hv,mul_zero]

/-- True original directional derivative of the projected coefficient
Hamiltonian is zero at its own axis; no jet covariance is postulated. -/
theorem pairedTensorFeature_Hamiltonian_directional_zero {N : ℕ} (hN : 0 < N) (q j : ℕ) (hj : 0 < j)
    (x h : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    fderiv ℝ (Hamiltonian N (q+j+j) (fun I => pairedTensorFeature N q j x I)) x h=0 := by
  have hz := pairedTensorFeature_insertion_inner_zero hN q j hj x h hx
  rw [real_inner_comm] at hz
  have hd := Hamiltonian_iteratedFDeriv_eq_inner (p := q+j+j) (j := 1)
    (fun I => pairedTensorFeature N q j x I) x (fun _ : Fin 1 => h)
  simp only [iteratedFDeriv_one_apply] at hd
  change fderiv ℝ (Hamiltonian N (q+j+j) (fun I => pairedTensorFeature N q j x I)) x h=_ at hd
  have hflat : WithLp.toLp 2 (fun I => pairedTensorFeature N q j x I)=pairedTensorFeature N q j x := rfl
  rw [hflat,hz,mul_zero] at hd
  exact hd

end
end SlowEquilibration.PairedTensorProjectionFeatures
