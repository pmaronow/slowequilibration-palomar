-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairedTensorProjectionFeatures

/-! Actual heterogeneous ordered tensor products, with vector free slots
and matrix pair slots. Unit block increments are proved from literal
coefficient Gram contractions. -/

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

def pairedBlockFeature {N q j : ℕ} (v : Fin q → Vector N)
    (W : Fin j → EuclideanSpace ℝ (Fin N × Fin N)) :
    EuclideanSpace ℝ (TensorIndex N (q+j+j)) :=
  WithLp.toLp 2 (fun I => (∏ k : Fin q,v k (I (freeSlot q j k)))*
    ∏ k : Fin j,W k (I (leftPairSlot q j k),I (rightPairSlot q j k)))

theorem pairedBlockFeature_apply_full {N q j : ℕ} (v : Fin q → Vector N)
    (W : Fin j → EuclideanSpace ℝ (Fin N × Fin N))
    (a : TensorIndex N q) (b c : TensorIndex N j) :
    pairedBlockFeature v W (fullTensorIndex a b c)=
      (∏ k : Fin q,v k (a k))*∏ k : Fin j,W k (b k,c k) := by
  simp only [pairedBlockFeature,freeSlot,leftPairSlot,rightPairSlot,fullTensorIndex,
    Fin.addCases_left,Fin.addCases_right]

/-- Literal original coefficient Gram product, allowing heterogeneous blocks. -/
theorem pairedBlockFeature_inner {N q j : ℕ} (v w : Fin q → Vector N)
    (A B : Fin j → EuclideanSpace ℝ (Fin N × Fin N)) :
    inner ℝ (pairedBlockFeature v A) (pairedBlockFeature w B)=
      (∏ k : Fin q,inner ℝ (v k) (w k))*
        ∏ k : Fin j,inner ℝ (A k) (B k) := by
  let f : Fin q → Fin N → ℝ := fun k i => w k i*v k i
  let F : Fin j → Fin N → Fin N → ℝ := fun k i l => B k (i,l)*A k (i,l)
  have he (a : TensorIndex N q) (b c : TensorIndex N j) :
      pairedBlockFeature w B (fullTensorIndex a b c)*pairedBlockFeature v A (fullTensorIndex a b c)=
        (∏ k : Fin q,f k (a k))*(∏ k : Fin j,F k (b k) (c k)) := by
    rw [pairedBlockFeature_apply_full,pairedBlockFeature_apply_full]
    dsimp only [f,F]
    simp only [Finset.prod_mul_distrib]
    ring
  have hfree (k : Fin q) : (∑ i : Fin N,f k i)=inner ℝ (v k) (w k) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,f]
  have hpair (k : Fin j) : (∑ i : Fin N,∑ l : Fin N,F k i l)=inner ℝ (A k) (B k) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_prod_type,F]
  change (∑ I,pairedBlockFeature w B I*pairedBlockFeature v A I)=_
  rw [sum_original_tensorIndex N q j]
  simp_rw [he,←Finset.mul_sum,←Finset.sum_mul]
  rw [sum_twoTensorIndex_product,←Fintype.prod_sum]
  simp only [hfree,hpair]

theorem pairedBlockFeature_norm_sq_of_unit {N q j : ℕ} (v : Fin q → Vector N)
    (A : Fin j → EuclideanSpace ℝ (Fin N × Fin N))
    (hv : ∀ k,‖v k‖=1) (hA : ∀ k,‖A k‖=1) :
    ‖pairedBlockFeature v A‖^2=1 := by
  rw [←real_inner_self_eq_norm_sq,pairedBlockFeature_inner]
  simp [hv,hA]

/-- True square-root metric of the literal heterogeneous tensor product. -/
theorem pairedBlockFeature_increment_sq_le {N q j : ℕ} (v w : Fin q → Vector N)
    (A B : Fin j → EuclideanSpace ℝ (Fin N × Fin N))
    (hv : ∀ k,‖v k‖=1) (hw : ∀ k,‖w k‖=1)
    (hA : ∀ k,‖A k‖=1) (hB : ∀ k,‖B k‖=1) :
    ‖pairedBlockFeature v A-pairedBlockFeature w B‖^2 ≤
      (∑ k : Fin q,‖v k-w k‖^2)+(∑ k : Fin j,‖A k-B k‖^2) := by
  let z : Fin (q+j) → ℝ := Fin.addCases (fun k => inner ℝ (v k) (w k))
    (fun k => inner ℝ (A k) (B k))
  have hz (k : Fin (q+j)) : |z k| ≤ 1 := by
    refine Fin.addCases ?_ ?_ k
    · intro k
      simpa [z,hv,hw] using abs_real_inner_le_norm (v k) (w k)
    · intro k
      simpa [z,hA,hB] using abs_real_inner_le_norm (A k) (B k)
  have h := one_sub_prod_le_sum Finset.univ z (fun k _ => hz k)
  have hp : (∏ k : Fin (q+j),z k)=
      (∏ k : Fin q,inner ℝ (v k) (w k))*(∏ k : Fin j,inner ℝ (A k) (B k)) := by
    simp only [Fin.prod_univ_add,z,Fin.addCases_left,Fin.addCases_right]
  have hs : (∑ k : Fin (q+j),(1-z k))=
      (∑ k : Fin q,(1-inner ℝ (v k) (w k)))+
        ∑ k : Fin j,(1-inner ℝ (A k) (B k)) := by
    simp only [Fin.sum_univ_add,z,Fin.addCases_left,Fin.addCases_right]
  rw [hp,hs] at h
  rw [norm_sub_sq_real,pairedBlockFeature_norm_sq_of_unit v A hv hA,
    pairedBlockFeature_norm_sq_of_unit w B hw hB,pairedBlockFeature_inner]
  have hvw : (∑ k : Fin q,‖v k-w k‖^2)=2*∑ k : Fin q,(1-inner ℝ (v k) (w k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [norm_sub_sq_real,hv,hw]
    ring
  have hAB : (∑ k : Fin j,‖A k-B k‖^2)=2*∑ k : Fin j,(1-inner ℝ (A k) (B k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [norm_sub_sq_real,hA,hB]
    ring
  rw [hvw,hAB]
  linarith

/-- True original x^q Π_x^j feature is this concrete heterogeneous product. -/
theorem pairedTensorFeature_eq_pairedBlockFeature {N q j : ℕ} (x : Vector N) :
    pairedTensorFeature N q j x=pairedBlockFeature (fun _ : Fin q => x)
      (fun _ : Fin j => projectionMatrixFeature x) := rfl

/-- Exact covariance before any Gaussian law is transported. -/
theorem pairedTensorFeature_inner {N q j : ℕ} (x y : Vector N) :
    inner ℝ (pairedTensorFeature N q j x) (pairedTensorFeature N q j y)=
      (inner ℝ x y)^q*(inner ℝ (projectionMatrixFeature x) (projectionMatrixFeature y))^j := by
  rw [pairedTensorFeature_eq_pairedBlockFeature,pairedTensorFeature_eq_pairedBlockFeature,
    pairedBlockFeature_inner]
  simp

theorem pairedTensorFeature_norm_sq {N q j : ℕ} (hN : 0<N) (x : Vector N)
    (hx : ‖x‖^2=(N : ℝ)) :
    ‖pairedTensorFeature N q j x‖^2=(N : ℝ)^q*((N : ℝ)-1)^j := by
  rw [←real_inner_self_eq_norm_sq,pairedTensorFeature_inner,real_inner_self_eq_norm_sq,
    hx,real_inner_self_eq_norm_sq,projectionMatrixFeature_norm_sq hN x hx]

end
end SlowEquilibration.PairedTensorProjectionFeatures
