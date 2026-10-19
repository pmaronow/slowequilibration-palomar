-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianMaximalCorrelation
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Genuine exact second moments of centered finite Gaussian quadratic
forms, obtained from the proved product Hermite orthogonality. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def quadraticIndex (i : ι) : ι → ℕ := Function.update (fun _=>0) i 2

def centeredSquare (i : ι) (x : ι → ℝ) : ℝ := x i^2-1

omit [Fintype ι] in
lemma quadraticIndex_injective : Injective (quadraticIndex (ι:=ι)) := by
  intro i j hij
  by_contra hne
  have h:=congrFun hij i
  simp only [quadraticIndex,Function.update_self,Function.update_of_ne hne] at h
  norm_num at h

omit [Fintype ι] in
lemma quadraticIndex_ne_zero (i : ι) : quadraticIndex i≠(fun _=>0) := by
  intro h
  have hh:=congrFun h i
  simp only [quadraticIndex,Function.update_self] at hh
  norm_num at hh

lemma he_two (t : ℝ) : he 2 t=t^2-1 := by
  have h:=he_recurrence 0 t
  simpa [he_one,he_zero,pow_two] using h

lemma psi_quadraticIndex (i : ι) (x : ι → ℝ) :
    psi (quadraticIndex i) x=H 2 (x i) := by
  unfold psi
  rw [Finset.prod_eq_single i]
  · simp [quadraticIndex]
  · intro j hj hji
    simp [quadraticIndex,Function.update_of_ne hji,H]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

lemma centeredSquare_eq_psi (i : ι) :
    centeredSquare i=(fun x:ι→ℝ=>Real.sqrt 2*psi (quadraticIndex i) x) := by
  funext x
  rw [psi_quadraticIndex]
  unfold H
  rw [he_two]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  unfold centeredSquare
  field_simp

lemma centeredSquare_memLp (i : ι) : MemLp (centeredSquare i) 2 (γpi ι) := by
  rw [centeredSquare_eq_psi]
  exact (memLp_psi (quadraticIndex i)).const_mul _

lemma centeredSquare_mean (i : ι) : (∫ x,centeredSquare i x ∂γpi ι)=0 := by
  rw [centeredSquare_eq_psi,integral_const_mul]
  have h:=psi_product (quadraticIndex i) (fun _=>0)
  have h0 : psi (fun _ : ι=>0)=(fun _ : ι→ℝ=>1) := by
    funext x
    simp [psi,H]
  rw [h0] at h
  simp only [mul_one,ite_eq_right (quadraticIndex_ne_zero i)] at h
  rw [h,mul_zero]

lemma centeredSquare_product (i j : ι) :
    (∫ x,centeredSquare i x*centeredSquare j x ∂γpi ι)=if i=j then 2 else 0 := by
  simp only [centeredSquare_eq_psi]
  have heq : (fun x:ι→ℝ=> (Real.sqrt 2*psi (quadraticIndex i) x)*(Real.sqrt 2*psi (quadraticIndex j) x))=
      (fun x=>2*(psi (quadraticIndex i) x*psi (quadraticIndex j) x)) := by
    funext x
    calc
      _=Real.sqrt 2^2*(psi (quadraticIndex i) x*psi (quadraticIndex j) x) := by ring
      _=_ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [heq,integral_const_mul,psi_product]
  simp only [quadraticIndex_injective.eq_iff]
  split_ifs <;> norm_num

def diagonalQuadratic (w : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i,w i*centeredSquare i x

lemma diagonalQuadratic_memLp (w : ι → ℝ) : MemLp (diagonalQuadratic w) 2 (γpi ι) :=
  memLp_finsetSum _ (fun i _=>(centeredSquare_memLp i).const_mul (w i))

lemma diagonalQuadratic_mean (w : ι → ℝ) : (∫ x,diagonalQuadratic w x ∂γpi ι)=0 := by
  unfold diagonalQuadratic
  rw [integral_finsetSum _ (fun i _=>(centeredSquare_memLp i).integrable (by norm_num) |>.const_mul (w i))]
  simp only [integral_const_mul,centeredSquare_mean,mul_zero,Finset.sum_const_zero]

/-- Exact Gaussian quadratic variance, with no probabilistic moment input. -/
theorem diagonalQuadratic_second_moment (w : ι → ℝ) :
    (∫ x,diagonalQuadratic w x^2 ∂γpi ι)=2*∑ i,w i^2 := by
  have heq : (fun x:ι→ℝ=>diagonalQuadratic w x^2)=
      (fun x=>∑ i,∑ j,(w i*w j)*(centeredSquare i x*centeredSquare j x)) := by
    funext x
    simp only [diagonalQuadratic,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hint (i j : ι) : Integrable (fun x=>(w i*w j)*(centeredSquare i x*centeredSquare j x)) (γpi ι) :=
    ((centeredSquare_memLp i).integrable_mul (centeredSquare_memLp j)).const_mul _
  rw [heq,integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hint i j))]
  simp only [integral_finsetSum _ (fun j _=>hint _ j),integral_const_mul,centeredSquare_product]
  simp [mul_ite,Finset.mul_sum,pow_two,mul_comm,mul_assoc]

end
end SlowEquilibration.GaussianQuadraticVariance
