-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceTensorPolynomial
public import SlowEquilibration.SphericalConditionedEntranceCorrection
public import SlowEquilibration.UniformC1PolynomialApproximation
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Concrete ordered coefficient tensors for the entrance cutoff polynomial
approximants. Products of scalar polynomial cutoffs with the actual regression
correction remain exact physical finite-mixture fields. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.TensorPolynomial
open SphericalModel SphericalForm
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N P₀ P : ℕ}

def multiplyAtom (a : Atom N P₀) (u v : Vector N) (i j : ℕ)
    (hP : a.degree.val.val+(i+j) ≤ P) (b : ℝ) : Atom N P where
  degree := ⟨⟨a.degree.val.val+(i+j),Nat.lt_succ_of_le hP⟩,by
    change 2 ≤ a.degree.val.val+(i+j)
    have ha:=a.degree.property
    omega⟩
  coefficient := b*a.coefficient
  factors := Fin.append a.factors (Fin.append (fun _ : Fin i => u) (fun _ : Fin j => v))

theorem multiplyAtom_value (a : Atom N P₀) (u v : Vector N) (i j : ℕ)
    (hP : a.degree.val.val+(i+j) ≤ P) (b : ℝ) (x : Vector N) :
    (multiplyAtom a u v i j hP b).value x=b*a.value x*(inner ℝ u x)^i*(inner ℝ v x)^j := by
  unfold Atom.value multiplyAtom
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

theorem polynomial_eval_fin_sum (p : Polynomial ℝ) (r : ℝ) :
    p.eval r=∑ i : Fin (p.natDegree+1),p.coeff i*r^(i : ℕ) := by
  exact (Polynomial.eval_eq_sum_range r).trans
    (Fin.sum_univ_eq_sum_range (fun j : ℕ => p.coeff j*r^j) (p.natDegree+1)).symm

def polynomialProductAtom {ι : Type*} (a : ι → Atom N P₀)
    (u v : Vector N) (p q : Polynomial ℝ)
    (z : ι × Fin (p.natDegree+1) × Fin (q.natDegree+1)) :
    Atom N (P₀+(p.natDegree+q.natDegree)) :=
  multiplyAtom (a z.1) u v z.2.1 z.2.2
    (by have ha:=Nat.le_of_lt_succ (a z.1).degree.val.isLt
        have hi:=Nat.le_of_lt_succ z.2.1.isLt
        have hj:=Nat.le_of_lt_succ z.2.2.isLt
        omega)
    (p.coeff z.2.1*q.coeff z.2.2)

/-- The actual product cutoff, expanded before choosing a coefficient law. -/
theorem polynomialProductAtom_sum {ι : Type*} [Fintype ι] (a : ι → Atom N P₀)
    (u v : Vector N) (p q : Polynomial ℝ) (x : Vector N) :
    (∑ z : ι × Fin (p.natDegree+1) × Fin (q.natDegree+1),
      (polynomialProductAtom a u v p q z).value x)=
      p.eval (inner ℝ u x)*q.eval (inner ℝ v x)*(∑ i,(a i).value x) := by
  simp only [Fintype.sum_prod_type,polynomialProductAtom,multiplyAtom_value]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [polynomial_eval_fin_sum,polynomial_eval_fin_sum,Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite polynomial cutoff of a represented correction is an
actual finite ordered-tensor field, without an approximation premise. -/
theorem polynomial_cutoff_exists_physical_mixture (hN : 1 ≤ N) (hP₀ : 2 ≤ P₀)
    {ι : Type*} [Fintype ι] (a : ι → Atom N P₀)
    (u v : Vector N) (p q : Polynomial ℝ) :
    ∃ μ : FiniteMixture, ∃ J : Disorder N μ.maxDegree,
      fieldOfMixture μ J=fun x => p.eval (inner ℝ u x)*q.eval (inner ℝ v x)*(∑ i,(a i).value x) := by
  obtain ⟨μ,J,hJ⟩ := atomBank_exists_physical_mixture hN
    (by omega : 2 ≤ P₀+(p.natDegree+q.natDegree)) (polynomialProductAtom a u v p q)
  refine ⟨μ,J,?_⟩
  rw [hJ]
  funext x
  exact polynomialProductAtom_sum a u v p q x

abbrev CorrectionIndex (μ : FiniteMixture) := Bool × μ.coeff.support

def regressionCorrectionAtom (μ : FiniteMixture) (Q : ℝ) (u G : Vector N)
    (Hq Kq h k : ℝ) (z : CorrectionIndex μ) : Atom N μ.maxDegree :=
  if z.1 then
    twoLinearAtom ((N : ℝ)⁻¹ • u) G (z.2.val-1) 1
      (by have hp:=μ.degree_ge_two z.2.property; omega)
      (by have hp:=μ.degree_ge_two z.2.property; have hd:=(μ.degree_bounds z.2.property).2; omega)
      (-tangentCoefficient μ Q z.2.val)
  else
    twoLinearAtom ((N : ℝ)⁻¹ • u) G z.2.val 0
      (by have hp:=μ.degree_ge_two z.2.property; omega)
      (by have hd:=(μ.degree_bounds z.2.property).2; omega)
      (valueCoefficient μ Q z.2.val*((N : ℝ)*h-Hq)+
        radialCoefficient μ Q z.2.val*((N : ℝ)*k-Kq))

/-- The actual source correction polynomial is exactly the finite atom
family attached to the same observed value, radial jet, and gradient. -/
theorem regressionCorrection_atom_sum (μ : FiniteMixture) (Q : ℝ) (u G : Vector N)
    (Hq Kq h k : ℝ) (x : Vector N) :
    (∑ z : CorrectionIndex μ,(regressionCorrectionAtom μ Q u G Hq Kq h k z).value x)=
      regressionCorrection μ Q u G Hq Kq h k x := by
  have hr : inner ℝ ((N : ℝ)⁻¹ • u) x=overlap x u := by
    rw [real_inner_smul_left]
    have hc : inner ℝ u x=inner ℝ x u := real_inner_comm _ _
    rw [hc]
    exact (div_eq_inv_mul _ _).symm
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [regressionCorrectionAtom,ite_true,Bool.coe_false,ite_false,
    twoLinearAtom_value,hr,pow_one,pow_zero,mul_one]
  have hs (f : ℕ → ℝ) : (∑ p : μ.coeff.support,f p)=∑ p∈μ.coeff.support,f p :=
    Finset.sum_coe_sort _ _
  rw [hs (fun p => -tangentCoefficient μ Q p*(overlap x u)^(p-1)*inner ℝ G x),
    hs (fun p => (valueCoefficient μ Q p*((N : ℝ)*h-Hq)+
      radialCoefficient μ Q p*((N : ℝ)*k-Kq))*(overlap x u)^p)]
  unfold regressionCorrection valueTheta radialTheta tangentTheta monomialSum
  simp only [id_eq,Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The polynomial cutoff perturbation and the original realized field
are together represented in a single actual mixed tensor bank. -/
theorem original_plus_polynomial_cutoff_exists_physical_mixture
    (hN : 1 ≤ N) (hP₀ : 2 ≤ P₀) (μ₀ : FiniteMixture)
    (J₀ : Disorder N μ₀.maxDegree) (h₀ : μ₀.maxDegree ≤ P₀)
    {ι : Type*} [Fintype ι] (a : ι → Atom N P₀)
    (u v : Vector N) (p q : Polynomial ℝ) :
    ∃ μ : FiniteMixture, ∃ J : Disorder N μ.maxDegree,
      fieldOfMixture μ J=fun x => fieldOfMixture μ₀ J₀ x+
        p.eval (inner ℝ u x)*q.eval (inner ℝ v x)*(∑ i,(a i).value x) := by
  let A := Sum.elim
    (originalAtom μ₀ J₀ (show μ₀.maxDegree ≤ P₀+(p.natDegree+q.natDegree) by omega))
    (polynomialProductAtom a u v p q)
  obtain ⟨μ,J,hJ⟩ := atomBank_exists_physical_mixture hN
    (by omega : 2 ≤ P₀+(p.natDegree+q.natDegree)) A
  refine ⟨μ,J,?_⟩
  rw [hJ]
  funext x
  simp only [Fintype.sum_sum_type,A,Sum.elim_inl,Sum.elim_inr]
  rw [originalField_atom_sum,polynomialProductAtom_sum]

/-- The literal entrance regression polynomial, cut off by two ordinary
scalar polynomial approximants, plus the original field is an actual
physical finite-mixture Hamiltonian. Observed marks remain explicit. -/
theorem regression_polynomial_cutoff_exists_physical_mixture (hN : 1 ≤ N)
    (μ₀ : FiniteMixture) (J₀ : Disorder N μ₀.maxDegree) (Q : ℝ)
    (u G v₁ v₂ : Vector N) (Hq Kq h k : ℝ) (p q : Polynomial ℝ) :
    ∃ μ : FiniteMixture, ∃ J : Disorder N μ.maxDegree,
      fieldOfMixture μ J=fun x => fieldOfMixture μ₀ J₀ x+
        p.eval (inner ℝ v₁ x)*q.eval (inner ℝ v₂ x)*regressionCorrection μ₀ Q u G Hq Kq h k x := by
  have hdeg : 2 ≤ μ₀.maxDegree :=
    μ₀.degree_ge_two (Finset.max'_mem μ₀.coeff.support μ₀.support_nonempty)
  obtain ⟨μ,J,hJ⟩ := original_plus_polynomial_cutoff_exists_physical_mixture hN hdeg μ₀ J₀
    (le_refl _) (regressionCorrectionAtom μ₀ Q u G Hq Kq h k) v₁ v₂ p q
  refine ⟨μ,J,?_⟩
  rw [hJ]
  funext x
  rw [regressionCorrection_atom_sum]

end SlowEquilibration.ConditionedEntrance.TensorPolynomial
