module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The inverse-Hessian algebra in the posterior argument. This result
does not assume the desired quadratic bound. Positive semidefiniteness
and symmetry of the constituent Hessians imply it by completing squares.
The analytic Brascamp--Lieb variance inequality is a separate obligation. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace QuantitativeFollowup

theorem posterior_shift_quadratic_bound {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (A : ι → E →ₗ[ℝ] E) (w k : ι → ℝ) (ζ : ι → E) (u : E)
    (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i x, 0 ≤ (inner ℝ (x) ( A i x)))
    (hAs : ∀ i x y, (inner ℝ (x) ( A i y)) = (inner ℝ (y) ( A i x)))
    (hsolve : u + ∑ i, w i • A i u = ∑ i, (w i*k i) • A i (ζ i)) :
    inner ℝ u (∑ i, (w i*k i) • A i (ζ i)) ≤
      ∑ i, w i*(k i)^2*(inner ℝ (ζ i) (A i (ζ i))) := by
  classical
  have hp (i : ι) : 0 ≤ w i*((k i)^2*(inner ℝ (ζ i) (A i (ζ i)))-
      2*k i*(inner ℝ (u) (A i (ζ i)))+(inner ℝ (u) (A i u))) := by
    have hh := mul_nonneg (hw i) (hA i (k i • ζ i-u))
    simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,
      real_inner_smul_left,real_inner_smul_right] at hh
    rw [hAs i (ζ i) u] at hh
    nlinarith
  have hs := Finset.sum_nonneg (fun i (_hi : i∈Finset.univ) => hp i)
  have hi : (inner ℝ (u) (u)) + ∑ i,w i*(inner ℝ (u) (A i u)) =
      ∑ i,w i*k i*(inner ℝ (u) (A i (ζ i))) := by
    have hh := congrArg (fun x : E => (inner ℝ (u) (x))) hsolve
    simpa only [inner_add_right,inner_sum,real_inner_smul_right] using hh
  have hsimp : (∑ i,w i*((k i)^2*(inner ℝ (ζ i) (A i (ζ i)))-
      2*k i*(inner ℝ (u) (A i (ζ i)))+(inner ℝ (u) (A i u)))) =
      (∑ i,w i*(k i)^2*(inner ℝ (ζ i) (A i (ζ i))))-
        2*(∑ i,w i*k i*(inner ℝ (u) (A i (ζ i))))+
          (∑ i,w i*(inner ℝ (u) (A i u))) := by
    simp_rw [mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 2 <;> apply Finset.sum_congr rfl <;> intro i _hi <;> ring
  rw [hsimp] at hs
  simp only [inner_sum,real_inner_smul_right]
  have hu : 0 ≤ (inner ℝ (u) (u)) := real_inner_self_nonneg
  linarith

end QuantitativeFollowup
