module
public import QuantitativeFollowup.PosteriorQuadratic
public import QuantitativeFollowup.InverseFamily

@[expose] public section

/-! The posterior Schur estimate with a literal constructed inverse of
`I+∑ wᵢ Aᵢ`. This is the exact finite-feature inverse-Hessian algebra,
separate from the model-specific identification of the posterior law. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup

def posteriorFeatureHessian {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (A : ι → E →L[ℝ] E) (w : ι → ℝ) : E →L[ℝ] E := 1+∑ i,w i • A i

def posteriorFeatureShift {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (A : ι → E →L[ℝ] E) (w k : ι → ℝ) (ζ : ι → E) : E :=
  ∑ i,(w i*k i) • A i (ζ i)

theorem posteriorFeatureHessian_coercive {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (A : ι → E →L[ℝ] E) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    (hA : ∀ i x,0 ≤ inner ℝ x (A i x)) (z : E) :
    ‖z‖^2 ≤ inner ℝ z (posteriorFeatureHessian A w z) := by
  classical
  have hs : 0 ≤ ∑ i,w i*inner ℝ z (A i z) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hA i z))
  simpa only [posteriorFeatureHessian,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,inner_add_right,inner_sum,real_inner_smul_right,
    real_inner_self_eq_norm_sq] using le_add_of_nonneg_right hs

theorem posteriorFeatureHessian_isUnit {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
    (A : ι → E →L[ℝ] E) (w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    (hA : ∀ i x,0 ≤ inner ℝ x (A i x)) : IsUnit (posteriorFeatureHessian A w) := by
  apply isUnit_of_coercive _ 1 (by norm_num)
  intro z
  simpa only [one_mul] using posteriorFeatureHessian_coercive A w hw hA z

theorem posteriorFeature_inverse_energy_le {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
    (A : ι → E →L[ℝ] E) (w k : ι → ℝ) (ζ : ι → E)
    (hw : ∀ i,0 ≤ w i) (hA : ∀ i x,0 ≤ inner ℝ x (A i x))
    (hAs : ∀ i x y,inner ℝ x (A i y)=inner ℝ y (A i x)) :
    inner ℝ (posteriorFeatureShift A w k ζ)
      (Ring.inverse (posteriorFeatureHessian A w) (posteriorFeatureShift A w k ζ)) ≤
      ∑ i,w i*(k i)^2*inner ℝ (ζ i) (A i (ζ i)) := by
  let u := Ring.inverse (posteriorFeatureHessian A w) (posteriorFeatureShift A w k ζ)
  have hu : posteriorFeatureHessian A w u=posteriorFeatureShift A w k ζ := by
    have hh := congrArg (fun C : E →L[ℝ] E => C (posteriorFeatureShift A w k ζ))
      (Ring.mul_inverse_cancel (posteriorFeatureHessian A w)
        (posteriorFeatureHessian_isUnit A w hw hA))
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply,u] using hh
  have hsolve : u+∑ i,w i • A i u=∑ i,(w i*k i) • A i (ζ i) := by
    simpa only [posteriorFeatureHessian,posteriorFeatureShift,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply] using hu
  have hh := posterior_shift_quadratic_bound (fun i => (A i).toLinearMap) w k ζ u
    hw hA hAs hsolve
  rw [real_inner_comm u (posteriorFeatureShift A w k ζ)]
  exact hh

end QuantitativeFollowup
