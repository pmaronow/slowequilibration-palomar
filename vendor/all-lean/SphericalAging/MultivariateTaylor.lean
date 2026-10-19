module

public import SphericalAging.SphereGenerator
public import StochasticCalculus.ItoFormulaPartition
public import Mathlib.Analysis.Calculus.Taylor

public section

/-! Genuine second-order Taylor control for the finite-dimensional state.
The remainder modulus is uniform on each compact closed ball and therefore
can be used along every continuous physical sphere path. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MultivariateTaylor
open HardSphereDynamics LocalSDE
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] abbrev Hessian (f : State N → ℝ) (x : State N) := fderiv ℝ (fderiv ℝ f) x

@[expose] def remainder (f : State N → ℝ) (x y : State N) : ℝ :=
  f y-f x-fderiv ℝ f x (y-x)-(1/2 : ℝ)*Hessian f x (y-x) (y-x)

lemma hessian_continuous {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Hessian f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)

/-- Ordinary one-variable Taylor along the actual line segment gives the
exact multivariate Hessian contraction at an intermediate point. -/
theorem line_taylor {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (x y : State N) :
    ∃ r : ℝ,r ∈ Ioo 0 1 ∧
      f y-f x-fderiv ℝ f x (y-x) = (1/2 : ℝ)*Hessian f (x+r • (y-x)) (y-x) (y-x) := by
  let h : State N := y-x
  let g : ℝ → ℝ := fun r => f (x+r • h)
  have hgc : ContDiff ℝ 2 g := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hline (r : ℝ) : HasDerivAt (fun r : ℝ => x+r • h) h r := by
    convert (hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const h) using 1
    · funext s
      rfl
    · simp
  have hd (r : ℝ) : HasDerivAt g (fderiv ℝ f (x+r • h) h) r :=
    ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt r (hline r)
  have hderiv : deriv g = fun r => fderiv ℝ f (x+r • h) h := funext (fun r => (hd r).deriv)
  have hdd (r : ℝ) : HasDerivAt (fun r => fderiv ℝ f (x+r • h) h)
      (Hessian f (x+r • h) h h) r := by
    have hh := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt r (hline r)
    simpa only [Hessian,map_zero,add_zero,Function.comp_def] using
      hh.clm_apply (hasDerivAt_const r h)
  have hsecond : deriv (deriv g) = fun r => Hessian f (x+r • h) h h := by
    rw [hderiv]
    exact funext (fun r => (hdd r).deriv)
  obtain ⟨r,hr,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    (by norm_num : (0 : ℝ) ≠ 1) hgc.contDiffOn
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hfirst : iteratedDerivWithin 1 g (uIcc (0 : ℝ) 1) 0 = deriv g 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hgc.contDiffAt.of_le (by norm_num)) left_mem_uIcc]
    rw [show 1 = 0+1 by rfl,iteratedDeriv_succ]
    simp only [iteratedDeriv_zero]
  have h2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,show 1 = 0+1 by rfl,iteratedDeriv_succ]
    simp only [iteratedDeriv_zero]
  rw [taylorWithinEval_succ,taylor_within_zero_eval,hfirst,h2,hsecond,hderiv] at he
  refine ⟨r,?_,?_⟩
  · simpa only [uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using hr
  · norm_num only [Nat.factorial] at he
    simp only [g,h,zero_smul,add_zero,one_smul,add_sub_cancel,sub_zero,
      one_pow,one_div,one_mul,mul_one,smul_eq_mul] at he
    linarith only [he]

/-- Actual C² regularity makes the second-order remainder uniformly small
on every compact state ball, with no third-derivative assumption. -/
theorem uniform_remainder_closedBall {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (R : ℝ) : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧
      ∀ x ∈ Metric.closedBall (0 : State N) R,∀ y ∈ Metric.closedBall (0 : State N) R,
        ‖y-x‖ < δ → ‖remainder f x y‖ ≤ ε*‖y-x‖^2 := by
  have huc := (isCompact_closedBall (0 : State N) R).uniformContinuousOn_of_continuous
    (hessian_continuous hf).continuousOn
  intro ε hε
  obtain ⟨δ,hδ,hm⟩ := (Metric.uniformContinuousOn_iff
    (α := State N) (β := State N →L[ℝ] State N →L[ℝ] ℝ)).mp huc (2*ε) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy
  obtain ⟨r,hr,he⟩ := line_taylor hf x y
  have hz : x+r • (y-x) ∈ Metric.closedBall (0 : State N) R := by
    exact (convex_closedBall (0 : State N) R).add_smul_sub_mem hx hy ⟨hr.1.le,hr.2.le⟩
  have hdist : dist (x+r • (y-x)) x < δ := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr.2.le).trans_lt hxy
  have hHlt : ‖Hessian f (x+r • (y-x))-Hessian f x‖ < 2*ε := by
    have hh := hm _ hz _ hx hdist
    have heq (u v : State N →L[ℝ] State N →L[ℝ] ℝ) : dist u v = ‖u-v‖ := dist_eq_norm u v
    rw [heq] at hh
    exact hh
  have hH := hHlt.le
  unfold remainder
  rw [he]
  rw [show (1/2 : ℝ)*Hessian f (x+r • (y-x)) (y-x) (y-x)-
      (1/2 : ℝ)*Hessian f x (y-x) (y-x) =
        (1/2 : ℝ)*(Hessian f (x+r • (y-x))-Hessian f x) (y-x) (y-x) by
      simp only [ContinuousLinearMap.sub_apply];ring]
  calc
    _ = (1/2 : ℝ)*‖(Hessian f (x+r • (y-x))-Hessian f x) (y-x) (y-x)‖ := by
      rw [norm_mul,Real.norm_of_nonneg (by norm_num)]
    _ ≤ (1/2 : ℝ)*((2*ε)*‖y-x‖*‖y-x‖) := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (norm_nonneg _))
    _ = _ := by ring

end SphericalAging.MultivariateTaylor
