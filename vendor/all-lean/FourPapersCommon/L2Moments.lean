module
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Actual expectations, variances, and covariances are continuous in L². -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace FourPapersCommon
variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def l2Expectation : Lp E 2 P →L[ℝ] E :=
  (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip).lpPairing P 2 2).flip
    (Lp.const 2 P (1:ℝ))

theorem l2Expectation_eq_integral (X : Lp E 2 P) :
    l2Expectation X = ∫ω,X ω ∂P := by
  rw [l2Expectation,ContinuousLinearMap.flip_apply,ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 P (1:ℝ)] with ω hω
  simp [hω,ContinuousLinearMap.flip_apply]

theorem continuous_integral_l2 : Continuous (fun X : Lp E 2 P => ∫ω,X ω ∂P) := by
  convert (l2Expectation (E:=E) (P:=P)).continuous using 1
  funext X
  exact (l2Expectation_eq_integral X).symm

theorem continuous_covariance_l2 :
    Continuous (fun X : Lp ℝ 2 P × Lp ℝ 2 P => cov[X.1,X.2;P]) := by
  have he (X : Lp ℝ 2 P × Lp ℝ 2 P) :
      cov[X.1,X.2;P] = ⟪X.1,X.2⟫-(∫ω,X.1 ω ∂P)*(∫ω,X.2 ω ∂P) := by
    rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial,mul_comm,Pi.mul_apply]
  simp_rw [he]
  exact (continuous_fst.inner continuous_snd).sub
    ((continuous_integral_l2.comp continuous_fst).mul
      (continuous_integral_l2.comp continuous_snd))

theorem continuous_variance_l2 : Continuous (fun X : Lp ℝ 2 P => Var[X;P]) := by
  have he (X : Lp ℝ 2 P) : Var[X;P]=cov[X,X;P] :=
    (covariance_self (Lp.memLp X).aemeasurable).symm
  simp_rw [he]
  exact continuous_covariance_l2.comp (continuous_id.prodMk continuous_id)

end FourPapersCommon
