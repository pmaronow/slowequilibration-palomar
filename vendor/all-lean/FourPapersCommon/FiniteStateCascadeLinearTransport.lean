module
public import FourPapersCommon.FiniteStateCascadeDefinitions

@[expose] public section

/-! Genuine covariance-cascade transport through a continuous linear field
embedding. This moves between spin-field, replica-field and site coordinates
without supplying a distributional or baseline recursion premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace FourPapersCommon
variable {S R I : Type*} [Fintype S] [Fintype R] [Fintype I]

theorem finiteStateGaussianStep_comp_linear
    (T : FiniteStateField R →L[ℝ] FiniteStateField S)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (a : ℝ) (F : FiniteStateField S → ℝ) (H : FiniteStateField R) :
    finiteStateGaussianStep a (T.comp L) F (T H) =
      finiteStateGaussianStep a L (fun y => F (T y)) H := by
  unfold finiteStateGaussianStep
  congr 1
  funext z
  simp only [ContinuousLinearMap.comp_apply, map_add]

theorem finiteStateGaussianCascade_comp_linear
    (T : FiniteStateField R →L[ℝ] FiniteStateField S)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (a : ℕ → ℝ) (F : FiniteStateField S → ℝ) (j : ℕ) (H : FiniteStateField R) :
    finiteStateGaussianCascade a (fun p => T.comp (L p)) F j (T H) =
      finiteStateGaussianCascade a L (fun y => F (T y)) j H := by
  induction j generalizing H with
  | zero => rfl
  | succ j ih =>
    rw [finiteStateGaussianCascade, finiteStateGaussianStep_comp_linear]
    have hf : (fun y => finiteStateGaussianCascade a (fun p => T.comp (L p)) F j (T y)) =
        finiteStateGaussianCascade a L (fun y => F (T y)) j := funext ih
    rw [hf]
    rfl

end FourPapersCommon
