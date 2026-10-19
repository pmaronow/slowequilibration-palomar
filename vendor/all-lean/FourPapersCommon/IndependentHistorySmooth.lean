module
public import FourPapersCommon.IndependentHistory
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Smooth dependence of the actual independent-coordinate path construction. -/
noncomputable section
namespace FourPapersCommon

variable {State Noise : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Noise] [NormedSpace ℝ Noise]

theorem contDiff_independentHistory (r : WithTop ℕ∞)
    (update : ℕ → State → Noise → State)
    (hu : ∀ i,ContDiff ℝ r (Function.uncurry (update i))) (m : ℕ) :
    ContDiff ℝ r (independentHistory update m) := by
  induction m with
  | zero => exact contDiff_pi.2 fun _ => contDiff_fst
  | succ m ih =>
    have hp : ContDiff ℝ r (fun p : State × (Fin (m+1) → Noise) =>
        (p.1,fun i : Fin m => p.2 i.castSucc)) :=
      contDiff_fst.prodMk (contDiff_pi.2 fun i =>
        (contDiff_apply ℝ Noise i.castSucc).comp contDiff_snd)
    have hh := ih.comp hp
    apply contDiff_pi.2
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · convert (hu m).comp (((contDiff_apply ℝ State (Fin.last m)).comp hh).prodMk
        ((contDiff_apply ℝ Noise (Fin.last m)).comp contDiff_snd)) using 1
      funext p
      simp [independentHistory,Function.comp_def]
    · convert (contDiff_apply ℝ State j).comp hh using 1
      funext p
      simp [independentHistory,Function.comp_def]

end FourPapersCommon
