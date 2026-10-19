module
public import QuantitativePaper.VectorEuclideanCoordinates
public import FourPapersCommon.IndependentHistorySmooth

@[expose] public section

/-! Genuine smoothness of every retained Gaussian path coordinate. -/
noncomputable section
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon

theorem contDiff_vectorCoordinateUpdate {n k : ℕ} (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (r : WithTop ℕ∞) :
    ContDiff ℝ r (Function.uncurry (vectorCoordinateUpdate (n := n) s β t i)) := by
  unfold vectorCoordinateUpdate
  split_ifs
  · unfold vectorStateUpdate fieldShift
    fun_prop
  · exact contDiff_fst

theorem contDiff_vectorCoordinateHistory {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (r : WithTop ℕ∞) : ContDiff ℝ r (vectorCoordinateHistory (n := n) s β t) :=
  (contDiff_independentHistory r _ (fun i => contDiff_vectorCoordinateUpdate s β t i r) _).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)

theorem contDiff_flatCompletionCoordinates (n : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (flatCompletionCoordinates n) := by
  unfold flatCompletionCoordinates
  fun_prop

theorem contDiff_flatFieldCoordinates (n k : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (flatFieldCoordinates n k) := by
  unfold flatFieldCoordinates
  apply contDiff_pi.2
  intro j
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.comp
    (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ (j,i))

theorem contDiff_vectorRawGaussianCoordinates (n k : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (vectorRawGaussianCoordinates n k) :=
  ((contDiff_flatCompletionCoordinates n r).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ _)).prodMk
    ((contDiff_flatFieldCoordinates n k r).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ _))

theorem contDiff_vectorEuclideanCoordinates (n k : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (vectorEuclideanCoordinates n k) :=
  (contDiff_vectorRawGaussianCoordinates n k r).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : VectorGaussianIndex n k => ℝ)).contDiff

theorem contDiff_vectorEuclideanHistory {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (r : WithTop ℕ∞) :
    ContDiff ℝ r (vectorCoordinateHistory s β t ∘ vectorEuclideanCoordinates n k) :=
  (contDiff_vectorCoordinateHistory s β t r).comp (contDiff_vectorEuclideanCoordinates n k r)

end QuantitativePaper
