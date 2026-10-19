module
public import QuantitativeFollowup.AnisotropicGaussianCoordinates

@[expose] public section

/-! The actual anisotropic chronological history is a continuous linear
map of all independent Gaussian coordinates, including zero variances. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000

def anisotropicEuclideanCoordinatesLinear (n k : ℕ) :
    AnisotropicGaussianSpace n k →L[ℝ]AnisotropicGaussianCoordinates n k :=
  ((((PiLp.continuousLinearEquiv 2 ℝ (fun _ : AnisotropicCouplingIndex n => ℝ)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (.inl i))).prod
    (ContinuousLinearMap.pi fun j : Fin (k+2) =>
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (.inr (j,i)))))

@[simp] theorem anisotropicEuclideanCoordinatesLinear_apply (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanCoordinatesLinear n k z=anisotropicEuclideanCoordinates n k z := rfl

def anisotropicCoordinateUpdateLinear (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : ℕ) :
    (AnisotropicParameter n×Field n)→L[ℝ]AnisotropicParameter n :=
  ContinuousLinearMap.fst ℝ (AnisotropicParameter n) (Field n)+
    (anisotropicSchemeInput D s (k+1-i)).comp (ContinuousLinearMap.snd ℝ (AnisotropicParameter n) (Field n))

@[simp] theorem anisotropicCoordinateUpdateLinear_apply (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (P : AnisotropicParameter n) (z : Field n) :
    anisotropicCoordinateUpdateLinear D s i (P,z)=anisotropicCoordinateUpdate D s i P z := rfl

def anisotropicCoordinateInitialLinear (n k : ℕ) : AnisotropicGaussianCoordinates n k→L[ℝ]
    (AnisotropicParameter n×(Fin (k+2)→Field n)) :=
  ((anisotropicDisorderInjection n).comp
    (ContinuousLinearMap.fst ℝ (AnisotropicDisorder n) (Fin (k+2)→Field n))).prod
      (ContinuousLinearMap.snd ℝ (AnisotropicDisorder n) (Fin (k+2)→Field n))

def anisotropicCoordinateHistoryLinear (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    AnisotropicGaussianCoordinates n k→L[ℝ](Fin (k+3)→AnisotropicParameter n) :=
  (independentHistoryLinear (anisotropicCoordinateUpdateLinear D s) (k+2)).comp
    (anisotropicCoordinateInitialLinear n k)

theorem anisotropicCoordinateHistoryLinear_apply (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p : AnisotropicGaussianCoordinates n k) :
    anisotropicCoordinateHistoryLinear D s p=anisotropicCoordinateHistory D s p := by
  unfold anisotropicCoordinateHistoryLinear
  rw [ContinuousLinearMap.comp_apply,independentHistoryLinear_apply]
  simp_rw [anisotropicCoordinateUpdateLinear_apply]
  rfl

def anisotropicEuclideanHistoryLinear (D : AnisotropicSpinModel n) (s : RSBScheme k) :
    AnisotropicGaussianSpace n k→L[ℝ](Fin (k+3)→AnisotropicParameter n) :=
  (anisotropicCoordinateHistoryLinear D s).comp (anisotropicEuclideanCoordinatesLinear n k)

theorem anisotropicEuclideanHistoryLinear_apply (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (z : AnisotropicGaussianSpace n k) : anisotropicEuclideanHistoryLinear D s z =
      anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z) := by
  rw [anisotropicEuclideanHistoryLinear,ContinuousLinearMap.comp_apply,
    anisotropicEuclideanCoordinatesLinear_apply,anisotropicCoordinateHistoryLinear_apply]

def anisotropicEuclideanStateLinear (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : ℕ) :
    AnisotropicGaussianSpace n k→L[ℝ]AnisotropicParameter n :=
  (ContinuousLinearMap.proj (Fin.ofNat (k+3) i)).comp (anisotropicEuclideanHistoryLinear D s)

theorem anisotropicEuclideanStateLinear_apply (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (z : AnisotropicGaussianSpace n k) : anisotropicEuclideanStateLinear D s i z =
      historyExtended (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z)) i := by
  rw [anisotropicEuclideanStateLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,anisotropicEuclideanHistoryLinear_apply]
  rfl

end QuantitativeFollowup
