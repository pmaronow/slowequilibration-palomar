module

public import FourPapersCommon.FiniteStateCascadePosteriorLogDensity
public import FourPapersCommon.FiniteGaussianBlockLaw
public import QuantitativeFollowup.AnisotropicHistoryLinear

@[expose] public section

/-! The actual chronological Gaussian history as a continuous linear map of
all independent layer drivers. No invertibility of any covariance increment
is required. This includes matrix and spin-field layers with independent clocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory QuantitativePaper
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [Fintype S] {d : ℕ}

abbrev NativePinnedDriverSpace (N d : ℕ) := EuclideanSpace ℝ (Fin N × Fin d)

def nativePinnedDriverCoordinates (N d : ℕ) :
    NativePinnedDriverSpace N d →L[ℝ] (Fin N → Field d) :=
  ContinuousLinearMap.pi fun i =>
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.pi fun r => EuclideanSpace.proj (i,r))

theorem nativePinnedDriverCoordinates_apply (N d : ℕ) (z : NativePinnedDriverSpace N d) :
    nativePinnedDriverCoordinates N d z = gaussianBlockCurry z := rfl

def nativePinnedHistoryUpdateLinear
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ) :
    (FiniteStateField S × Field d) →L[ℝ] FiniteStateField S :=
  ContinuousLinearMap.fst ℝ (FiniteStateField S) (Field d)+
    (L (N-1-i)).comp (ContinuousLinearMap.snd ℝ (FiniteStateField S) (Field d))

def nativePinnedDriverHistoryLinear
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N : ℕ) :
    NativePinnedDriverSpace N d →L[ℝ] (Fin (N+1) → FiniteStateField S) :=
  let history : (FiniteStateField S × (Fin N → Field d)) →L[ℝ]
      (Fin (N+1) → FiniteStateField S) :=
    independentHistoryLinear (State := FiniteStateField S) (Noise := Field d)
      (nativePinnedHistoryUpdateLinear L N) N
  let initial : NativePinnedDriverSpace N d →L[ℝ]
      (FiniteStateField S × (Fin N → Field d)) :=
    (0 : NativePinnedDriverSpace N d →L[ℝ] FiniteStateField S).prod
      (nativePinnedDriverCoordinates N d)
  history.comp initial

theorem nativePinnedDriverHistoryLinear_apply
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N : ℕ)
    (z : NativePinnedDriverSpace N d) :
    nativePinnedDriverHistoryLinear L N z = cascadePosteriorHistory L N 0 (gaussianBlockCurry z) := by
  unfold nativePinnedDriverHistoryLinear
  rw [ContinuousLinearMap.comp_apply,independentHistoryLinear_apply]
  change independentHistory (fun i x z => nativePinnedHistoryUpdateLinear L N i (x,z))
    N ((0:FiniteStateField S),nativePinnedDriverCoordinates N d z) = _
  rw [nativePinnedDriverCoordinates_apply]
  rfl

def nativePinnedDriverStateLinear
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ) :
    NativePinnedDriverSpace N d →L[ℝ] FiniteStateField S :=
  (ContinuousLinearMap.proj (Fin.ofNat (N+1) i)).comp (nativePinnedDriverHistoryLinear L N)

theorem nativePinnedDriverStateLinear_apply
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ)
    (z : NativePinnedDriverSpace N d) :
    nativePinnedDriverStateLinear L N i z =
      historyExtended (cascadePosteriorHistory L N 0 (gaussianBlockCurry z)) i := by
  rw [nativePinnedDriverStateLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,nativePinnedDriverHistoryLinear_apply]
  rfl

theorem nativePinnedDriverCoordinates_gaussian_law (N d : ℕ) :
    (stdGaussian (NativePinnedDriverSpace N d)).map (nativePinnedDriverCoordinates N d) =
      Measure.pi (fun _ : Fin N => stdGaussian (Field d)) :=
  stdGaussian_map_gaussianBlockCurry

end FourPapersCommon
