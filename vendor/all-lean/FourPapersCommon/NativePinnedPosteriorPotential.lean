module

public import FourPapersCommon.NativePinnedDriverHistory
public import FourPapersCommon.FiniteStateCascadeConvexity
public import QuantitativePaper.VectorPosteriorCoercivity

@[expose] public section

/-! The actual spin-pinned Gaussian potential for a finite-state hierarchy.
The chronology is reversed relative to the Gaussian recursion. Telescoping
its true transition log density gives nonnegative continuation coefficients,
and hence a native Gaussian Hessian lower bound of one. -/
noncomputable section
open MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup Set
open scoped BigOperators ContDiff
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 400000
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {d : ℕ}

def nativePinnedForwardMass (a : ℕ → ℝ) (N i : ℕ) : ℝ := a (N-1-i)

def nativePinnedHistoryPotential (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ)
    (z : NativePinnedDriverSpace N d) : ℝ :=
  finiteStateGaussianTerminalCascade V a L (N-i) (nativePinnedDriverStateLinear L N i z)

def nativePinnedTerminalLinear (L : ℕ → Field d →L[ℝ] FiniteStateField S)
    (N : ℕ) (σ : S) : NativePinnedDriverSpace N d →L[ℝ] ℝ :=
  (EuclideanSpace.proj σ).comp (nativePinnedDriverStateLinear L N N)

def nativePinnedPosteriorCorrection (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N : ℕ) (σ : S)
    (z : NativePinnedDriverSpace N d) : ℝ :=
  -V σ-nativePinnedTerminalLinear L N σ z+
    nativePinnedForwardMass a N 0*nativePinnedHistoryPotential V a L N 0 z+
    (∑i∈Finset.range N,
      (nativePinnedForwardMass a N (i+1)-nativePinnedForwardMass a N i)*
        nativePinnedHistoryPotential V a L N (i+1) z)+
    (1-nativePinnedForwardMass a N N)*nativePinnedHistoryPotential V a L N N z

def nativePinnedPosteriorPotential (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N : ℕ) (σ : S)
    (z : NativePinnedDriverSpace N d) : ℝ :=
  standardGaussianPotential z+nativePinnedPosteriorCorrection V a L N σ z

theorem nativePinnedForwardMass_monotone (a : ℕ → ℝ) (ha : Antitone a) (N : ℕ) :
    Monotone (nativePinnedForwardMass a N) := by
  intro i j hij
  exact ha (by omega)

theorem contDiff_nativePinnedHistoryPotential (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ) :
    ContDiff ℝ ∞ (nativePinnedHistoryPotential V a L N i) :=
  (contDiff_finiteStateGaussianTerminalCascade V a ha L (N-i)).comp
    (nativePinnedDriverStateLinear L N i).contDiff

theorem convexOn_nativePinnedHistoryPotential (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ) :
    ConvexOn ℝ univ (nativePinnedHistoryPotential V a L N i) :=
  (convexOn_finiteStateGaussianTerminalCascade V a ha L (N-i)).comp_linearMap
    (nativePinnedDriverStateLinear L N i).toLinearMap

theorem contDiff_nativePinnedPosteriorCorrection (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S)
    (N : ℕ) (σ : S) : ContDiff ℝ ∞ (nativePinnedPosteriorCorrection V a L N σ) := by
  unfold nativePinnedPosteriorCorrection
  exact ((((contDiff_const.sub (nativePinnedTerminalLinear L N σ).contDiff).add
    (contDiff_const.mul (contDiff_nativePinnedHistoryPotential V a ha L N 0))).add
    (ContDiff.sum fun i _ => contDiff_const.mul
      (contDiff_nativePinnedHistoryPotential V a ha L N (i+1)))).add
    (contDiff_const.mul (contDiff_nativePinnedHistoryPotential V a ha L N N)))

theorem contDiff_nativePinnedPosteriorPotential (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S)
    (N : ℕ) (σ : S) : ContDiff ℝ ∞ (nativePinnedPosteriorPotential V a L N σ) :=
  contDiff_standardGaussianPotential.add (contDiff_nativePinnedPosteriorCorrection V a ha L N σ)

theorem convexOn_nativePinnedPosteriorCorrection (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : a 0 ≤ 1) (hanti : Antitone a)
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N : ℕ) (σ : S) :
    ConvexOn ℝ univ (nativePinnedPosteriorCorrection V a L N σ) := by
  have hm := nativePinnedForwardMass_monotone a hanti N
  have hlin : ConvexOn ℝ univ (fun z : NativePinnedDriverSpace N d =>
      -V σ-nativePinnedTerminalLinear L N σ z) := by
    have hh := (-(nativePinnedTerminalLinear L N σ).toLinearMap).convexOn (convex_univ (𝕜:=ℝ))
    convert hh.add_const (-V σ) using 1
    funext z
    change -V σ-nativePinnedTerminalLinear L N σ z =
      -nativePinnedTerminalLinear L N σ z+(-V σ)
    ring
  have h0 := (convexOn_nativePinnedHistoryPotential V a ha L N 0).smul (ha (N-1))
  have hs := convexOn_finite_sum_univ (Finset.range N)
    (fun i z => (nativePinnedForwardMass a N (i+1)-nativePinnedForwardMass a N i)*
      nativePinnedHistoryPotential V a L N (i+1) z)
    (fun i _ => by
      simpa only [smul_eq_mul] using (convexOn_nativePinnedHistoryPotential V a ha L N (i+1)).smul
        (sub_nonneg.mpr (hm (Nat.le_succ i))))
  have ht := (convexOn_nativePinnedHistoryPotential V a ha L N N).smul (sub_nonneg.mpr ha1)
  convert ((hlin.add h0).add hs).add ht using 1
  funext z
  simp only [nativePinnedPosteriorCorrection,nativePinnedForwardMass,Nat.sub_zero,
    show N-1-N=0 by omega,smul_eq_mul,Pi.add_apply]

theorem nativePinnedPosteriorPotential_hessian_lower (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha1 : a 0 ≤ 1) (hanti : Antitone a)
    (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N : ℕ) (σ : S)
    (z w : NativePinnedDriverSpace N d) :
    ‖w‖^2 ≤ directionalHessian (nativePinnedPosteriorPotential V a L N σ) z w := by
  unfold nativePinnedPosteriorPotential
  rw [directionalHessian_add _ _ (contDiff_standardGaussianPotential.of_le (by simp))
      ((contDiff_nativePinnedPosteriorCorrection V a ha L N σ).of_le (by simp)),
    directionalHessian_standardGaussianPotential]
  exact le_add_of_nonneg_right (directionalHessian_nonneg_of_convex _
    ((contDiff_nativePinnedPosteriorCorrection V a ha L N σ).of_le (by simp))
    (convexOn_nativePinnedPosteriorCorrection V a ha ha1 hanti L N σ) z w)

end FourPapersCommon
