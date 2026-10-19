module
public import FourPapersCommon.FiniteStateCascadeExpectations
public import QuantitativePaper.SmoothGaussianStep
public import QuantitativePaper.VectorTerminalSmooth
public import QuantitativePaper.VectorSharpMassBounds

@[expose] public section

/-! Actual finite cascade smoothness for arbitrary fixed terminal offsets
and arbitrary Gaussian maps. These preliminary bounds may depend on depth;
the normalized posterior is used separately to remove that dependence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff NNReal
namespace FourPapersCommon
open SpinGlass.AT QuantitativePaper OverlapPaper
variable {S : Type} [Fintype S] [Nonempty S] {n : ℕ}
set_option maxHeartbeats 1000000

theorem gtStateLogPartition_eq_translated_softmax (V : S → ℝ) :
    gtStateLogPartition V=fun H : FiniteStateField S=>
      finiteLinearSoftmax (fun σ=>EuclideanSpace.proj σ) (H+WithLp.toLp 2 V) := by
  funext H
  unfold gtStateLogPartition gtStatePartition finiteLinearSoftmax finiteLinearPartition
  rfl

theorem gtStateLogPartition_smooth_bounded_jets (V : S → ℝ) (N : ℕ) :
    ContDiff ℝ N (gtStateLogPartition V) ∧
    ∃ K : ℝ,1 ≤ K ∧ ∀ i,1 ≤ i → i ≤ N → ∀ H : FiniteStateField S,
      ‖iteratedFDeriv ℝ i (gtStateLogPartition V) H‖ ≤ K^i := by
  let l : S → FiniteStateField S →L[ℝ]ℝ := fun σ=>EuclideanSpace.proj σ
  let B := fun i=>(i.factorial : ℝ)*logJetCoefficient i*(finitePartitionPowerBound l N)^i
  rw [gtStateLogPartition_eq_translated_softmax]
  refine ⟨(contDiff_finiteLinearSoftmax l N).comp (contDiff_id.add contDiff_const),
    finiteJetPowerBound B N,finiteJetPowerBound_ge_one B N,?_⟩
  intro i hi0 hi H
  rw [iteratedFDeriv_comp_add_right]
  exact (norm_iteratedFDeriv_finiteLinearSoftmax_le l N i hi0 hi _).trans
    (finite_jet_bound_le_power B N i hi0 hi)

theorem finiteStateGaussianTerminalCascade_smooth_bounded_jets
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ i,0 ≤ a i)
    (L : ℕ → FiniteStateGaussianInput (Fin n) →L[ℝ]FiniteStateField S) (N j : ℕ) :
    ContDiff ℝ N (finiteStateGaussianTerminalCascade V a L j) ∧
    ∃ K : ℝ,1 ≤ K ∧ ∀ i,1 ≤ i → i ≤ N → ∀ H : FiniteStateField S,
      ‖iteratedFDeriv ℝ i (finiteStateGaussianTerminalCascade V a L j) H‖ ≤ K^i := by
  induction j with
  | zero=>exact gtStateLogPartition_smooth_bounded_jets V N
  | succ j ih=>
    obtain ⟨hf,K,hK,hB⟩:=ih
    have he : finiteStateGaussianTerminalCascade V a L (j+1)=
        gaussianShiftColeHopf (L j) (a j) (finiteStateGaussianTerminalCascade V a L j) := by
      funext H
      unfold finiteStateGaussianTerminalCascade
      rw [finiteStateGaussianCascade]
      unfold finiteStateGaussianStep sourceLogAverage gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
      rw [fieldGaussian_eq_stdGaussian]
    rw [he]
    exact gaussianShiftColeHopf_smooth_bounded_jets N _ hf 1
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L j) K hK hB (L j) (a j)

theorem contDiff_finiteStateGaussianTerminalCascade
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ i,0 ≤ a i)
    (L : ℕ → FiniteStateGaussianInput (Fin n) →L[ℝ]FiniteStateField S) (j : ℕ) :
    ContDiff ℝ ∞ (finiteStateGaussianTerminalCascade V a L j) :=
  contDiff_infty.mpr fun N=>(finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L N j).1

end FourPapersCommon
