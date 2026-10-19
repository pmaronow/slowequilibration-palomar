module

public import FourPapersCommon.NativePinnedPosteriorPotential
public import QuantitativePaper.VectorPosteriorJets

@[expose] public section

/-! Global positive-order jets of the actual independent-layer posterior.
The bounds follow from its finite Gaussian recursion. -/
noncomputable section
open Set QuantitativePaper
open scoped BigOperators ContDiff
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 400000
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {d : ℕ}

theorem boundedPositiveJets_nativePinnedContinuation (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S) (j : ℕ) :
    BoundedPositiveJets (finiteStateGaussianTerminalCascade V a L j) := by
  refine ⟨contDiff_finiteStateGaussianTerminalCascade V a ha L j,?_⟩
  intro r hr
  obtain ⟨_,C,hC,hb⟩ := finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r j
  exact ⟨C^r,pow_nonneg (zero_le_one.trans hC) _,fun H => hb r hr le_rfl H⟩

theorem boundedPositiveJets_nativePinnedHistoryPotential (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S) (N i : ℕ) :
    BoundedPositiveJets (nativePinnedHistoryPotential V a L N i) :=
  (boundedPositiveJets_nativePinnedContinuation V a ha L (N-i)).comp_linear
    (nativePinnedDriverStateLinear L N i)

theorem boundedPositiveJets_nativePinnedPosteriorCorrection (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S)
    (N : ℕ) (σ : S) : BoundedPositiveJets (nativePinnedPosteriorCorrection V a L N σ) := by
  have hlin : BoundedPositiveJets (fun z : NativePinnedDriverSpace N d =>
      -V σ-nativePinnedTerminalLinear L N σ z) := by
    simpa only [sub_eq_add_neg] using (boundedPositiveJets_const (-V σ)).add
      (boundedPositiveJets_linear (nativePinnedTerminalLinear L N σ)).neg
  have h0 := (boundedPositiveJets_nativePinnedHistoryPotential V a ha L N 0).const_mul
    (nativePinnedForwardMass a N 0)
  have hs := boundedPositiveJets_finite_sum (Finset.range N)
    (fun i z => (nativePinnedForwardMass a N (i+1)-nativePinnedForwardMass a N i)*
      nativePinnedHistoryPotential V a L N (i+1) z)
    (fun i _ => (boundedPositiveJets_nativePinnedHistoryPotential V a ha L N (i+1)).const_mul _)
  have ht := (boundedPositiveJets_nativePinnedHistoryPotential V a ha L N N).const_mul
    (1-nativePinnedForwardMass a N N)
  exact ((hlin.add h0).add hs).add ht

theorem exists_nativePinnedPosteriorPotential_jet_bound (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field d →L[ℝ] FiniteStateField S)
    (N : ℕ) (σ : S) {j : ℕ} (hj : 3 ≤ j) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ z : NativePinnedDriverSpace N d,
      ‖iteratedFDeriv ℝ j (nativePinnedPosteriorPotential V a L N σ) z‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := (boundedPositiveJets_nativePinnedPosteriorCorrection V a ha L N σ).2 j
    (by omega)
  refine ⟨B,hB,fun z => ?_⟩
  unfold nativePinnedPosteriorPotential
  change ‖iteratedFDeriv ℝ j (standardGaussianPotential+nativePinnedPosteriorCorrection V a L N σ) z‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_standardGaussianPotential.of_le (by simp)).contDiffAt
    ((boundedPositiveJets_nativePinnedPosteriorCorrection V a ha L N σ).1.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (by
    rw [norm_iteratedFDeriv_standardGaussianPotential_eq_zero hj,zero_add]
    exact hb z)

end FourPapersCommon
