module
public import QuantitativePaper.VectorTerminalLinear
public import QuantitativePaper.FiniteSoftmaxJets
public import QuantitativePaper.FiniteJetBounds

@[expose] public section

/-! Actual joint terminal smoothness and globally bounded positive-order jets,
proved for the physical SK terminal Hamiltonian. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper

theorem vectorTerminalPotential_eq_finiteLinearSoftmax (n : ℕ) (β t : ℝ) :
    (fun p : VectorParameter n => vectorTerminalPotential n β t p.1 p.2) =
      finiteLinearSoftmax (vectorTerminalLinear n β t) := by
  funext p
  unfold vectorTerminalPotential terminalPotential terminalPartition finiteLinearSoftmax finiteLinearPartition
  simp_rw [vectorTerminalLinear_apply]

theorem contDiff_vectorTerminalPotential_joint (n : ℕ) (β t : ℝ) (N : ℕ) :
    ContDiff ℝ N (fun p : VectorParameter n => vectorTerminalPotential n β t p.1 p.2) := by
  rw [vectorTerminalPotential_eq_finiteLinearSoftmax]
  exact contDiff_finiteLinearSoftmax _ N

theorem exists_vectorTerminalPotential_joint_jet_bound (n : ℕ) (β t : ℝ) (N : ℕ) :
    ∃ K : ℝ,1 ≤ K ∧ ∀ j,1 ≤ j → j ≤ N → ∀ x : VectorParameter n,
      ‖iteratedFDeriv ℝ j (fun p => vectorTerminalPotential n β t p.1 p.2) x‖ ≤ K^j := by
  let l := vectorTerminalLinear n β t
  let B := fun j => (j.factorial : ℝ)*logJetCoefficient j*(finitePartitionPowerBound l N)^j
  refine ⟨finiteJetPowerBound B N,finiteJetPowerBound_ge_one B N,?_⟩
  intro j hj0 hj x
  rw [vectorTerminalPotential_eq_finiteLinearSoftmax]
  exact (norm_iteratedFDeriv_finiteLinearSoftmax_le l N j hj0 hj x).trans
    (finite_jet_bound_le_power B N j hj0 hj)

end QuantitativePaper
