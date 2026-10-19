module
public import QuantitativePaper.LogJetBounds

@[expose] public section

/-! Converting finitely many genuine global derivative bounds to a single
positive constant in the power form needed by the composition estimates. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativePaper

def finiteJetPowerBound (B : ℕ → ℝ) (N : ℕ) : ℝ := max 1 (∑ j ∈ Finset.range (N+1),|B j|)

theorem finiteJetPowerBound_ge_one (B : ℕ → ℝ) (N : ℕ) :
    1 ≤ finiteJetPowerBound B N := le_max_left _ _

theorem finite_jet_bound_le_power (B : ℕ → ℝ) (N j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ N) :
    B j ≤ (finiteJetPowerBound B N)^j := by
  have hh : |B j| ≤ ∑ i ∈ Finset.range (N+1),|B i| :=
    Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  exact (le_abs_self _).trans (hh.trans ((le_max_right _ _).trans
    (le_self_pow₀ (finiteJetPowerBound_ge_one B N) (by omega))))

end QuantitativePaper
