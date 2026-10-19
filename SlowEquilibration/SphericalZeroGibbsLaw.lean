-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGibbs

/-! The common zero-energy Gibbs law is the original uniform sphere law. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.SphericalModel
set_option maxHeartbeats 300000

theorem gibbsLaw_zeroHamiltonian (N : ℕ) :
    gibbsLaw N 0 (fun _ => 0)=sphereLaw N := by
  let := sphereLaw_probability N
  simp [gibbsLaw,gibbsDensity,partition]

theorem gibbsLaw_zeroHamiltonian_probability (N : ℕ) :
    IsProbabilityMeasure (gibbsLaw N 0 (fun _ => 0)) := by
  rw [gibbsLaw_zeroHamiltonian]
  exact sphereLaw_probability N

theorem gibbsLaw_absolutelyContinuous_zeroHamiltonian {N : ℕ} (β : ℝ) (H : Vector N→ℝ) :
    gibbsLaw N β H ≪ gibbsLaw N 0 (fun _ => 0) := by
  rw [gibbsLaw_zeroHamiltonian]
  exact gibbsLaw_absolutelyContinuous β H

end SlowEquilibration.SphericalModel
