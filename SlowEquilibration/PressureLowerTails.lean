-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiBound

/-! The exact all-temperature pressure lower-tail predicate, separated
from the lower-band argument so its proof has only analytic dependencies. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LiteratureSubagBandLowerComplete

open MeasureTheory Filter
open SphericalModel
open scoped Topology

set_option autoImplicit false

/-- Lemma 22, with an arbitrary exponential rate and the actual mean pressure. -/
def PressureLowerTails (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ t c : ℝ, 0 < t → 0 < c → ∀ᶠ N : ℕ in atTop,
    (disorderLaw N μ.maxDegree).real
      {J | Real.log (mixturePartition μ β J) / (N : ℝ) <
        quenchedPressure N μ β - t} ≤ Real.exp (-c * (N : ℝ))

end SlowEquilibration.LiteratureSubagBandLowerComplete
