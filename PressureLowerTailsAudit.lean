-- SPDX-License-Identifier: Apache-2.0
module

import SlowEquilibration.LiteratureSubagLemma22Full
import Lean.Util.CollectAxioms

open Lean Elab Command
open SlowEquilibration

-- This checks the entire requested type, including the absence of any
-- remaining literature, variance, convex-tail or Hermite-bound argument.
example : ∀ μ : FiniteMixture, ∀ β : ℝ,
    LiteratureSubagBandLowerComplete.PressureLowerTails μ β :=
  LiteratureSubagLemma22Full.universalPressureLowerTails

#check LiteratureSubagLemma22Full.pressureLowerTails
#check LiteratureSubagLemma22Full.universalPressureLowerTails

run_cmd do
  let permitted := [``propext, ``Quot.sound, ``Classical.choice]
  for name in [``LiteratureSubagLemma22Full.logPartition_variance_sublinear,
      ``LiteratureSubagLemma22Full.pressureLowerTails,
      ``LiteratureSubagLemma22Full.universalPressureLowerTails] do
    let axioms ← collectAxioms name
    for axName in axioms do
      unless permitted.contains axName do
        throwError "forbidden axiom {axName} in {name}"
    logInfo m!"{name}: {axioms}"
