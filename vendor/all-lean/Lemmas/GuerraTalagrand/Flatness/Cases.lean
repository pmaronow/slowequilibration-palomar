module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Lemmas.GuerraTalagrand.Flatness.Cases.Endpoints
public import Lemmas.GuerraTalagrand.Flatness.Cases.SmallNegative
public import Lemmas.GuerraTalagrand.Flatness.Cases.SmallPositive
public import Lemmas.GuerraTalagrand.Flatness.Cases.LargeNegative
public import Lemmas.GuerraTalagrand.Flatness.Cases.LargePositive

@[expose] public section

/-!
# GT flatness cases

This module collects the overlap-region implementations. Import an individual
module for a single case, or import this module for the full case analysis.
-/
