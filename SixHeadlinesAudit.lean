-- SPDX-License-Identifier: Apache-2.0
module

import SixHeadlines
import PressureLowerTailsAudit
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Check the active theorem types independently of their axiom audit.
The first three result groups have Chen's formula as their sole literature
premise. Pressure-tail and generic variance-analytic premises are forbidden. -/
run_cmd do
  let env ← getEnv
  let chenRoots := [
    ``SlowEquilibration.SixHeadlines.theorem_1_2,
    ``SlowEquilibration.SixHeadlines.corollary_1_3_a,
    ``SlowEquilibration.SixHeadlines.corollary_1_3_b,
    ``SlowEquilibration.SixHeadlines.corollary_1_3_b_degree_window,
    ``SlowEquilibration.SixHeadlines.corollary_1_3_b_support,
    ``SlowEquilibration.SixHeadlines.corollary_1_3_c,
    ``SlowEquilibration.SixHeadlines.corollary_1_3_d,
    ``SlowEquilibration.SixHeadlines.theorem_1_4]
  let roots := chenRoots ++ [
    ``SlowEquilibration.SixHeadlines.theorem_1_4_haar,
    ``SlowEquilibration.SixHeadlines.theorem_1_5,
    ``SlowEquilibration.SixHeadlines.theorem_1_6,
    ``SlowEquilibration.SixHeadlines.theorem_1_7]
  let forbidden := [
    "SlowEquilibration.LiteratureSubagBandLowerComplete.PressureLowerTails",
    "ProbabilityTheory.variance"]
  for name in roots do
    let some info := env.find? name | throwError "missing active headline {name}"
    let unwanted := info.type.find? fun e => match e with
      | .const n _ => forbidden.contains n.toString ||
          n.toString.startsWith "SlowEquilibration.LiteratureSubagLemma22Full."
      | _ => false
    if let some e := unwanted then
      throwError "unwanted pressure-tail or variance-analytic premise {e} in {name}"
    let hasChen := (info.type.find? fun e =>
      e.isConstOf ``SlowEquilibration.SourceLiteratureParisi.Chen2013FiniteParisi).isSome
    unless hasChen == chenRoots.contains name do
      throwError "unexpected Chen-premise status for {name}"
  logInfo m!"Checked all {roots.length} active headline exports: only the first three result groups have a Chen premise; no pressure-tail or variance-analytic premise."

/- Audit every active headline declaration and its transitive proof dependencies. -/
run_cmd do
  let permitted := [``propext, ``Quot.sound, ``Classical.choice]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "SlowEquilibration.SixHeadlines." then
      count := count + 1
      let axioms ← collectAxioms name
      for axName in axioms do
        unless permitted.contains axName do
          throwError "forbidden axiom {axName} in {name}"
      logInfo m!"{name}: {axioms}"
  unless count > 0 do
    throwError "the active six-headline surface is empty"
  logInfo m!"Audited {count} active headline declarations; only permitted axioms."
