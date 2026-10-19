-- SPDX-License-Identifier: Apache-2.0
module

import all Solution
import SixHeadlinesAudit
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted := [``propext, ``Quot.sound, ``Classical.choice]
  let chenRoots := [
    ``SlowEquilibrationCondensedSource.theorem_1_2,
    ``SlowEquilibrationCondensedSource.corollary_1_3_a,
    ``SlowEquilibrationCondensedSource.corollary_1_3_b,
    ``SlowEquilibrationCondensedSource.corollary_1_3_b_degree_window,
    ``SlowEquilibrationCondensedSource.corollary_1_3_b_support,
    ``SlowEquilibrationCondensedSource.corollary_1_3_c,
    ``SlowEquilibrationCondensedSource.corollary_1_3_d,
    ``SlowEquilibrationCondensedSource.theorem_1_4]
  let roots := chenRoots ++ [
    ``SlowEquilibrationCondensedSource.theorem_1_4_haar,
    ``SlowEquilibrationCondensedSource.theorem_1_5,
    ``SlowEquilibrationCondensedSource.theorem_1_6,
    ``SlowEquilibrationCuspSource.theorem_1_7]
  for name in roots do
    let some info := env.find? name | throwError "missing Comparator export {name}"
    unless info.isTheorem do
      throwError "Comparator theorem export is not a theorem: {name}"
    let hasChen := (info.type.find? fun e =>
      e.isConstOf ``SlowEquilibrationCondensedSource.Chen2013FiniteParisi).isSome
    unless hasChen == chenRoots.contains name do
      throwError "unexpected Chen-premise status for {name}"
    let unwanted := info.type.find? fun e => match e with
      | .const n _ =>
        n.toString == "SlowEquilibration.LiteratureSubagBandLowerComplete.PressureLowerTails" ||
        n.toString == "ProbabilityTheory.variance" ||
        n.toString.startsWith "SlowEquilibration.LiteratureSubagLemma22Full."
      | _ => false
    if let some expression := unwanted then
      throwError "unwanted pressure-tail or variance premise {expression} in {name}"
    let axioms ← collectAxioms name
    for axName in axioms do
      unless permitted.contains axName do
        throwError "forbidden axiom {axName} in {name}"
    logInfo m!"Comparator export {name}: {axioms}"
  let mut count := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "SlowEquilibrationCondensedSource." ||
        name.toString.startsWith "SlowEquilibrationCuspSource." then
      count := count + 1
      let axioms ← collectAxioms name
      for axName in axioms do
        unless permitted.contains axName do
          throwError "forbidden axiom {axName} in source interface {name}"
  unless count ≥ roots.length do
    throwError "incomplete Comparator source surface"
  logInfo m!"Audited {roots.length} Comparator theorem exports and {count} source-interface declarations; only the three standard axioms."
