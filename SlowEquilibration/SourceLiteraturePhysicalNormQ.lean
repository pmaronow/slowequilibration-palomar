-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureStrictTAPGap
public import SlowEquilibration.SourceLiteratureParisiTemperatureEven
public import SlowEquilibration.SourcePureCapturePhysicalNormParisiExclusion
public import SlowEquilibration.LiteratureSubagFullOverlapAdapter

/-!
# The physical directing norm from cited literature alone

Source `thm:dir-norm` input for the pure and mixed capture arguments. With
the strict TAP gap proved from the Chen and Chen–Sen variational limits,
Subag's Theorem 5 and Remark 25 exclude every off-contact equilateral
replica block, and the Ghirlanda–Guerra/directing argument then forces the
norm `Q` on every directing representation of every original array limit.

The Chen pressure hypothesis is cited at nonnegative temperatures only; the
all-real form needed by the GG wrappers follows from temperature evenness.
The remaining hypotheses are exactly the published statements.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteraturePhysicalNormQ

open Set Filter
open SphericalTAPCertificate LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open SourceLiteratureParisiTemperatureEven
open SourcePureCapturePhysicalNormParisiExclusion LiteratureSubagFullOverlapAdapter
open PureCapturePhysicalCoarseDiniAssembly

set_option autoImplicit false

/-- The source directing-norm input, for any thermodynamic data satisfying
Subag's Theorem 5. -/
theorem physicalDirectingNormQ_of_literature (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) (D : ThermodynamicData μ β) (h5 : Theorem5 D)
    (h25 : Remark25Contrapositive μ β) :
    PhysicalDirectingNormQ μ β Q :=
  physical_directing_normQ_of_parisi_and_replica_exclusion μ h
    (finite_pressure_limit_all_real_shift hChen μ)
    (physical_full_overlap_exclusion_of_offContactTAPGap D h5 h25
      (strictTAPGap_of_literature hChen hChenSen h D))

/-- The same conclusion with the thermodynamic data constructed from the
two variational limit theorems, so that Subag's Theorem 5 is invoked only
for the literal original-model limits. -/
theorem physicalDirectingNormQ_of_cited_theorems (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) :
    PhysicalDirectingNormQ μ β Q :=
  physicalDirectingNormQ_of_literature hChen hChenSen h _ h5 h25

end SlowEquilibration.SourceLiteraturePhysicalNormQ
