-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTAPTelescope
public import SlowEquilibration.CSTAPGroundTrialContactGap
public import SlowEquilibration.SourceLiteratureGroundTrialProfile
public import SlowEquilibration.SourceLiteratureGroundStateCenterBridge
public import SlowEquilibration.SourceLiteratureParisi

/-!
# The strict physical TAP gap away from the contact set

Source `thm:th-contact`(3) and `prop:th-structure`(5): if `(ξ,β)` is
strictly 1RSB with contact at `Q`, then for every `q ∈ (0,1) \ {Q}`
`T_β(q) ≤ F(β) - V(q)^2/(8 β^3 M_q) < F(β)`.

The proof combines three ingredients.

* The telescope `F(β) = β 𝒬_q(ℓ_q) + ½ log(1-q) + 𝒫_β(ζ_{β,q}; ψ_q)`
  (`CSTAPTelescope.telescope`), a deterministic identity.
* The ground trial `ℓ_ε` lowers `𝒬_q` by `V(q)^2/(8 β^4 M_q)`
  (`CSTAPGroundTrialContactGap`), and it is a genuine Chen–Sen profile of
  the center covariance (`SourceLiteratureGroundTrialProfile`).
* The thermodynamic limits in `ThermodynamicData` are identified with the
  variational values through the explicit Chen (2013) and Chen–Sen (2017)
  hypotheses (`SourceLiteratureGroundStateCenterBridge`).

Both literature results enter as explicit hypotheses. No Subag input is
used here; the gap is a premise of the Subag adapters downstream.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureStrictTAPGap

open MeasureTheory Set Filter CrisantiSommers SphericalTAPCertificate
open CSTAPGroundTrialQuadratic CSTAPGroundTrialContactGap CSTAPTelescope
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateRadialCoefficients SourceLiteratureGroundStateCenterBridge
open SourceLiteratureGroundTrialProfile LiteratureSubagTAP SphericalModel
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Quantitative source gap `(eq:th-gap)` for any thermodynamic data whose
limits are those of the actual original Gaussian model. -/
theorem tapValue_le_pressure_sub_gap (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≠ Q) :
    tapValue D q ≤ D.pressure -
      (CSStructure.potential μ β (twoAtom x Q) q) ^ 2 /
        (8 * β ^ 3 * curvature β (twoAtom x Q) q) := by
  have hβ := h.beta_pos
  have hP : D.pressure = CSParisiMeasure.variationalValue μ β :=
    tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have hR : D.residual q =
      CSParisiMeasure.variationalValue (physicalResidualMixture μ q hq) β :=
    tendsto_nhds_unique (D.residual_limit q hq) (hChen _ β hβ.le)
  obtain ⟨u, hmin, hlim⟩ := center_ground_limit hChenSen μ hq.1
  have hG : D.ground q = groundFunctional (centerMixture μ q hq.1) u :=
    tendsto_nhds_unique (D.ground_limit q hq) hlim
  set V := CSStructure.potential μ β (twoAtom x Q) q with hVdef
  set M := curvature β (twoAtom x Q) q with hMdef
  have hV : 0 < V := h.positive_off_contact q hq hqQ
  have hM : 0 < M := ground_trial_curvature_pos μ h hq
  have hε : 0 ≤ V / (2 * β ^ 2 * M) := by positivity
  have hground : D.ground q ≤
      functional μ β (twoAtom x Q) q 0 - V ^ 2 / (8 * β ^ 4 * M) := by
    rw [hG]
    calc groundFunctional (centerMixture μ q hq.1) u
        ≤ groundFunctional (centerMixture μ q hq.1) (trialGroundProfile h hq hε) :=
          hmin _
      _ = functional μ β (twoAtom x Q) q (V / (2 * β ^ 2 * M)) :=
          groundFunctional_trialGroundProfile h hq hε
      _ ≤ functional μ β (twoAtom x Q) q 0 - V ^ 2 / (8 * β ^ 4 * M) :=
          ground_trial_strict_contact_gap μ h hq hqQ
  have hres : D.residual q ≤
      (residualTrial h.weight_range h.overlap_range hq).value β
        (residualMixture μ hq).xi := by
    rw [hR]
    exact CSParisiMeasure.canonicalMinimizer_isMinimizer (residualMixture μ hq) β _
  have htel := telescope h hq
  have hβg := mul_le_mul_of_nonneg_left hground hβ.le
  have hscale : β * (V ^ 2 / (8 * β ^ 4 * M)) = V ^ 2 / (8 * β ^ 3 * M) := by
    field_simp [hβ.ne', hM.ne']
  unfold tapValue
  rw [hP, htel]
  nlinarith [hβg, hres, hscale]

/-- Source `prop:th-structure`(5): the strict TAP inequality at every
non-contact overlap, conditional on the cited Chen and Chen–Sen theorems. -/
theorem strictTAPGap_of_literature (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) (D : ThermodynamicData μ β) :
    ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q → tapValue D q < D.pressure := by
  intro q hq hqQ
  have hgap := tapValue_le_pressure_sub_gap hChen hChenSen h D hq hqQ
  have hV : 0 < CSStructure.potential μ β (twoAtom x Q) q :=
    h.positive_off_contact q hq hqQ
  have hM : 0 < curvature β (twoAtom x Q) q := ground_trial_curvature_pos μ h hq
  have hpos : 0 < (CSStructure.potential μ β (twoAtom x Q) q) ^ 2 /
      (8 * β ^ 3 * curvature β (twoAtom x Q) q) := by
    have := h.beta_pos
    positivity
  linarith

/-- Thermodynamic data of the original model, built from the two cited
variational limit theorems alone. `ThermodynamicData` constrains the ground
and residual values only on `(0,1)`. Outside it this definition uses the
physical values at `q = 0`, namely `E(0) = 0` and `F_res(β,0) = F(β)`, as
placeholders. -/
def literatureThermodynamicData (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) :
    ThermodynamicData μ β where
  pressure := CSParisiMeasure.variationalValue μ β
  pressure_limit := hChen μ β hβ
  ground := fun q => if hq : 0 < q then
    groundFunctional (centerMixture μ q hq)
      (Classical.choose (center_ground_limit hChenSen μ hq)) else 0
  ground_limit := by
    intro q hq
    simp only [dite_eq_left hq.1]
    exact (Classical.choose_spec (center_ground_limit hChenSen μ hq.1)).2
  residual := fun q => if hq : q ∈ Ioo (0 : ℝ) 1 then
    CSParisiMeasure.variationalValue (physicalResidualMixture μ q hq) β
    else CSParisiMeasure.variationalValue μ β
  residual_limit := by
    intro q hq
    simp only [dite_eq_left hq]
    exact hChen _ β hβ

end SlowEquilibration.SourceLiteratureStrictTAPGap
