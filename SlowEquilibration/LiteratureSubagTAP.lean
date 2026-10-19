-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagContact
public import SlowEquilibration.LiteratureSubagProposition24
public import SlowEquilibration.FiniteMixtureTaylorResidual

@[expose] public section

/-!
# The physical generalized TAP identity as an explicit cited input

Subag, *Free energy landscapes in spherical spin glasses*, Duke Math. J.
173 (2024), arXiv:1804.10576v6, Theorem 5, equation (1.24).
`ThermodynamicData` pins every scalar to a limit of a literal original
Gaussian spherical model.  In particular, the ground value is the maximum
of the original field on the radius-`sqrt(Nq)` center sphere, and the
residual pressure is that of the exact Taylor residual after removing its
constant and linear terms.  The theorem is passed as an explicit argument;
the data are not allowed to supply a free, ungrounded TAP value.
-/

namespace SlowEquilibration.LiteratureSubagTAP

noncomputable section
open MeasureTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions
open scoped Topology
set_option autoImplicit false

/-- The expected original-field maximum at squared center overlap `q`,
divided by the physical dimension `N`. -/
def expectedCenterGroundEnergy (N : ℕ) (μ : FiniteMixture) (q : ℝ) : ℝ :=
  (∫ J : Disorder N μ.maxDegree,
    sSup ((field (mixtureCoefficients μ) J) ''
      {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q})
    ∂disorderLaw N μ.maxDegree) / (N : ℝ)

/-- The residual covariance is `ξ(q+(1-q)t)-ξ(q)-(1-q)ξ'(q)t` by the
proved `FiniteMixture.taylorResidual_xi` identity. -/
def physicalResidualMixture (μ : FiniteMixture) (q : ℝ)
    (hq : q ∈ Ioo (0 : ℝ) 1) : FiniteMixture :=
  μ.taylorResidual hq.1 (sub_pos.mpr hq.2)

/-- Thermodynamic limits to which the cited Theorem 5 refers.  These
limit-identification fields are mathematical premises that must be supplied
by the external Parisi and ground-state packages or proved locally. -/
structure ThermodynamicData (μ : FiniteMixture) (β : ℝ) where
  pressure : ℝ
  pressure_limit : Tendsto (fun N : ℕ => quenchedPressure N μ β)
    atTop (nhds pressure)
  ground : ℝ → ℝ
  ground_limit : ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
    Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q)
      atTop (nhds (ground q))
  residual : ℝ → ℝ
  residual_limit : ∀ (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1),
    Tendsto (fun N : ℕ =>
      quenchedPressure N (physicalResidualMixture μ q hq) β)
      atTop (nhds (residual q))

/-- The right side of Subag's generalized TAP identity, at the limits of
the actual ground and residual models above. -/
def tapValue {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (q : ℝ) : ℝ :=
  β * D.ground q + Real.log (1 - q) / 2 + D.residual q

/-- Published Theorem 5, restricted to the positive overlaps needed for
replica exclusion.  For non-multisamplable `q`, its inequality is strict. -/
def Theorem5 {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) : Prop :=
  0 < β ∧ ∀ q : ℝ, q ∈ Ioo (0 : ℝ) 1 →
    (D.pressure = tapValue D q ↔ MultiSamplable μ β q) ∧
      tapValue D q ≤ D.pressure

/-- The physical strict TAP gap, once proved from the contact potential,
Chen--Sen ground value and residual pressure, rules out multisamplability.
This uses only the published equality direction of Theorem 5. -/
theorem not_multiSamplable_of_strictTAPGap
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    (h5 : Theorem5 D) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hgap : tapValue D q < D.pressure) :
    ¬ MultiSamplable μ β q := by
  intro hm
  have heq := (h5.2 q hq).1.mpr hm
  exact hgap.ne heq.symm

end
end SlowEquilibration.LiteratureSubagTAP
