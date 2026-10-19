-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMinMax
public import SlowEquilibration.DenseCoreMinMax

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section

open MeasureTheory Set Filter Module
open SphericalModel
open SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- The actual smooth spherical gradient core inside the literal graph
completion. Its members are genuine smooth ambient function restrictions,
with the actual normalized spherical Gibbs gradient. -/
def smoothGraphCore {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : Submodule ℝ (sphericalSobolevGraph hN β H hH) :=
  LinearMap.range (smoothEnergyToGraph hN β H hH)

/-- Density of the actual smooth core follows from the actual definition
of the spherical form as the topological closure of its smooth graph. -/
theorem smoothGraphCore_dense {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    Dense (smoothGraphCore hN β H hH : Set (sphericalSobolevGraph hN β H hH)) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu := u.property
  change u.val ∈ closure (Set.range (smoothGradientGraphLinear hN β H hH)) at hu
  obtain ⟨y, ⟨f, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp hu ε hε
  refine ⟨smoothEnergyToGraph hN β H hH f, ⟨f, rfl⟩, ?_⟩
  change dist u.val (smoothGradientGraphLinear hN β H hH f) < ε
  exact hy

/-- The ordinary min-max infimum over true finite-dimensional smooth
spherical trial spaces, with the actual completed Dirichlet energy. -/
def sphericalSmoothRayleighMinMax {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (k : ℕ) : ℝ :=
  FormMinMax.coreRayleighMinMax (H := Lp ℝ 2 (gibbsLaw N β H))
    (F := sphericalSobolevGraph hN β H hH)
    (sphericalEnergyL2Map hN β H hH) (smoothGraphCore hN β H hH) k

namespace SphericalSpectralData

variable {N : ℕ} {hN : 2 ≤ N} {β : ℝ} {H : Vector N → ℝ} {hH : Continuous H}

/-- Actual spherical form min-max for any proved dense linear form core. -/
theorem coreMinMax_eq_eigenvalue (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H)
    (core : Submodule ℝ (sphericalSobolevGraph (show 1 ≤ N by omega) β H hH))
    (hdense : Dense (core : Set (sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)))
    (k : ℕ) :
    FormMinMax.coreRayleighMinMax (H := Lp ℝ 2 (gibbsLaw N β H))
      (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)
      (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH) core k = D.eigenvalue k := by
  let Jmap := sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH
  have hJmap : Function.Injective Jmap :=
    sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hHC
  have he : ∀ n : ℕ, Jmap ((ContinuousLinearMap.adjoint (𝕜 := ℝ) Jmap) (D.basis n)) =
      D.resolventEigenvalue n • D.basis n := by
    intro n
    change sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis n) = _
    exact D.eigen n
  have hmono : Monotone (FormMinMax.weight D.resolventEigenvalue) := D.generator_monotone
  have hg := FormMinMax.coreRayleighMinMax_eq_weight
    (H := Lp ℝ 2 (gibbsLaw N β H))
    (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)
    Jmap hJmap D.basis D.resolventEigenvalue (fun n => (D.bounds n).1) he hmono
    core hdense k
  change FormMinMax.coreRayleighMinMax (H := Lp ℝ 2 (gibbsLaw N β H))
      (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)
      (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH) core k = D.eigenvalue k at hg
  exact hg

/-- True smooth-trial min-max for the actual spherical Gibbs gradient
form. The density argument proves equality of the infimum and the actual
generator eigenvalue; it makes no eigenfunction smoothness or attainment
assertion. -/
theorem smoothMinMax_eq_eigenvalue (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (k : ℕ) :
    sphericalSmoothRayleighMinMax (show 1 ≤ N by omega) β H hH k = D.eigenvalue k :=
  D.coreMinMax_eq_eigenvalue hHC (smoothGraphCore (show 1 ≤ N by omega) β H hH)
    (smoothGraphCore_dense (show 1 ≤ N by omega) β H hH) k

end SphericalSpectralData
end
end SlowEquilibration.SphericalForm
