-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpectral
public import SlowEquilibration.FormMinMax
public import SlowEquilibration.SpectralRank

@[expose] public section

/-!
# Variational min-max and spectral rank of the actual spherical form

The trial spaces here are subspaces of the literal completed spherical
gradient graph. Their energy is the actual completed Gibbs Dirichlet form.
The ordered eigenvalues and spectral projections are those of the actual
compact spherical form resolvent proved in `SphericalSpectral`.
-/

namespace SlowEquilibration.SphericalForm

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Module
open SphericalModel
open SphericalAging.HardSphereDynamics
open scoped InnerProductSpace Topology

/-- The graph norm difference is exactly the literal completed spherical
Dirichlet energy. -/
theorem formEnergy_eq_sphericalCompletedDirichlet {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u : sphericalSobolevGraph hN β H hH) :
    FormMinMax.formEnergy (sphericalEnergyL2Map hN β H hH) u =
      sphericalCompletedDirichlet hN β H hH u u := by
  have h := sphericalCompletedDirichlet_add_L2 hN β H hH u u
  simp only [real_inner_self_eq_norm_sq] at h
  unfold FormMinMax.formEnergy
  linarith

/-- Uniform Rayleigh bounds on genuine `(k+1)`-dimensional subspaces of
the actual completed spherical form domain. -/
def SphericalRayleighTrialBound {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (k : ℕ) (c : ℝ) : Prop :=
  ∃ U : Submodule ℝ (sphericalSobolevGraph hN β H hH),
    FiniteDimensional ℝ U ∧ finrank ℝ U = k+1 ∧
      ∀ u ∈ U, sphericalCompletedDirichlet hN β H hH u u ≤
        c*‖sphericalEnergyL2Map hN β H hH u‖^2

/-- The ordinary variational min-max value of the actual spherical Gibbs
Dirichlet form. -/
def sphericalRayleighMinMax {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (k : ℕ) : ℝ :=
  sInf {c | SphericalRayleighTrialBound hN β H hH k c}

theorem sphericalRayleighMinMax_eq_graph {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (k : ℕ) :
    sphericalRayleighMinMax hN β H hH k =
      FormMinMax.rayleighMinMax (H := Lp ℝ 2 (gibbsLaw N β H))
        (F := sphericalSobolevGraph hN β H hH) (sphericalEnergyL2Map hN β H hH) k := by
  unfold sphericalRayleighMinMax FormMinMax.rayleighMinMax
  congr 1
  ext c
  simp only [SphericalRayleighTrialBound, FormMinMax.RayleighTrialBound,
    formEnergy_eq_sphericalCompletedDirichlet]

namespace SphericalSpectralData

variable {N : ℕ} {hN : 2 ≤ N} {β : ℝ} {H : Vector N → ℝ} {hH : Continuous H}

/-- Genuine Courant--Fischer identity for the actual completed spherical
Gibbs gradient form, derived from its compact resolvent and actual form
domain rather than assumed as spectral data. -/
theorem minMax_eq_eigenvalue (D : SphericalSpectralData hN β H hH)
    (hHC : ContDiff ℝ 1 H) (k : ℕ) :
    sphericalRayleighMinMax (show 1 ≤ N by omega) β H hH k = D.eigenvalue k := by
  let Jmap := sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH
  have hJmap : Function.Injective Jmap :=
    sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hHC
  have he : ∀ n : ℕ, Jmap ((ContinuousLinearMap.adjoint (𝕜 := ℝ) Jmap) (D.basis n)) =
      D.resolventEigenvalue n • D.basis n := by
    intro n
    change sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis n) = _
    exact D.eigen n
  have hmono : Monotone (FormMinMax.weight D.resolventEigenvalue) := D.generator_monotone
  have hg := FormMinMax.rayleighMinMax_eq_weight
    (H := Lp ℝ 2 (gibbsLaw N β H))
    (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)
    Jmap hJmap D.basis D.resolventEigenvalue (fun n => (D.bounds n).1) he hmono k
  change FormMinMax.rayleighMinMax (H := Lp ℝ 2 (gibbsLaw N β H))
      (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)
      (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH) k = D.eigenvalue k at hg
  exact (sphericalRayleighMinMax_eq_graph (show 1 ≤ N by omega) β H hH k).trans hg

/-- The actual finite set of positive spherical generator eigenvalues
below a cutoff, with multiplicity recorded by eigenvector indices. -/
def positiveCutoffIndices (D : SphericalSpectralData hN β H hH) (Λ : ℝ) : Finset ℕ :=
  SpectralRank.positiveCutoffIndices D.toSemigroupData D.generator_tendsto_atTop Λ

@[simp] theorem mem_positiveCutoffIndices (D : SphericalSpectralData hN β H hH)
    (Λ : ℝ) (j : ℕ) :
    j ∈ D.positiveCutoffIndices Λ ↔ 0 < D.eigenvalue j ∧ D.eigenvalue j ≤ Λ :=
  SpectralRank.mem_positiveCutoffIndices D.toSemigroupData D.generator_tendsto_atTop Λ j

/-- The rank of the actual positive spherical spectral projection is
exactly its eigenvalue count, with multiplicity. All zero modes are excluded;
the theorem does not presuppose simplicity of the constant mode. -/
theorem positiveCutoff_finrank (D : SphericalSpectralData hN β H hH) (Λ : ℝ) :
    finrank ℝ (D.toSemigroupData.lowSubspace Λ) = (D.positiveCutoffIndices Λ).card :=
  SpectralRank.lowSubspace_finrank D.toSemigroupData D.generator_tendsto_atTop Λ

/-- The literal actual spherical low spectral range is finite-dimensional
as a consequence of compactness and the constructed diverging spectrum. -/
theorem positiveCutoff_finiteDimensional (D : SphericalSpectralData hN β H hH) (Λ : ℝ) :
    FiniteDimensional ℝ (D.toSemigroupData.lowSubspace Λ) :=
  SpectralRank.lowSubspace_finiteDimensional D.toSemigroupData D.generator_tendsto_atTop Λ

end SphericalSpectralData
end
end SlowEquilibration.SphericalForm
