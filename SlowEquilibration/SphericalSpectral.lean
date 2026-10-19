module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphereCompactEmbedding
public import SlowEquilibration.SphericalInfiniteDimensional
public import SlowEquilibration.SphericalEigenvalues
public import SlowEquilibration.OrderedCompactEigenbasis
public import SlowEquilibration.GraphEigenbasis
public import SlowEquilibration.SpectralSemigroup
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# The actual ordered spherical resolvent and form eigenbasis

The compact operator used here is the resolvent of the actual completed
spherical Gibbs gradient form. Its compactness follows from the proved
chart-volume and Rellich arguments; its infinite dimension follows from
actual polynomial observables. Thus the ordered basis, operator eigenvalue
equations, and weighted form domain are conclusions about that form.
-/

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open scoped BigOperators InnerProductSpace Topology

/-- The actual spherical Gibbs form resolvent is compact in every ambient
manuscript dimension N ≥ 2. -/
theorem sphericalL2Resolvent_compact {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    IsCompactOperator (sphericalL2Resolvent (show 1 ≤ N by omega) β H hH) :=
  (SphereCompactEmbedding.sphericalEnergyL2Map_compact_of_two_le hN β H hH).comp_clm
    (sphericalWeakSolution (show 1 ≤ N by omega) β H hH)

/-- A genuine ordered eigen Hilbert basis for the actual spherical
resolvent, with all ordering and divergence properties proved. -/
theorem exists_spherical_ordered_eigenbasis {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    ∃ b : HilbertBasis ℕ ℝ (Lp ℝ 2 (gibbsLaw N β H)), ∃ μ : ℕ → ℝ,
      (∀ n, 0 < μ n ∧ μ n ≤ 1) ∧ Antitone μ ∧ Tendsto μ atTop (𝓝 (0 : ℝ)) ∧
      (∀ n, sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (b n) = μ n • b n) ∧
      Monotone (fun n => (μ n)⁻¹ - 1) ∧
      Tendsto (fun n => (μ n)⁻¹ - 1) atTop atTop := by
  let := gibbsLaw_probability (show 1 ≤ N by omega) β hH
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact CompactEigenbasis.exists_ordered_nat_eigenbasis
    (sphericalL2Resolvent (show 1 ≤ N by omega) β H hH)
    (sphericalL2Resolvent_compact hN β H hH)
    (sphericalL2Resolvent_symmetric (show 1 ≤ N by omega) β H hH)
    (sphericalL2Resolvent_positive (show 1 ≤ N by omega) β H hH)
    (sphericalL2Resolvent_norm_le (show 1 ≤ N by omega) β H hH)
    (sphericalL2_not_finiteDimensional hN β H hH)

/-- The package retains actual resolvent eigenvalue equations. In particular
its basis and eigenvalues are obtained from the actual form resolvent. -/
structure SphericalSpectralData {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) where
  basis : HilbertBasis ℕ ℝ (Lp ℝ 2 (gibbsLaw N β H))
  resolventEigenvalue : ℕ → ℝ
  bounds : ∀ n, 0 < resolventEigenvalue n ∧ resolventEigenvalue n ≤ 1
  antitone : Antitone resolventEigenvalue
  tendsto_zero : Tendsto resolventEigenvalue atTop (𝓝 (0 : ℝ))
  eigen : ∀ n, sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (basis n) =
    resolventEigenvalue n • basis n
  generator_monotone : Monotone (fun n => (resolventEigenvalue n)⁻¹ - 1)
  generator_tendsto_atTop : Tendsto (fun n => (resolventEigenvalue n)⁻¹ - 1) atTop atTop

theorem sphericalSpectralData_nonempty {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : Nonempty (SphericalSpectralData hN β H hH) := by
  obtain ⟨b, μ, hb, ha, ht, he, hm, hinfty⟩ := exists_spherical_ordered_eigenbasis hN β H hH
  exact ⟨⟨b, μ, hb, ha, ht, he, hm, hinfty⟩⟩

/-- Choice of the proved actual ordered spherical eigenbasis. -/
def sphericalSpectralData {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : SphericalSpectralData hN β H hH :=
  Classical.choice (sphericalSpectralData_nonempty hN β H hH)

namespace SphericalSpectralData

variable {N : ℕ} {hN : 2 ≤ N} {β : ℝ} {H : Vector N → ℝ} {hH : Continuous H}

/-- The actual nonnegative generator eigenvalues. -/
def eigenvalue (D : SphericalSpectralData hN β H hH) (n : ℕ) : ℝ :=
  (D.resolventEigenvalue n)⁻¹ - 1

theorem eigenvalue_nonneg (D : SphericalSpectralData hN β H hH) (n : ℕ) :
    0 ≤ D.eigenvalue n := by
  dsimp [eigenvalue]
  have hi := (D.bounds n).2
  have hp := (D.bounds n).1
  have h := (one_le_inv₀ hp).mpr hi
  linarith

/-- The genuine actual spherical spectral data viewed by the diagonal
semigroup API. Identification with the actual SDE semigroup is a separate
proved dynamical step. -/
def toSemigroupData (D : SphericalSpectralData hN β H hH) :
    SpectralSemigroup.Data (Lp ℝ 2 (gibbsLaw N β H)) where
  basis := D.basis
  eigenvalue := D.eigenvalue
  eigenvalue_nonneg := D.eigenvalue_nonneg

theorem generator_eigen (D : SphericalSpectralData hN β H hH) (n : ℕ) :
    ∃ hn : D.basis n ∈ (sphericalGenerator (show 1 ≤ N by omega) β H hH).domain,
      sphericalGenerator (show 1 ≤ N by omega) β H hH ⟨D.basis n, hn⟩ =
        D.eigenvalue n • D.basis n :=
  sphericalGenerator_of_resolvent_eigenvector (show 1 ≤ N by omega) β H hH
    (D.resolventEigenvalue n) (D.basis n) (D.basis.orthonormal.ne_zero n) (D.eigen n)

/-- Exact actual completed-energy Parseval formula. -/
theorem energy_hasSum (D : SphericalSpectralData hN β H hH) (hHC : ContDiff ℝ 1 H)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH) :
    HasSum (fun n => D.eigenvalue n *
      (D.basis.repr (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH u) n) ^ 2)
      (sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH u u) := by
  have hs := GraphEigenbasis.graph_energy_hasSum
    (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH)
    (sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hHC)
    D.basis D.resolventEigenvalue (fun n => (D.bounds n).1)
    (fun n => by change sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis n) = _; exact D.eigen n) u
  rw [sphericalSobolev_norm_sq] at hs
  simpa only [add_sub_cancel_left, eigenvalue] using hs

/-- Actual form membership is exactly convergence of the weighted actual
resolvent-basis coefficient squares. -/
theorem formDomain_iff (D : SphericalSpectralData hN β H hH) (hHC : ContDiff ℝ 1 H)
    (f : Lp ℝ 2 (gibbsLaw N β H)) :
    (∃ u : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH,
      sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH u = f) ↔
        D.toSemigroupData.FormDomain f := by
  simp only [SpectralSemigroup.Data.FormDomain, SpectralSemigroup.Data.coefficient,
    toSemigroupData]
  simpa only [HilbertBasis.repr_apply_apply, eigenvalue] using
    GraphEigenbasis.range_iff_summable_generator
    (E := Lp ℝ 2 (gibbsLaw N β H))
    (F := sphericalSobolevGraph (show 1 ≤ N by omega) β H hH)
    (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH)
    (sphericalEnergyL2Map_injective (show 1 ≤ N by omega) β H hHC)
    D.basis D.resolventEigenvalue (fun n => (D.bounds n).1)
    (fun n => by change sphericalL2Resolvent (show 1 ≤ N by omega) β H hH (D.basis n) = _; exact D.eigen n) f

/-- The diagonal spectral energy is the literal completed spherical form
energy, established by actual graph Parseval. -/
theorem energy_eq_completed (D : SphericalSpectralData hN β H hH) (hHC : ContDiff ℝ 1 H)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β H hH) :
    D.toSemigroupData.energy (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH u) =
      sphericalCompletedDirichlet (show 1 ≤ N by omega) β H hH u u := by
  simpa only [SpectralSemigroup.Data.energy, SpectralSemigroup.Data.coefficient,
    toSemigroupData, HilbertBasis.repr_apply_apply] using (D.energy_hasSum hHC u).tsum_eq

end SphericalSpectralData
end
end SlowEquilibration.SphericalForm
