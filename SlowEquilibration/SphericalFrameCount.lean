-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPhysicalSpectral
public import SlowEquilibration.SpectralRank
public import SlowEquilibration.MeasureFrame

@[expose] public section

/-!
# Measure-frame counting for the actual spherical Langevin spectrum

The ordered basis and eigenvalues used below are constructed from the
actual spherical Gibbs gradient form and identified with the physical
Brownian Langevin semigroup. Trial functions belong to that actual graph
completion; their spectral energy identity is proved rather than assumed.
-/

namespace SlowEquilibration.SphericalFrameCount

noncomputable section

open MeasureTheory Filter Set Module
open SphericalModel SphericalForm SphericalPhysicalSpectral SphericalDynamics SphericalReversibility
open SphericalLaplaceIdentification
open scoped Topology InnerProductSpace ENNReal NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable {N : ℕ}

/-- The proved actual ordered spectral data of the genuine finite-mixture
spherical Langevin model. No eigenbasis is provided as input. -/
def data (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :=
  sphericalSpectralData hN β (potential μ J) (potential_continuous μ J)

/-- The actual finite generator-cutoff indices, including its zero modes.
Multiplicity is recorded by the actual eigenvector indices. -/
def cutoffIndices (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β Λ : ℝ) : Finset ℕ :=
  (SpectralRank.cutoff_indices_finite (data hN μ J β).eigenvalue
    (data hN μ J β).generator_tendsto_atTop Λ).toFinset

@[simp] theorem mem_cutoffIndices (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) (j : ℕ) :
    j ∈ cutoffIndices hN μ J β Λ ↔ (data hN μ J β).eigenvalue j ≤ Λ := by
  classical
  simp only [cutoffIndices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The true low generator-eigenspace in the actual Gibbs L² space. -/
def cutoffSpace (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β Λ : ℝ) : Submodule ℝ (SphericalL2Semigroup.Space μ J β) :=
  SpectralRank.basisSpan (data hN μ J β).basis (cutoffIndices hN μ J β Λ)

theorem cutoffSpace_finrank (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) :
    finrank ℝ (cutoffSpace hN μ J β Λ) = (cutoffIndices hN μ J β Λ).card :=
  SpectralRank.basisSpan_finrank (data hN μ J β).basis _

theorem cutoffSpace_finiteDimensional (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) :
    FiniteDimensional ℝ (cutoffSpace hN μ J β Λ) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range _)

/-- Every genuine eigenvector used by the frame count has the actual
physical Langevin multiplier. -/
theorem physical_eigenvector (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (j : ℕ) :
    SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t ((data hN μ J β).basis j) =
      Real.exp (-(t : ℝ)*(data hN μ J β).eigenvalue j) • (data hN μ J β).basis j :=
  SphericalPhysicalSpectral.P_basis (data hN μ J β) t j

/-- The manuscript measure-frame count for the literal spherical Gibbs
Dirichlet form and actual physical Langevin eigenvalues. The input consists
only of the actual trial graph family, measurable representatives, genuine
row and column bounds, and its ordinary mass and Dirichlet-energy integrals.
No eigenbasis, coefficient identities, or spectral form membership is an
input. The cutoff includes zero modes; their removal is a separate statement
about the actual constant-mode simplicity. -/
theorem measure_frame_count {U : Type*} [MeasurableSpace U]
    (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (ν : Measure U) [IsFiniteMeasure ν]
    (u : U → sphericalSobolevGraph (show 1 ≤ N by omega) β
      (potential μ J) (potential_continuous μ J))
    (f : U → Vector N → ℝ) (r Λ R C : ℝ)
    (hf : Measurable (Function.uncurry f)) (hfnonneg : ∀ a x, 0 ≤ f a x)
    (hfrep : ∀ a, f a =ᵐ[mixtureGibbsLaw μ β J]
      formValue (show 1 ≤ N by omega) μ J β (u a))
    (hR : 0 < R) (hC : 0 < C) (hr : 0 ≤ r) (hrΛ : r < Λ)
    (hrow : ∀ᵐ a ∂ν, (∫ x, f a x ∂mixtureGibbsLaw μ β J) ≤ R)
    (hcol : ∀ᵐ x ∂mixtureGibbsLaw μ β J,
      (∫⁻ a, ENNReal.ofReal (f a x) ∂ν) ≤ ENNReal.ofReal C)
    (hmass : Integrable (fun a => ‖formValue (show 1 ≤ N by omega) μ J β (u a)‖^2) ν)
    (henergyInt : Integrable (fun a => sphericalCompletedDirichlet (show 1 ≤ N by omega)
      β (potential μ J) (potential_continuous μ J) (u a) (u a)) ν)
    (henergy : (∫ a, sphericalCompletedDirichlet (show 1 ≤ N by omega) β
      (potential μ J) (potential_continuous μ J) (u a) (u a) ∂ν) ≤
      r*(∫ a, ‖formValue (show 1 ≤ N by omega) μ J β (u a)‖^2 ∂ν)) :
    (1-r/Λ)*(∫ a, ‖formValue (show 1 ≤ N by omega) μ J β (u a)‖^2 ∂ν)/(R*C) ≤
      ((cutoffIndices hN μ J β Λ).card : ℝ) := by
  let := mixtureGibbsLaw_probability (show 1 ≤ N by omega) μ β J
  let D := data hN μ J β
  let F : U → SphericalL2Semigroup.Space μ J β :=
    fun a => formValue (show 1 ≤ N by omega) μ J β (u a)
  have hHC : ContDiff ℝ 1 (potential μ J) := (fieldOfMixture_contDiff μ J).of_le (by simp)
  have hform : ∀ a, Summable (fun j => D.eigenvalue j*(inner ℝ (D.basis j) (F a))^2) := by
    intro a
    exact (D.formDomain_iff hHC (F a)).mp ⟨u a, rfl⟩
  have henergyEq : spectralFrameEnergy D.basis D.eigenvalue F =
      (fun a => sphericalCompletedDirichlet (show 1 ≤ N by omega) β
        (potential μ J) (potential_continuous μ J) (u a) (u a)) := by
    funext a
    exact D.energy_eq_completed hHC (u a)
  apply measure_frame_spectral_count ν (mixtureGibbsLaw μ β J) D.basis F f
    (fun j => (D.basis j : Vector N → ℝ)) D.eigenvalue
    (cutoffIndices hN μ J β Λ) r Λ R C hf hfnonneg hfrep
    (fun j => (Lp.stronglyMeasurable (D.basis j)).measurable)
    (fun _ => Filter.Eventually.of_forall (fun _ => rfl)) hR hC hr hrΛ hrow hcol hmass D.eigenvalue_nonneg
    (fun j => mem_cutoffIndices hN μ J β Λ j) (ae_of_all _ hform)
  · simpa only [henergyEq] using henergyInt
  · simpa only [henergyEq] using henergy

/-- The same genuine measure-frame bound stated as the actual low-spectrum
dimension, rather than as a supplied abstract count. -/
theorem measure_frame_dimension {U : Type*} [MeasurableSpace U]
    (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (ν : Measure U) [IsFiniteMeasure ν]
    (u : U → sphericalSobolevGraph (show 1 ≤ N by omega) β
      (potential μ J) (potential_continuous μ J))
    (f : U → Vector N → ℝ) (r Λ R C : ℝ)
    (hf : Measurable (Function.uncurry f)) (hfnonneg : ∀ a x, 0 ≤ f a x)
    (hfrep : ∀ a, f a =ᵐ[mixtureGibbsLaw μ β J]
      formValue (show 1 ≤ N by omega) μ J β (u a))
    (hR : 0 < R) (hC : 0 < C) (hr : 0 ≤ r) (hrΛ : r < Λ)
    (hrow : ∀ᵐ a ∂ν, (∫ x, f a x ∂mixtureGibbsLaw μ β J) ≤ R)
    (hcol : ∀ᵐ x ∂mixtureGibbsLaw μ β J,
      (∫⁻ a, ENNReal.ofReal (f a x) ∂ν) ≤ ENNReal.ofReal C)
    (hmass : Integrable (fun a => ‖formValue (show 1 ≤ N by omega) μ J β (u a)‖^2) ν)
    (henergyInt : Integrable (fun a => sphericalCompletedDirichlet (show 1 ≤ N by omega)
      β (potential μ J) (potential_continuous μ J) (u a) (u a)) ν)
    (henergy : (∫ a, sphericalCompletedDirichlet (show 1 ≤ N by omega) β
      (potential μ J) (potential_continuous μ J) (u a) (u a) ∂ν) ≤
      r*(∫ a, ‖formValue (show 1 ≤ N by omega) μ J β (u a)‖^2 ∂ν)) :
    (1-r/Λ)*(∫ a, ‖formValue (show 1 ≤ N by omega) μ J β (u a)‖^2 ∂ν)/(R*C) ≤
      (finrank ℝ (cutoffSpace hN μ J β Λ) : ℝ) := by
  rw [cutoffSpace_finrank]
  exact measure_frame_count hN μ J β ν u f r Λ R C hf hfnonneg hfrep hR hC hr hrΛ
    hrow hcol hmass henergyInt henergy

end
end SlowEquilibration.SphericalFrameCount
