-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCenteredObservables
public import SlowEquilibration.Correlation

/-! Actual low-mode spin projection and direct stationary correlation.
The spectrum, zero-mode centering, projection tail and physical semigroup
displacement are constructed or proved internally from the genuine form. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalSpinProjection

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalPhysicalSpectral SphericalBarycenter
open SphericalLaplaceIdentification SphericalCenteredObservables
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N M : ℕ}

def data (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :=
  normalizedSphericalSpectralData hN β (potential μ J) (potential_continuous μ J)

/-- The actual positive spectral cutoff acts on each actual Gibbs L²
coordinate. Its range will be identified with its orthogonal projection. -/
def vectorCutoff (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β Λ : ℝ) : VectorSpace (Fin M) μ J β →L[ℝ] VectorSpace (Fin M) μ J β :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin M => SphericalL2Semigroup.Space μ J β)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi (fun a => ((data hN μ J β).toSemigroupData.cutoff Λ).comp
      (PiLp.proj 2 (fun _ : Fin M => SphericalL2Semigroup.Space μ J β) a)))

@[simp] lemma vectorCutoff_apply (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) (F : VectorSpace (Fin M) μ J β) (a : Fin M) :
    vectorCutoff hN μ J β Λ F a = (data hN μ J β).toSemigroupData.cutoff Λ (F a) := rfl

lemma vectorCutoff_isSymmetric (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) :
    (vectorCutoff (M := M) hN μ J β Λ).toLinearMap.IsSymmetric := by
  intro F G
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun a _ =>
    ((data hN μ J β).toSemigroupData.cutoff_isSymmetric Λ).apply_clm (F a) (G a))

lemma vectorCutoff_idempotent (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) (F : VectorSpace (Fin M) μ J β) :
    vectorCutoff hN μ J β Λ (vectorCutoff hN μ J β Λ F) = vectorCutoff hN μ J β Λ F := by
  apply PiLp.ext
  intro a
  exact (data hN μ J β).toSemigroupData.cutoff_idempotent Λ (F a)

def lowSpace (hN : 2 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β Λ : ℝ) : Submodule ℝ (VectorSpace (Fin M) μ J β) := (vectorCutoff hN μ J β Λ).range

lemma vectorCutoff_isSymmetricProjection (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) :
    (vectorCutoff (M := M) hN μ J β Λ).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, vectorCutoff_isSymmetric hN μ J β Λ⟩
  apply LinearMap.ext
  intro F
  exact vectorCutoff_idempotent hN μ J β Λ F

instance lowSpace_hasOrthogonalProjection (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) :
    (lowSpace (M := M) hN μ J β Λ).HasOrthogonalProjection :=
  (vectorCutoff_isSymmetricProjection hN μ J β Λ).hasOrthogonalProjection_range

lemma vectorCutoff_eq_starProjection (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) :
    vectorCutoff (M := M) hN μ J β Λ = (lowSpace hN μ J β Λ).starProjection := by
  apply ContinuousLinearMap.coe_injective
  exact (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp
    (vectorCutoff_isSymmetricProjection hN μ J β Λ)).2

lemma centered_coordinate_formDomain (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (a : Fin M) :
    (data hN μ J β).toSemigroupData.FormDomain (centeredL2 (show 1 ≤ N by omega) μ J β B hB a) := by
  apply ((data hN μ J β).formDomain_iff ((fieldOfMixture_contDiff μ J).of_le (by simp)) _).mp
  exact ⟨C1ToGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)
    (fun x => centered μ J β B x a) (contDiff_vector_coordinate (centered_contDiff μ J β hB) a), rfl⟩

lemma centered_coordinate_spectral_energy (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (a : Fin M) :
    (data hN μ J β).toSemigroupData.energy (centeredL2 (show 1 ≤ N by omega) μ J β B hB a) =
      dirichletEnergy N β (potential μ J) (fun x => B x a) := by
  have he := (data hN μ J β).energy_eq_completed ((fieldOfMixture_contDiff μ J).of_le (by simp))
    (C1ToGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)
      (fun x => centered μ J β B x a) (contDiff_vector_coordinate (centered_contDiff μ J β hB) a))
  rw [sphericalCompletedDirichlet_C1_energy,
    centered_coordinate_energy (show 1 ≤ N by omega) β (potential μ J) μ J B a] at he
  exact he

/-- Exact source projection tail, with actual smooth B and actual energy;
no form, coefficient-centering or tail hypothesis is supplied. -/
theorem centered_projection_tail (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ‖centeredL2 (show 1 ≤ N by omega) μ J β B hB -
      vectorCutoff hN μ J β Λ (centeredL2 (show 1 ≤ N by omega) μ J β B hB)‖^2 ≤
        vectorDirichletEnergy β (potential μ J) B / Λ := by
  rw [PiLp.norm_sq_eq_of_L2]
  let C : Fin M → Lp ℝ 2 (gibbsLaw N β (potential μ J)) :=
    fun a => centeredL2 (show 1 ≤ N by omega) μ J β B hB a
  change (∑ a : Fin M, ‖C a - (data hN μ J β).toSemigroupData.cutoff Λ (C a)‖^2) ≤ _
  have hscalar (a : Fin M) := (data hN μ J β).toSemigroupData.cutoff_tail_energy_le Λ hΛ
    (centeredL2 (show 1 ≤ N by omega) μ J β B hB a)
    (centered_coordinate_formDomain hN μ J β B hB a)
    (centeredL2_spectrally_centered hN μ J β B hB a)
  simp_rw [centered_coordinate_spectral_energy] at hscalar
  exact (Finset.sum_le_sum (fun a _ => hscalar a)).trans_eq (by rw [← Finset.sum_div]; rfl)

/-- Exact source low-mode correlation floor, for actual physical transition
and the constructed positive spectral projection. -/
theorem projected_physical_correlation (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) (t : ℝ≥0) (Z : VectorSpace (Fin M) μ J β) :
    Real.exp (-(t : ℝ) * Λ) * ‖vectorCutoff hN μ J β Λ Z‖^2 ≤
      inner ℝ Z (vectorP (show 1 ≤ N by omega) μ J β t Z) := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, PiLp.inner_apply]
  apply Finset.sum_le_sum
  intro a _
  have hs := (data hN μ J β).toSemigroupData.projected_correlation_lower Λ t (Z a)
  rw [← (data hN μ J β).toSemigroupData.cutoff_eq_starProjection] at hs
  change Real.exp (-(t : ℝ) * Λ) * ‖(data hN μ J β).toSemigroupData.cutoff Λ (Z a)‖^2 ≤
    inner ℝ (Z a) (SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t (Z a))
  rw [P_eq_diagonal (data hN μ J β)]
  exact hs

/-- Unit-norm actual spin projection bound, from literal Gibbs mean
alignment and true spherical Dirichlet energy of any smooth unit observable. -/
theorem spin_projection_norm_lower (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, SphericalAging.HardSphereDynamics.OnSphere x → ‖B x‖ ≤ 1)
    {a Λ : ℝ} (hΛ : 0 < Λ)
    (ha : a ≤ ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β J) :
    max 0 (a - ‖mean μ J β spin‖ - Real.sqrt (vectorDirichletEnergy β (potential μ J) B / Λ)) ≤
      ‖vectorCutoff hN μ J β Λ
        (centeredL2 (show 1 ≤ N by omega) μ J β spin (spin_contDiff.of_le (by simp)))‖ := by
  let Z := centeredL2 (show 1 ≤ N by omega) μ J β spin (spin_contDiff.of_le (by simp))
  let C := centeredL2 (show 1 ≤ N by omega) μ J β B hBs
  have hE : 0 ≤ vectorDirichletEnergy β (potential μ J) B :=
    Finset.sum_nonneg (fun a _ => dirichletEnergy_nonneg _ _ _ _)
  have htail := centered_projection_tail hN μ J β B hBs hΛ
  have herr : ‖C - vectorCutoff hN μ J β Λ C‖ ≤ Real.sqrt (vectorDirichletEnergy β (potential μ J) B / Λ) := by
    nlinarith [Real.sq_sqrt (div_nonneg hE hΛ.le), Real.sqrt_nonneg (vectorDirichletEnergy β (potential μ J) B / Λ),
      norm_nonneg (C - vectorCutoff hN μ J β Λ C)]
  have hnorm := norm_image_lower_of_displacement (vectorCutoff hN μ J β Λ)
    (vectorCutoff_isSymmetric hN μ J β Λ) Z C
    (Real.sqrt (vectorDirichletEnergy β (potential μ J) B / Λ))
    (centered_spin_norm_le_one (show 1 ≤ N by omega) μ J β)
    (centeredL2_norm_le_one (show 1 ≤ N by omega) μ J β B hBs hB) (Real.sqrt_nonneg _) herr
  have halign := centered_spin_alignment_lower (show 1 ≤ N by omega) μ J β B hBs hB ha
  exact (max_le_max le_rfl (sub_le_sub_right halign _)).trans hnorm

lemma vectorP_square (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) :
    vectorP (ι := Fin M) hN μ J β t =
      (vectorP hN μ J β (t / 2)).comp (vectorP hN μ J β (t / 2)) := by
  apply ContinuousLinearMap.ext
  intro F
  apply PiLp.ext
  intro a
  change SphericalL2Semigroup.P hN μ J β t (F a) =
    SphericalL2Semigroup.P hN μ J β (t / 2) (SphericalL2Semigroup.P hN μ J β (t / 2) (F a))
  rw [← ContinuousLinearMap.comp_apply, ← SphericalL2Semigroup.P_add, add_halves]

/-- Direct physical source correlation estimate for the literal centered
spin and a genuine smooth unit observable; its displacement bound is proved
from the actual completed form, rather than supplied as a premise. -/
theorem spin_direct_correlation_lower (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, SphericalAging.HardSphereDynamics.OnSphere x → ‖B x‖ ≤ 1)
    {a : ℝ} (ha : a ≤ ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β J) (t : ℝ≥0) :
    (max 0 (a - ‖mean μ J β spin‖ - Real.sqrt ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2)))^2 ≤
      inner ℝ (centeredL2 (show 1 ≤ N by omega) μ J β spin (spin_contDiff.of_le (by simp)))
        (vectorP (show 1 ≤ N by omega) μ J β t
          (centeredL2 (show 1 ≤ N by omega) μ J β spin (spin_contDiff.of_le (by simp)))) := by
  let hN1 : 1 ≤ N := by omega
  let Z := centeredL2 hN1 μ J β spin (spin_contDiff.of_le (by simp))
  let C := centeredL2 hN1 μ J β B hBs
  let u (a : Fin N) := C1ToGraph hN1 β (potential μ J) (potential_continuous μ J)
    (fun x => centered μ J β B x a) (contDiff_vector_coordinate (centered_contDiff μ J β hBs) a)
  have hdis := vector_semigroup_displacement_energy_le (data hN μ J β) (t / 2) u
  have henergyEq : (∑ a : Fin N, sphericalCompletedDirichlet hN1 β (potential μ J)
      (potential_continuous μ J) (u a) (u a)) = vectorDirichletEnergy β (potential μ J) B := by
    dsimp [u]
    simp_rw [sphericalCompletedDirichlet_C1_energy,
      centered_coordinate_energy hN1 β (potential μ J) μ J B]
    rfl
  have hFV : vectorFormValue hN1 μ J β u = C := rfl
  rw [hFV, henergyEq] at hdis
  simp only [NNReal.coe_div, NNReal.coe_ofNat] at hdis
  have hE : 0 ≤ vectorDirichletEnergy β (potential μ J) B :=
    Finset.sum_nonneg (fun a _ => dirichletEnergy_nonneg _ _ _ _)
  have hnon : 0 ≤ (t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2 := by positivity
  have herr : ‖C - vectorP hN1 μ J β (t / 2) C‖ ≤
      Real.sqrt ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2) := by
    nlinarith [Real.sq_sqrt hnon, Real.sqrt_nonneg ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2),
      norm_nonneg (C - vectorP hN1 μ J β (t / 2) C)]
  have hc := correlation_lower_of_displacement (vectorP hN1 μ J β (t / 2))
    (vectorP_isSymmetric hN1 μ J β (t / 2)) Z C
    (Real.sqrt ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2))
    (centered_spin_norm_le_one hN1 μ J β) (centeredL2_norm_le_one hN1 μ J β B hBs hB)
    (Real.sqrt_nonneg _) herr
  have hsq : vectorP hN1 μ J β t Z = vectorP hN1 μ J β (t / 2) (vectorP hN1 μ J β (t / 2) Z) := by
    rw [vectorP_square]
    rfl
  rw [← hsq] at hc
  have halign := centered_spin_alignment_lower hN1 μ J β B hBs hB ha
  have hmax := max_le_max (show (0 : ℝ) ≤ 0 from le_rfl) (sub_le_sub_right halign
    (Real.sqrt ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2)))
  exact (pow_le_pow_left₀ (le_max_left _ _) hmax 2).trans hc

end SlowEquilibration.SphericalSpinProjection
