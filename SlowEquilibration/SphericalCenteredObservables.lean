-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothCorrelation
public import SlowEquilibration.SphericalBarycenterMeans
public import Mathlib.Probability.Moments.Covariance

/-! Actual centered smooth vector observables in spherical Gibbs L².
Their centering, variance, norm and energy are proved from ordinary Gibbs
integrals and literal tangent derivatives. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalCenteredObservables

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalPhysicalSpectral SphericalBarycenter
open SphericalLaplaceIdentification SphericalAging.HardSphereDynamics
open SphericalReversibility
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N M : ℕ}

def mean (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) : Vector M := ∫ x, B x ∂mixtureGibbsLaw μ β J

def centered (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (x : Vector N) : Vector M := B x - mean μ J β B

lemma centered_contDiff (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {B : Vector N → Vector M} (hB : ContDiff ℝ 1 B) :
    ContDiff ℝ 1 (centered μ J β B) := hB.sub contDiff_const

/-- The genuine finite-vector Gibbs Hilbert class of a smooth observable. -/
def vectorL2 (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) : VectorSpace (Fin M) μ J β :=
  WithLp.toLp 2 (smoothCoordinateL2 hN μ J β B hB)

@[simp] lemma vectorL2_apply (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M)
    (hB : ContDiff ℝ 1 B) (a : Fin M) :
    vectorL2 hN μ J β B hB a = smoothCoordinateL2 hN μ J β B hB a := rfl

def centeredL2 (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) : VectorSpace (Fin M) μ J β :=
  vectorL2 hN μ J β (centered μ J β B) (centered_contDiff μ J β hB)

lemma mean_coordinate (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {B : Vector N → Vector M} (hB : Continuous B) (a : Fin M) :
    (∫ x, B x a ∂mixtureGibbsLaw μ β J) = mean μ J β B a := by
  have hi := integrable_gibbs_of_continuous_vector hN β (potential_continuous μ J) hB
  exact (PiLp.proj 2 (fun _ : Fin M => ℝ) a : Vector M →L[ℝ] ℝ).integral_comp_comm hi

lemma centered_coordinate_integral (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {B : Vector N → Vector M}
    (hB : ContDiff ℝ 1 B) (a : Fin M) :
    (∫ x, centered μ J β B x a ∂mixtureGibbsLaw μ β J) = 0 := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  let _ := gibbsLaw_probability hN β (potential_continuous μ J)
  change (∫ x, B x a - mean μ J β B a ∂mixtureGibbsLaw μ β J) = 0
  have hi : Integrable (fun x => B x a) (mixtureGibbsLaw μ β J) :=
    integrable_gibbs_of_continuous hN β (potential_continuous μ J)
      (contDiff_vector_coordinate hB a).continuous
  rw [integral_sub hi (integrable_const _),
    mean_coordinate hN μ J β hB.continuous a, integral_const, probReal_univ, one_smul, sub_self]

lemma vectorL2_inner (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (B C : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (hC : ContDiff ℝ 1 C) :
    inner ℝ (vectorL2 hN μ J β B hB) (vectorL2 hN μ J β C hC) =
      ∫ x, inner ℝ (B x) (C x) ∂mixtureGibbsLaw μ β J := by
  rw [PiLp.inner_apply]
  have hcoord (a : Fin M) : inner ℝ (vectorL2 hN μ J β B hB a) (vectorL2 hN μ J β C hC a) =
      ∫ x, B x a * C x a ∂mixtureGibbsLaw μ β J :=
    gibbsToL2_inner hN β (potential μ J) (potential_continuous μ J)
      (fun x => B x a) (fun x => C x a) (contDiff_vector_coordinate hB a).continuous
      (contDiff_vector_coordinate hC a).continuous
  simp_rw [hcoord]
  have hi (a : Fin M) : Integrable (fun x => B x a * C x a) (mixtureGibbsLaw μ β J) := by
    have hc : Continuous (fun x => B x a * C x a) := by
      have hb := (contDiff_vector_coordinate hB a).continuous
      have hd := (contDiff_vector_coordinate hC a).continuous
      fun_prop
    exact integrable_gibbs_of_continuous hN β (potential_continuous μ J) hc
  rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change (∑ a : Fin M, B x a * C x a) = inner ℝ (B x) (C x)
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp [RCLike.inner_apply, mul_comm]

lemma vectorL2_norm_sq (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) :
    ‖vectorL2 hN μ J β B hB‖^2 = ∫ x, ‖B x‖^2 ∂mixtureGibbsLaw μ β J := by
  rw [← real_inner_self_eq_norm_sq, vectorL2_inner]
  simp_rw [real_inner_self_eq_norm_sq]

lemma centeredL2_variance (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) :
    ‖centeredL2 hN μ J β B hB‖^2 =
      (∫ x, ‖B x‖^2 ∂mixtureGibbsLaw μ β J) - ‖mean μ J β B‖^2 := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  let _ := gibbsLaw_probability hN β (potential_continuous μ J)
  rw [centeredL2, vectorL2_norm_sq]
  exact MeasureCovariance.integral_norm_sub_mean_sq _ B
    (memLp_sphereSupported_continuous _ (gibbsLaw_support hN β (fieldOfMixture μ J)) hB.continuous 2)

lemma centeredL2_norm_le_one (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, OnSphere x → ‖B x‖ ≤ 1) : ‖centeredL2 hN μ J β B hBs‖ ≤ 1 := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  let _ := gibbsLaw_probability hN β (potential_continuous μ J)
  have hi : Integrable (fun x => ‖B x‖^2) (mixtureGibbsLaw μ β J) :=
    (memLp_sphereSupported_continuous _ (gibbsLaw_support hN β (fieldOfMixture μ J)) hBs.continuous 2).integrable_norm_pow'
  have hm := integral_mono_ae hi (integrable_const (1 : ℝ)) (by
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
    have hb := hB x hx
    nlinarith [norm_nonneg (B x)])
  simp only [integral_const, probReal_univ, one_smul] at hm
  have hv := centeredL2_variance hN μ J β B hBs
  nlinarith [sq_nonneg ‖mean μ J β B‖, norm_nonneg (centeredL2 hN μ J β B hBs)]

lemma centeredL2_spectrally_centered (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B)
    (a : Fin M) :
    (normalizedSphericalSpectralData hN β (potential μ J) (potential_continuous μ J)).toSemigroupData.Centered
      (centeredL2 (show 1 ≤ N by omega) μ J β B hB a) := by
  let D := normalizedSphericalSpectralData hN β (potential μ J) (potential_continuous μ J)
  apply (D.centered_iff_integral_zero ((fieldOfMixture_contDiff μ J).of_le (by simp)) _).mpr
  have hae := gibbsToL2_coe (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)
    (fun x => centered μ J β B x a) (contDiff_vector_coordinate (centered_contDiff μ J β hB) a).continuous
  calc
    _ = ∫ x, centered μ J β B x a ∂mixtureGibbsLaw μ β J := integral_congr_ae hae
    _ = 0 := centered_coordinate_integral (show 1 ≤ N by omega) μ J β hB a

lemma centered_coordinate_energy (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (B : Vector N → Vector M) (a : Fin M) :
    dirichletEnergy N β H (fun x => centered μ J β B x a) =
      dirichletEnergy N β H (fun x => B x a) := by
  simp only [dirichletEnergy_eq_integral_norm_sq]
  congr 1
  funext x
  congr 1
  unfold surfaceGradient gradient
  rw [show (fun y => centered μ J β B y a) = (fun y => B y a - mean μ J β B a) from rfl,
    fderiv_sub_const]

lemma centered_vector_energy (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) :
    vectorDirichletEnergy β (potential μ J) (centered μ J β B) =
      vectorDirichletEnergy β (potential μ J) B := by
  unfold vectorDirichletEnergy
  exact Finset.sum_congr rfl (fun a _ => centered_coordinate_energy hN β _ μ J B a)

lemma mean_norm_le_one (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) {B : Vector N → Vector M} (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, OnSphere x → ‖B x‖ ≤ 1) : ‖mean μ J β B‖ ≤ 1 := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  have hi : Integrable B (mixtureGibbsLaw μ β J) :=
    integrable_gibbs_of_continuous_vector hN β (potential_continuous μ J) hBs.continuous
  have hm := integral_mono_ae hi.norm (integrable_const (1 : ℝ)) (by
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
    exact hB x hx)
  simp only [integral_const, probReal_univ, one_smul] at hm
  exact (norm_integral_le_integral_norm _).trans hm

lemma centeredL2_inner (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (B C : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (hC : ContDiff ℝ 1 C) :
    inner ℝ (centeredL2 hN μ J β B hB) (centeredL2 hN μ J β C hC) =
      (∫ x, inner ℝ (B x) (C x) ∂mixtureGibbsLaw μ β J) -
        inner ℝ (mean μ J β B) (mean μ J β C) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  let _ := gibbsLaw_probability hN β (potential_continuous μ J)
  have hscalar (a : Fin M) :
      (∫ x, centered μ J β B x a * centered μ J β C x a ∂mixtureGibbsLaw μ β J) =
        (∫ x, B x a * C x a ∂mixtureGibbsLaw μ β J) - mean μ J β B a * mean μ J β C a := by
    have hmemB : MemLp (fun x => B x a) 2 (mixtureGibbsLaw μ β J) :=
      memLp_gibbs_of_continuous hN β (potential_continuous μ J) (contDiff_vector_coordinate hB a).continuous
    have hmemC : MemLp (fun x => C x a) 2 (mixtureGibbsLaw μ β J) :=
      memLp_gibbs_of_continuous hN β (potential_continuous μ J) (contDiff_vector_coordinate hC a).continuous
    have hs := covariance_eq_sub hmemB hmemC
    unfold covariance at hs
    rw [mean_coordinate hN μ J β hB.continuous a,
      mean_coordinate hN μ J β hC.continuous a] at hs
    exact hs
  have hcoord (B C : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (hC : ContDiff ℝ 1 C) (a : Fin M) :
      inner ℝ (vectorL2 hN μ J β B hB a) (vectorL2 hN μ J β C hC a) =
        ∫ x, B x a * C x a ∂mixtureGibbsLaw μ β J :=
    gibbsToL2_inner hN β (potential μ J) (potential_continuous μ J) _ _
      (contDiff_vector_coordinate hB a).continuous (contDiff_vector_coordinate hC a).continuous
  have hraw : (∑ a : Fin M, ∫ x, B x a * C x a ∂mixtureGibbsLaw μ β J) =
      ∫ x, inner ℝ (B x) (C x) ∂mixtureGibbsLaw μ β J := by
    have h := vectorL2_inner hN μ J β B C hB hC
    rw [PiLp.inner_apply] at h
    simpa only [hcoord] using h
  rw [centeredL2, centeredL2, PiLp.inner_apply]
  simp_rw [hcoord, hscalar]
  rw [Finset.sum_sub_distrib, hraw, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp [RCLike.inner_apply, mul_comm]

lemma centered_spin_norm_le_one (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    ‖centeredL2 hN μ J β spin (spin_contDiff.of_le (by simp))‖ ≤ 1 :=
  centeredL2_norm_le_one hN μ J β spin (spin_contDiff.of_le (by simp))
    (fun x hx => (spin_norm hN x hx).le)

/-- A lower bound on actual Gibbs spin alignment gives its literal
centered Hilbert alignment, with the true magnetization error. -/
theorem centered_spin_alignment_lower (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, OnSphere x → ‖B x‖ ≤ 1) {a : ℝ}
    (ha : a ≤ ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β J) :
    a - ‖mean μ J β spin‖ ≤
      inner ℝ (centeredL2 hN μ J β spin (spin_contDiff.of_le (by simp)))
        (centeredL2 hN μ J β B hBs) := by
  rw [centeredL2_inner]
  have hCS := real_inner_le_norm (mean μ J β spin) (mean μ J β B)
  have hMean := mean_norm_le_one hN μ J β hBs hB
  have hBound : inner ℝ (mean μ J β spin) (mean μ J β B) ≤ ‖mean μ J β spin‖ := by
    nlinarith [norm_nonneg (mean μ J β spin)]
  linarith

end SlowEquilibration.SphericalCenteredObservables
