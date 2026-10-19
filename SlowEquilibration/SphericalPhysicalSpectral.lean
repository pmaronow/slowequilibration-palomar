-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpectral
public import SlowEquilibration.SphericalLaplaceIdentification
public import SlowEquilibration.SemigroupLaplaceSpectral
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-!
# The actual physical Langevin spectral calculus

The literal Brownian SDE transition is identified with the diagonal operator
of the genuine ordered spherical form eigenbasis. Its two-time stationary
law uses the actual transition kernel and the normalized actual Gibbs law.
-/

noncomputable section
namespace SlowEquilibration.SphericalPhysicalSpectral

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalLaplaceIdentification
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {hN : 2 ≤ N} {μ : FiniteMixture} {J : Disorder N μ.maxDegree} {β : ℝ}

/-- A genuine eigenvector of the actual spherical form has the proved
physical Langevin multiplier. -/
theorem P_basis (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) (j : ℕ) :
    SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t (D.basis j) =
      Real.exp (-(t : ℝ) * D.eigenvalue j) • D.basis j := by
  have he : (SphericalLaplace.data (show 1 ≤ N by omega) μ J β).operator (D.basis j) =
      D.resolventEigenvalue j • D.basis j := by
    change SphericalLaplace.R (show 1 ≤ N by omega) μ J β (D.basis j) = _
    rw [R_eq_form]
    exact D.eigen j
  exact (SphericalLaplace.data (show 1 ≤ N by omega) μ J β).P_laplace_eigen
    (D.bounds j).1.ne' he t

/-- The actual physical transition has the convergent genuine eigenbasis
series. Its multiplier is derived from its actual Laplace resolvent. -/
theorem P_hasSum (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) (f : SphericalL2Semigroup.Space μ J β) :
    HasSum (fun j => (Real.exp (-(t : ℝ) * D.eigenvalue j) *
      inner ℝ (D.basis j) f) • D.basis j)
      (SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t f) := by
  apply (SphericalLaplace.data (show 1 ≤ N by omega) μ J β).P_hasSum_eigenbasis
    D.basis D.resolventEigenvalue (fun j => (D.bounds j).1.ne')
  intro j
  change SphericalLaplace.R (show 1 ≤ N by omega) μ J β (D.basis j) = _
  rw [R_eq_form]
  exact D.eigen j

theorem coefficient_P (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) (f : SphericalL2Semigroup.Space μ J β) (j : ℕ) :
    D.toSemigroupData.coefficient (SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t f) j =
      Real.exp (-(t : ℝ) * D.eigenvalue j) * D.toSemigroupData.coefficient f j := by
  change inner ℝ (D.basis j) (SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t f) = _
  rw [← (SphericalL2Semigroup.P_isSymmetric (show 1 ≤ N by omega) μ J β t).apply_clm,
    P_basis D t j, inner_smul_left, conj_trivial]
  rfl

/-- Exact equality of the literal physical Langevin operator with the
diagonal operator of the actual independently constructed spherical form. -/
theorem P_eq_diagonal (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) :
    SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t = D.toSemigroupData.P t := by
  apply ContinuousLinearMap.ext
  intro f
  apply D.toSemigroupData.coefficient_injective
  intro j
  exact (coefficient_P D t f j).trans (D.toSemigroupData.coefficient_P t f j).symm

theorem correlation_hasSum (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) (f : SphericalL2Semigroup.Space μ J β) :
    HasSum (fun j => Real.exp (-(t : ℝ) * D.eigenvalue j) *
      (D.toSemigroupData.coefficient f j)^2)
      (inner ℝ f (SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t f)) := by
  rw [P_eq_diagonal D]
  exact D.toSemigroupData.correlation_hasSum t f

namespace StationaryCoupling

variable {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
  (K : Kernel E E) [IsMarkovKernel K] (hInv : K ∘ₘ π = π)

/-- Genuine two-time Markov law with the proved stationary initial law. -/
def law : Measure (E × E) := π ⊗ₘ K

instance law_probability : IsProbabilityMeasure (law π K) := by
  unfold law
  infer_instance

theorem fst_preserving : MeasurePreserving Prod.fst (law π K) π :=
  ⟨measurable_fst, Measure.fst_compProd π K⟩

include hInv in
theorem snd_preserving : MeasurePreserving Prod.snd (law π K) π :=
  ⟨measurable_snd, (Measure.snd_compProd π K).trans hInv⟩

theorem square_first_integral (U : Lp ℝ 2 π) :
    (∫ q, U q.1 ^ 2 ∂law π K) = ‖U‖ ^ 2 := by
  have h := integral_map (fst_preserving π K).aemeasurable
    (f := fun x => U x ^ 2) ((Lp.stronglyMeasurable U).pow 2).aestronglyMeasurable
  rw [(fst_preserving π K).map_eq] at h
  rw [← h, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp only [RCLike.inner_apply, conj_trivial, pow_two])

include hInv in
theorem square_second_integral (U : Lp ℝ 2 π) :
    (∫ q, U q.2 ^ 2 ∂law π K) = ‖U‖ ^ 2 := by
  have h := integral_map (snd_preserving π K hInv).aemeasurable
    (f := fun x => U x ^ 2) ((Lp.stronglyMeasurable U).pow 2).aestronglyMeasurable
  rw [(snd_preserving π K hInv).map_eq] at h
  rw [← h, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp only [RCLike.inner_apply, conj_trivial, pow_two])

include hInv in
theorem correlation_integrable (U V : Lp ℝ 2 π) :
    Integrable (fun q : E × E => U q.1*V q.2) (law π K) := by
  have hU := (Lp.memLp U).comp_measurePreserving (fst_preserving π K)
  have hV := (Lp.memLp V).comp_measurePreserving (snd_preserving π K hInv)
  exact (hU.fun_mul hV : MemLp (fun q => U q.1*V q.2) 1 (law π K)).integrable (by norm_num)

/-- The actual two-time correlation equals the actual stationary-kernel
L² operator pairing for arbitrary square-integrable representatives. -/
theorem correlation (U V : Lp ℝ 2 π) :
    (∫ q, U q.1*V q.2 ∂law π K) =
      inner ℝ U (SphericalL2Semigroup.StationaryKernel.operator π K hInv V) := by
  have hF := Measure.integral_compProd (correlation_integrable π K hInv U V)
  change (∫ q, U q.1*V q.2 ∂law π K) = _ at hF
  rw [hF, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SphericalL2Semigroup.StationaryKernel.operator_ae π K hInv V] with x hx
  rw [integral_const_mul]
  simp only [hx, SphericalL2Semigroup.StationaryKernel.average, RCLike.inner_apply, conj_trivial, mul_comm]

include hInv in
theorem difference_square_integrable (U : Lp ℝ 2 π) :
    Integrable (fun q : E × E => (U q.2-U q.1)^2) (law π K) := by
  have hU := (Lp.memLp U).comp_measurePreserving (fst_preserving π K)
  have hV := (Lp.memLp U).comp_measurePreserving (snd_preserving π K hInv)
  exact (hV.sub hU).integrable_sq

/-- The true stationary displacement expectation equals twice the
semigroup correlation loss, by the actual equality of both marginals. -/
theorem difference_square (U : Lp ℝ 2 π) :
    (∫ q, (U q.2-U q.1)^2 ∂law π K) =
      2*inner ℝ U (U-SphericalL2Semigroup.StationaryKernel.operator π K hInv U) := by
  have hi₁ : Integrable (fun q : E × E => U q.1^2) (law π K) :=
    ((Lp.memLp U).comp_measurePreserving (fst_preserving π K)).integrable_sq
  have hi₂ : Integrable (fun q : E × E => U q.2^2) (law π K) :=
    ((Lp.memLp U).comp_measurePreserving (snd_preserving π K hInv)).integrable_sq
  have hic := (correlation_integrable π K hInv U U).const_mul 2
  calc
    _ = ∫ q, U q.2^2+U q.1^2-2*(U q.1*U q.2) ∂law π K := by
      apply integral_congr_ae
      exact ae_of_all _ (fun q => by ring)
    _ = (∫ q, U q.2^2 ∂law π K)+(∫ q, U q.1^2 ∂law π K)-
      2*(∫ q, U q.1*U q.2 ∂law π K) := by
      have hs := integral_sub (hi₂.add hi₁) hic
      simp only [Pi.add_apply] at hs
      rw [integral_add hi₂ hi₁, integral_const_mul] at hs
      simpa only [Pi.add_apply, Pi.sub_apply, Function.comp_def] using hs
    _ = _ := by
      rw [square_first_integral, square_second_integral π K hInv, correlation π K hInv,
        inner_sub_right, real_inner_self_eq_norm_sq]
      ring

end StationaryCoupling

/-- The literal stationary two-time law of the genuine mixed Langevin
transition. It uses the actual normalized Gibbs law and actual Brownian
transition kernel, without a supplied coupling. -/
def twoTimeLaw (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (t : ℝ≥0) : Measure (Vector N × Vector N) :=
  StationaryCoupling.law (mixtureGibbsLaw μ β J) (mixedTransitionKernel μ J β t)

theorem twoTimeLaw_probability (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (twoTimeLaw μ J β t) := by
  have := mixtureGibbsLaw_probability hN μ β J
  exact StationaryCoupling.law_probability _ _

theorem twoTimeLaw_first_marginal (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    (twoTimeLaw μ J β t).fst = mixtureGibbsLaw μ β J := by
  have := mixtureGibbsLaw_probability hN μ β J
  exact (StationaryCoupling.fst_preserving (mixtureGibbsLaw μ β J)
    (mixedTransitionKernel μ J β t)).map_eq

theorem twoTimeLaw_second_marginal (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    (twoTimeLaw μ J β t).snd = mixtureGibbsLaw μ β J := by
  have := mixtureGibbsLaw_probability hN μ β J
  exact (StationaryCoupling.snd_preserving (mixtureGibbsLaw μ β J)
    (mixedTransitionKernel μ J β t) (mixedTransitionKernel_gibbs_invariant hN μ J β t)).map_eq

/-- The true stationary two-time correlation identity for all genuine Gibbs
L² observables. Products are integrable by the actual marginals and Hölder. -/
theorem twoTime_correlation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0)
    (f g : SphericalL2Semigroup.Space μ J β) :
    (∫ q, f q.1*g q.2 ∂twoTimeLaw μ J β t) =
      inner ℝ f (SphericalL2Semigroup.P hN μ J β t g) := by
  have := mixtureGibbsLaw_probability hN μ β J
  exact StationaryCoupling.correlation (mixtureGibbsLaw μ β J)
    (mixedTransitionKernel μ J β t) (mixedTransitionKernel_gibbs_invariant hN μ J β t) f g

theorem twoTime_displacement (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0)
    (f : SphericalL2Semigroup.Space μ J β) :
    (∫ q, (f q.2-f q.1)^2 ∂twoTimeLaw μ J β t) =
      2*inner ℝ f (f-SphericalL2Semigroup.P hN μ J β t f) := by
  have := mixtureGibbsLaw_probability hN μ β J
  exact StationaryCoupling.difference_square (mixtureGibbsLaw μ β J)
    (mixedTransitionKernel μ J β t) (mixedTransitionKernel_gibbs_invariant hN μ J β t) f

theorem correlation_loss_hasSum
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) (f : SphericalL2Semigroup.Space μ J β) :
    HasSum (fun j => (1-Real.exp (-(t : ℝ)*D.eigenvalue j))*
      (D.toSemigroupData.coefficient f j)^2)
      (inner ℝ f (f-SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t f)) := by
  convert (D.toSemigroupData.parseval_hasSum f).sub (correlation_hasSum D t f) using 1
  · funext j
    ring
  · rw [inner_sub_right, real_inner_self_eq_norm_sq]

/-- The genuine completed form value, with the literal mixed Gibbs Hilbert
space named explicitly so that all physical operator expressions share it. -/
def formValue (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (u : sphericalSobolevGraph hN β (potential μ J) (potential_continuous μ J)) :
    SphericalL2Semigroup.Space μ J β :=
  sphericalEnergyL2Map hN β (potential μ J) (potential_continuous μ J) u

/-- The physical semigroup correlation loss is controlled by the literal
completed spherical gradient energy, proved by actual convergent Parseval. -/
theorem correlation_loss_energy_le
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)) :
    inner ℝ (formValue (show 1 ≤ N by omega) μ J β u)
      (formValue (show 1 ≤ N by omega) μ J β u -
        SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t
          (formValue (show 1 ≤ N by omega) μ J β u)) ≤
      (t : ℝ)*sphericalCompletedDirichlet (show 1 ≤ N by omega) β (potential μ J)
        (potential_continuous μ J) u u := by
  let f := formValue (show 1 ≤ N by omega) μ J β u
  have hHC : ContDiff ℝ 1 (potential μ J) := (fieldOfMixture_contDiff μ J).of_le (by simp)
  have hf : D.toSemigroupData.FormDomain f := (D.formDomain_iff hHC f).mp ⟨u, rfl⟩
  rw [← D.energy_eq_completed hHC u]
  apply hasSum_le _ (correlation_loss_hasSum D t f) (hf.hasSum.mul_left (t : ℝ))
  intro j
  have h : 1-Real.exp (-(t : ℝ)*D.eigenvalue j) ≤ (t : ℝ)*D.eigenvalue j := by
    linarith [Real.add_one_le_exp (-(t : ℝ)*D.eigenvalue j)]
  change (1-Real.exp (-(t : ℝ)*D.eigenvalue j))*
    (D.toSemigroupData.coefficient f j)^2 ≤
    (t : ℝ)*(D.eigenvalue j*(D.toSemigroupData.coefficient f j)^2)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h (sq_nonneg (D.toSemigroupData.coefficient f j))

/-- The physical L² displacement has the manuscript's energy constant. -/
theorem semigroup_displacement_energy_le
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)) :
    ‖formValue (show 1 ≤ N by omega) μ J β u -
      SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t
        (formValue (show 1 ≤ N by omega) μ J β u)‖ ^ 2 ≤
      (t : ℝ)*sphericalCompletedDirichlet (show 1 ≤ N by omega) β (potential μ J)
        (potential_continuous μ J) u u := by
  let f := formValue (show 1 ≤ N by omega) μ J β u
  have hHC : ContDiff ℝ 1 (potential μ J) := (fieldOfMixture_contDiff μ J).of_le (by simp)
  have hf : D.toSemigroupData.FormDomain f := (D.formDomain_iff hHC f).mp ⟨u, rfl⟩
  rw [P_eq_diagonal D, ← D.energy_eq_completed hHC u]
  exact D.toSemigroupData.displacement_energy_le t f hf

/-- The true physical stationary displacement estimate, including the
factor 2 in the manuscript, for the actual completed energy domain. -/
theorem stationary_displacement_energy_le
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0)
    (u : sphericalSobolevGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)) :
    (∫ q, ((formValue (show 1 ≤ N by omega) μ J β u) q.2-
      (formValue (show 1 ≤ N by omega) μ J β u) q.1)^2
      ∂twoTimeLaw μ J β t) ≤
      2*(t : ℝ)*sphericalCompletedDirichlet (show 1 ≤ N by omega) β (potential μ J)
        (potential_continuous μ J) u u := by
  rw [twoTime_displacement (show 1 ≤ N by omega)]
  have h := mul_le_mul_of_nonneg_left (correlation_loss_energy_le D t u) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using h

end SlowEquilibration.SphericalPhysicalSpectral
