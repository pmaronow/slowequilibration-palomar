-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SymmetricGaussianCovariance
public import SlowEquilibration.GaussianAffineDeterminantAllDimensions

/-! Normalized determinant moments under the actual arbitrary Gaussian
matrix law satisfying the manuscript's trace covariance bound. -/

@[expose] public section
namespace SlowEquilibration.GaussianMatrixMomentLaw
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK SpectralTraceLipschitz
open SymmetricGaussianCovariance GaussianAffineDeterminant
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ}

def rawDet (C : GOEAsymptotics.GaussianMatrix (n+1)) (k : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  |(k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)-gaussianToMatrix (C+A)).det|

def logClipped (C : GOEAsymptotics.GaussianMatrix (n+1)) (k ρ : ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  ∑ i, clippedLog k ρ (matrixOrderedEigenvalues (C+A) i)

lemma rawDet_measurable (C : GOEAsymptotics.GaussianMatrix (n+1)) (k : ℝ) :
    Measurable (rawDet C k) := by
  have h : Measurable (fun A : GOEAsymptotics.GaussianMatrix (n+1) => gaussianToMatrix (C+A)) :=
    (gaussianToMatrix_measurable (n+1)).comp (measurable_const.add measurable_id)
  unfold rawDet
  fun_prop

lemma logClipped_measurable (C : GOEAsymptotics.GaussianMatrix (n+1)) (k ρ : ℝ) :
    Measurable (logClipped C k ρ) := by
  unfold logClipped clippedLog
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.sub (((measurable_pi_apply i).comp
    (matrixOrderedEigenvalues_measurable _)).comp (measurable_const.add measurable_id))).abs.max
      measurable_const |>.log

structure MomentBounds (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1)))
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (k ρ : ℝ) (bound : ℝ → ℝ) : Prop where
  integrable : Integrable (rawDet C k) μ
  expectation_pos : 0 < ∫ A, rawDet C k A ∂μ
  raw_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun A => (rawDet C k A/(∫ B, rawDet C k B ∂μ))^r) μ
  clipped_integrable : ∀ r : ℝ, 0 ≤ r → Integrable
    (fun A => (Real.exp (logClipped C k ρ A)/(∫ B, rawDet C k B ∂μ))^r) μ
  ordered : ∀ r : ℝ, 0 ≤ r →
    (∫ A, (rawDet C k A/(∫ B, rawDet C k B ∂μ))^r ∂μ) ≤
      ∫ A, (Real.exp (logClipped C k ρ A)/(∫ B, rawDet C k B ∂μ))^r ∂μ
  upper : ∀ r : ℝ, 0 ≤ r →
    (∫ A, (Real.exp (logClipped C k ρ A)/(∫ B, rawDet C k B ∂μ))^r ∂μ) ≤ bound r

lemma momentBounds_of_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1)))
    (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (hμ : (SYK.standardGaussianMeasureOnEuclidean ι).map W = μ)
    (k ρ : ℝ) (bound : ℝ → ℝ)
    (hD : Integrable (absoluteDet C W k) (SYK.standardGaussianMeasureOnEuclidean ι))
    (hpos : 0 < ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι)
    (hmom : ∀ r : ℝ, 0 ≤ r →
      Integrable (fun z => (absoluteDet C W k z /
        (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
        (SYK.standardGaussianMeasureOnEuclidean ι) ∧
      Integrable (fun z => (Real.exp (clippedTrace C W k ρ z) /
        (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r)
        (SYK.standardGaussianMeasureOnEuclidean ι) ∧
      (∫ z, (absoluteDet C W k z /
        (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      (∫ z, (Real.exp (clippedTrace C W k ρ z) /
        (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ∧
      (∫ z, (Real.exp (clippedTrace C W k ρ z) /
        (∫ w, absoluteDet C W k w ∂SYK.standardGaussianMeasureOnEuclidean ι))^r
        ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ bound r) :
    MomentBounds μ C k ρ bound := by
  have hW := W.continuous.measurable
  have hd := rawDet_measurable C k
  have hy := (logClipped_measurable C k ρ).exp
  have he : (∫ A, rawDet C k A ∂μ) =
      ∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι := by
    rw [← hμ, integral_map hW.aemeasurable hd.aestronglyMeasurable]
    rfl
  have hraw (r : ℝ) : Measurable (fun A => (rawDet C k A/(∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι))^r) :=
    (hd.div_const _).pow_const r
  have hclip (r : ℝ) : Measurable (fun A => (Real.exp (logClipped C k ρ A)/(∫ z, absoluteDet C W k z ∂SYK.standardGaussianMeasureOnEuclidean ι))^r) :=
    (hy.div_const _).pow_const r
  refine ⟨?_, by rw [he]; exact hpos, ?_, ?_, ?_, ?_⟩
  · rw [← hμ]
    exact (integrable_map_measure hd.aestronglyMeasurable hW.aemeasurable).mpr hD
  · intro r hr
    rw [he, ← hμ, integrable_map_measure (hraw r).aestronglyMeasurable hW.aemeasurable]
    exact (hmom r hr).1
  · intro r hr
    rw [he, ← hμ, integrable_map_measure (hclip r).aestronglyMeasurable hW.aemeasurable]
    exact (hmom r hr).2.1
  · intro r hr
    rw [he, ← hμ, integral_map hW.aemeasurable (hraw r).aestronglyMeasurable,
      integral_map hW.aemeasurable (hclip r).aestronglyMeasurable]
    exact (hmom r hr).2.2.1
  · intro r hr
    rw [he, ← hμ, integral_map hW.aemeasurable (hclip r).aestronglyMeasurable]
    exact (hmom r hr).2.2.2

/-- Full all-dimension moment conclusion for arbitrary genuine Gaussian
matrix laws. The constant is uniform in both dimensions, covariance and shift;
the source upper bound on k is not needed. -/
theorem normalized_moments_all_dimensions {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N n : ℕ), n+1 ≤ N →
      ∀ (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ],
      (∫ A, A ∂μ = 0) → (∀ᵐ A ∂μ, ∀ i j, A i j = A j i) →
      (∀ M : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, M i j = M j i) →
        Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
          (2*b/N)*Matrix.trace (entries M * entries M)) →
      ∀ C : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, C i j = C j i) →
      ‖gaussianMatrixCLM C‖ ≤ g/4 → ∀ k : ℝ, 2*Real.sqrt b+g ≤ k →
      MomentBounds μ C k (g/2) (fun r => K^r*Real.exp (K*r^2)) := by
  obtain ⟨K, hK, hall⟩ := covarianceScale_normalized_moments_all_dimensions hb hg
  refine ⟨K, hK, ?_⟩
  intro N n hN μ _ hmean hSym hvar C hC hCop k hk
  obtain ⟨W, hW, hWs, hμ⟩ := exists_realization_of_trace_variance μ hmean hSym hb.le hvar
  have h := hall N n hN C W hC hWs hW hCop k hk
  exact momentBounds_of_realization μ C W hμ k (g/2) _ h.integrable h.expectation_pos
    (fun r hr => ⟨h.raw_integrable r hr, h.clipped_integrable r hr, h.ordered r hr, h.bound r hr⟩)

/-- The sharp large-N constant holds with one dimension threshold chosen
before every Gaussian covariance, both matrix dimensions and all shifts. -/
theorem normalized_moments_sharp_eventually {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n+1 ≤ N →
      ∀ (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ],
      (∫ A, A ∂μ = 0) → (∀ᵐ A ∂μ, ∀ i j, A i j = A j i) →
      (∀ M : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, M i j = M j i) →
        Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
          (2*b/N)*Matrix.trace (entries M * entries M)) →
      ∀ C : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, C i j = C j i) →
      ‖gaussianMatrixCLM C‖ ≤ g/4 → ∀ k : ℝ, 2*Real.sqrt b+g ≤ k →
      MomentBounds μ C k (g/2) (fun r => (2:ℝ)^r*Real.exp ((4*b/g^2)*r^2)) := by
  filter_upwards [covarianceScale_normalized_moments_eventually hb hg] with N hall
  intro n hN μ _ hmean hSym hvar C hC hCop k hk
  obtain ⟨W, hW, hWs, hμ⟩ := exists_realization_of_trace_variance μ hmean hSym hb.le hvar
  have h := hall n hN (Fin (Module.finrank ℝ (GOEAsymptotics.GaussianMatrix (n+1))))
    C W hC hWs hW hCop k hk
  exact momentBounds_of_realization μ C W hμ k (g/2) _ h.integrable h.expectation_pos
    (fun r hr => ⟨h.raw_integrable r hr, h.clipped_integrable r hr, h.ordered r hr, h.bound r hr⟩)

end
end SlowEquilibration.GaussianMatrixMomentLaw
