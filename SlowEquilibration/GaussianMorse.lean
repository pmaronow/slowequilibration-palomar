-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGlobalKacRice
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Almost-sure regularity of the actual Gaussian zero set, obtained by marking
the degenerate zeros in the proved full-coefficient Kac--Rice formula. -/

@[expose] public section

namespace SlowEquilibration.GaussianLocalCoordinates

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianRegression
open scoped ENNReal Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]

theorem regular_zeros_ae
    (Gamma : U → E →L[ℝ] U) (s : Set U) (hs : IsOpen s)
    (hG : ContDiffOn ℝ 1 Gamma s) (hSurj : ∀ u ∈ s, Surjective (Gamma u)) :
    ∀ᵐ z ∂stdGaussian E, ∀ u ∈ s, Gamma u z = 0 →
      (spatialJacobian Gamma z u).det ≠ 0 := by
  classical
  let D : E × U → U →L[ℝ] U := fun p => (fderiv ℝ Gamma p.2).flip p.1
  have hD : Measurable D := by
    have hflip : Measurable fun p : E × U => (fderiv ℝ Gamma p.2).flip :=
      (ContinuousLinearMap.flipₗᵢ ℝ U E U).continuous.measurable.comp
        ((measurable_fderiv ℝ Gamma).comp measurable_snd)
    exact (show Continuous (fun p : (E →L[ℝ] U →L[ℝ] U) × E => p.1 p.2) by
      fun_prop).measurable.comp (hflip.prodMk measurable_fst)
  let psi : E → U → ℝ≥0∞ := fun z u => if (D (z, u)).det = 0 then 1 else 0
  have hm : Measurable fun p : E × U => psi p.1 p.2 := by
    exact Measurable.ite ((measurableSet_singleton (0 : ℝ)).preimage
      (ContinuousLinearMap.continuous_det.measurable.comp hD)) measurable_const measurable_const
  have he (z : E) (u : U) (hu : u ∈ s) : spatialJacobian Gamma z u = D (z, u) := by
    have hd := ((hG.contDiffAt (hs.mem_nhds hu)).differentiableAt_one).hasFDerivAt
    simpa only [spatialJacobian, D, ContinuousLinearMap.comp_zero, zero_add] using
      (hd.clm_apply (hasFDerivAt_const z u)).fderiv
  have hk := marked_kacRice Gamma s hs hG hSurj psi hm
  have hz : (∫⁻ z, zeroCount Gamma s psi z ∂stdGaussian E) = 0 := by
    rw [hk.2]
    calc
      _ = ∫⁻ u in s, (0 : ℝ≥0∞) := by
        apply setLIntegral_congr_fun hs.measurableSet
        intro u hu
        dsimp only
        have hi : (∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
            ∂regressionKernel (Gamma u) 0) = 0 := by
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards [] with z
          rw [he z u hu]
          by_cases hd : (D (z, u)).det = 0 <;> simp [psi, hd]
        rw [hi, mul_zero]
      _ = 0 := by simp
  have hzero := (lintegral_eq_zero_iff' hk.1).mp hz
  filter_upwards [hzero] with z hz
  intro u hu hgu hd
  have hv := ENNReal.tsum_eq_zero.mp hz ⟨u, hu, hgu⟩
  have hd' : (D (z, u)).det = 0 := by rwa [← he z u hu]
  simp [psi, hd'] at hv

/-- A compact set of regular zeros is finite, using the actual local inverse
theorem to isolate each zero. The map need only be smooth on an open domain. -/
theorem compact_set_of_regular_zeros_finite
    (f : U → U) (s : Set U) (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (K : Set U) (hK : IsCompact K) (hKs : K ⊆ s)
    (hzero : ∀ u ∈ K, f u = 0) (hreg : ∀ u ∈ K, (fderiv ℝ f u).det ≠ 0) :
    K.Finite := by
  apply hK.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro u hu
  obtain ⟨v, hv, huv, _, hinj⟩ := WeightedAreaFormula.regular_inverse_neighborhood
    f s hs hf u ⟨hKs hu, hreg u hu⟩
  refine ⟨v, hv, ?_⟩
  ext w
  constructor
  · intro hw
    exact hinj hw.1 huv ((hzero w hw.2).trans (hzero u hu).symm)
  · rintro rfl
    exact ⟨huv, hu⟩

end
end SlowEquilibration.GaussianLocalCoordinates
