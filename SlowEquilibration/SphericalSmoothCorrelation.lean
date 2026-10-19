-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalObservableDisplacement

/-! The exact stationary identity of `lem:sp-trap`(1), on the actual
smooth coordinates and physical two-time diffusion law. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalPhysicalSpectral

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalForm
open SphericalLaplaceIdentification
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N M : ℕ}

/-- The ordinary Gibbs L² class of a literal smooth coordinate. -/
def smoothCoordinateL2 (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (a : Fin M) :
    SphericalL2Semigroup.Space μ J β :=
  gibbsToL2 hN β (potential μ J) (potential_continuous μ J)
    (fun x => B x a) (contDiff_vector_coordinate hB a).continuous

theorem smooth_stationary_displacement_identity (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (t : ℝ≥0) :
    (∫ z, ‖B z.2 - B z.1‖ ^ 2 ∂twoTimeLaw μ J β t) =
      2 * ∑ a : Fin M, inner ℝ (smoothCoordinateL2 hN μ J β B hB a)
        (smoothCoordinateL2 hN μ J β B hB a -
          SphericalL2Semigroup.P hN μ J β t (smoothCoordinateL2 hN μ J β B hB a)) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  let f := smoothCoordinateL2 hN μ J β B hB
  have hae (a : Fin M) : f a =ᵐ[mixtureGibbsLaw μ β J] (fun x => B x a) :=
    gibbsToL2_coe hN β (potential μ J) (potential_continuous μ J)
      (fun x => B x a) (contDiff_vector_coordinate hB a).continuous
  have hpair (a : Fin M) : ∀ᵐ z ∂twoTimeLaw μ J β t,
      f a z.1 = B z.1 a ∧ f a z.2 = B z.2 a := by
    have hf : ∀ᵐ z ∂twoTimeLaw μ J β t, f a z.1 = B z.1 a := by
      apply ae_of_ae_map (μ := twoTimeLaw μ J β t)
        (p := fun x => f a x = B x a) measurable_fst.aemeasurable
      change ∀ᵐ y ∂(twoTimeLaw μ J β t).fst, _
      rw [twoTimeLaw_first_marginal hN μ J β t]
      exact hae a
    have hs : ∀ᵐ z ∂twoTimeLaw μ J β t, f a z.2 = B z.2 a := by
      apply ae_of_ae_map (μ := twoTimeLaw μ J β t)
        (p := fun x => f a x = B x a) measurable_snd.aemeasurable
      change ∀ᵐ y ∂(twoTimeLaw μ J β t).snd, _
      rw [twoTimeLaw_second_marginal hN μ J β t]
      exact hae a
    exact hf.and hs
  have heq : (∫ z, ‖B z.2 - B z.1‖ ^ 2 ∂twoTimeLaw μ J β t) =
      ∫ z, ∑ a : Fin M, (f a z.2 - f a z.1) ^ 2 ∂twoTimeLaw μ J β t := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hpair] with z hz
    simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    exact Finset.sum_congr rfl (fun a _ => by rw [(hz a).1, (hz a).2])
  have hi (a : Fin M) : Integrable (fun z : Vector N × Vector N => (f a z.2 - f a z.1)^2)
      (twoTimeLaw μ J β t) :=
    StationaryCoupling.difference_square_integrable (mixtureGibbsLaw μ β J)
      (mixedTransitionKernel μ J β t) (mixedTransitionKernel_gibbs_invariant hN μ J β t) (f a)
  rw [heq, integral_finsetSum Finset.univ (fun a _ => hi a), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => twoTime_displacement hN μ J β t (f a))

end SlowEquilibration.SphericalPhysicalSpectral
