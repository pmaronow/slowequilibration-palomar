module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalVectorSpectral
public import SlowEquilibration.C1SphericalGraph
public import SlowEquilibration.SphericalNormalizedBasis

@[expose] public section

/-! # Stationary displacement of literal smooth spherical vector observables -/
namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel SphericalDynamics SphericalReversibility SphericalLaplaceIdentification
open SphericalPhysicalSpectral
open scoped Topology ContDiff InnerProductSpace BigOperators NNReal ENNReal
variable {N M : ℕ}

/-- The literal sum of the component spherical energies. -/
def vectorDirichletEnergy (β : ℝ) (H : Vector N → ℝ) (B : Vector N → Vector M) : ℝ :=
  ∑ a : Fin M, dirichletEnergy N β H (fun x => B x a)

/-- The genuine Hilbert--Schmidt norm squared of the tangent differential,
written as the sum of its actual Riesz-gradient rows. -/
def surfaceJacobianNormSq (B : Vector N → Vector M) (x : Vector N) : ℝ :=
  ∑ a : Fin M, ‖surfaceGradient (fun y => B y a) x‖^2

lemma contDiff_vector_coordinate {B : Vector N → Vector M} (hB : ContDiff ℝ 1 B) (a : Fin M) :
    ContDiff ℝ 1 (fun x => B x a) :=
  (show ContDiff ℝ 1 (fun v : Vector M => v a) from
    (PiLp.proj 2 (fun _ : Fin M => ℝ) a : Vector M →L[ℝ] ℝ).contDiff).comp hB

/-- The vector energy is the actual integral of the tangent differential's
Hilbert--Schmidt norm squared, with integrability proved from genuine C¹. -/
theorem vectorDirichletEnergy_eq_integral (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {B : Vector N → Vector M}
    (hB : ContDiff ℝ 1 B) :
    vectorDirichletEnergy β H B = ∫ x, surfaceJacobianNormSq B x ∂gibbsLaw N β H := by
  unfold vectorDirichletEnergy surfaceJacobianNormSq
  simp_rw [dirichletEnergy_eq_integral_norm_sq]
  symm
  exact integral_finsetSum _ (fun a _ => integrable_gibbs_of_continuous hN β hH
    (((surfaceGradient_continuous (contDiff_vector_coordinate hB a)).norm).pow 2))

/-- The literal squared vector displacement is genuinely integrable under
its actual stationary two-time law. -/
theorem smooth_vector_stationary_displacement_integrable (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (t : ℝ≥0) :
    Integrable (fun z => ‖B z.2-B z.1‖^2) (twoTimeLaw μ J β t) := by
  let := mixtureGibbsLaw_probability hN μ β J
  have hi (a : Fin M) : Integrable (fun z : Vector N × Vector N => (B z.2 a-B z.1 a)^2)
      (twoTimeLaw μ J β t) := by
    have hm := memLp_gibbs_of_continuous hN β (potential_continuous μ J)
      (contDiff_vector_coordinate hB a).continuous
    have hf := hm.comp_measurePreserving (StationaryCoupling.fst_preserving
      (mixtureGibbsLaw μ β J) (mixedTransitionKernel μ J β t))
    have hs := hm.comp_measurePreserving (StationaryCoupling.snd_preserving
      (mixtureGibbsLaw μ β J) (mixedTransitionKernel μ J β t)
      (mixedTransitionKernel_gibbs_invariant hN μ J β t))
    exact (hs.sub hf).integrable_sq
  have he : (fun z : Vector N × Vector N => ‖B z.2-B z.1‖^2) =
      fun z => ∑ a : Fin M, (B z.2 a-B z.1 a)^2 := by
    funext z
    simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [he]
  exact integrable_finset_sum _ (fun a _ => hi a)

/-- The source displacement estimate for an actual ambient C¹ observable
under the actual mixed spherical Langevin kernel. No spectral data or form
membership are supplied as premises. -/
theorem smooth_vector_stationary_displacement_energy_le (hN : 2 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (t : ℝ≥0) :
    (∫ z, ‖B z.2-B z.1‖^2 ∂twoTimeLaw μ J β t) ≤
      2*(t:ℝ)*vectorDirichletEnergy β (potential μ J) B := by
  let hN1 : 1 ≤ N := by omega
  let D := normalizedSphericalSpectralData hN β (potential μ J) (potential_continuous μ J)
  let u (a : Fin M) := C1ToGraph hN1 β (potential μ J) (potential_continuous μ J)
    (fun x => B x a) (contDiff_vector_coordinate hB a)
  have he := vector_stationary_displacement_energy_le D t u
  have ha (a : Fin M) : formValue hN1 μ J β (u a) =ᵐ[mixtureGibbsLaw μ β J] (fun x => B x a) :=
    gibbsToL2_coe hN1 β (potential μ J) (potential_continuous μ J)
      (fun x => B x a) (contDiff_vector_coordinate hB a).continuous
  have hpair (a : Fin M) : ∀ᵐ z ∂twoTimeLaw μ J β t,
      formValue hN1 μ J β (u a) z.1 = B z.1 a ∧
      formValue hN1 μ J β (u a) z.2 = B z.2 a := by
    have hf : ∀ᵐ z ∂twoTimeLaw μ J β t, formValue hN1 μ J β (u a) z.1 = B z.1 a := by
      apply ae_of_ae_map (μ := twoTimeLaw μ J β t)
        (p := fun x => formValue hN1 μ J β (u a) x = B x a) measurable_fst.aemeasurable
      change ∀ᵐ y ∂(twoTimeLaw μ J β t).fst, _
      rw [twoTimeLaw_first_marginal hN1 μ J β t]
      exact ha a
    have hs : ∀ᵐ z ∂twoTimeLaw μ J β t, formValue hN1 μ J β (u a) z.2 = B z.2 a := by
      apply ae_of_ae_map (μ := twoTimeLaw μ J β t)
        (p := fun x => formValue hN1 μ J β (u a) x = B x a) measurable_snd.aemeasurable
      change ∀ᵐ y ∂(twoTimeLaw μ J β t).snd, _
      rw [twoTimeLaw_second_marginal hN1 μ J β t]
      exact ha a
    exact hf.and hs
  have hall := (ae_all_iff.mpr hpair)
  have heq : (∫ z, ∑ a : Fin M,
      ((formValue hN1 μ J β (u a)) z.2-(formValue hN1 μ J β (u a)) z.1)^2 ∂twoTimeLaw μ J β t) =
      ∫ z, ‖B z.2-B z.1‖^2 ∂twoTimeLaw μ J β t := by
    apply integral_congr_ae
    filter_upwards [hall] with z hz
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro a ha
    rw [(hz a).1, (hz a).2]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [heq] at he
  convert he using 1
  unfold vectorDirichletEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact (sphericalCompletedDirichlet_C1_energy hN1 β (potential μ J)
    (potential_continuous μ J) (fun x => B x a) (contDiff_vector_coordinate hB a)).symm

end
end SlowEquilibration.SphericalForm
