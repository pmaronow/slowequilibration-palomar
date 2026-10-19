-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpinProjection

/-! Literal stationary connected spin correlation for the constructed
diffusion. Its equality with the centered Gibbs Hilbert pairing is proved
from the actual two-time law; both source correlation bounds follow. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalSpinCorrelation

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalPhysicalSpectral SphericalBarycenter
open SphericalLaplaceIdentification SphericalCenteredObservables SphericalSpinProjection
open SphericalDynamics SphericalReversibility SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators

set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N M : ℕ}

def connectedSpinCorrelation (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : ℝ :=
  (∫ z, overlap z.1 z.2 ∂twoTimeLaw μ J β t) - ‖mean μ J β spin‖^2

lemma twoTime_onSphere (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    ∀ᵐ z ∂twoTimeLaw μ J β t, OnSphere z.1 ∧ OnSphere z.2 := by
  have hf : ∀ᵐ z ∂twoTimeLaw μ J β t, OnSphere z.1 := by
    apply ae_of_ae_map (μ := twoTimeLaw μ J β t) (p := OnSphere) measurable_fst.aemeasurable
    change ∀ᵐ x ∂(twoTimeLaw μ J β t).fst, OnSphere x
    rw [twoTimeLaw_first_marginal hN μ J β t]
    exact mixtureGibbsLaw_onSphere hN μ J β
  have hs : ∀ᵐ z ∂twoTimeLaw μ J β t, OnSphere z.2 := by
    apply ae_of_ae_map (μ := twoTimeLaw μ J β t) (p := OnSphere) measurable_snd.aemeasurable
    change ∀ᵐ x ∂(twoTimeLaw μ J β t).snd, OnSphere x
    rw [twoTimeLaw_second_marginal hN μ J β t]
    exact mixtureGibbsLaw_onSphere hN μ J β
  exact hf.and hs

lemma twoTime_overlap_integrable (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    Integrable (fun z => overlap z.1 z.2) (twoTimeLaw μ J β t) := by
  let _ := twoTimeLaw_probability hN μ J β t
  apply Integrable.of_bound (by unfold overlap; fun_prop) 1
  filter_upwards [twoTime_onSphere hN μ J β t] with z hz
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (overlap_mem_Icc_of_norm_sq hN z.1 z.2
    ((onSphere_iff_norm_sq z.1).mp hz.1) ((onSphere_iff_norm_sq z.2).mp hz.2))

lemma spin_displacement_integral (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    (∫ z, ‖spin z.2 - spin z.1‖^2 ∂twoTimeLaw μ J β t) =
      2 - 2 * (∫ z, overlap z.1 z.2 ∂twoTimeLaw μ J β t) := by
  let _ := twoTimeLaw_probability hN μ J β t
  have heq : (fun z => ‖spin z.2 - spin z.1‖^2) =ᵐ[twoTimeLaw μ J β t]
      (fun z => 2 - 2 * overlap z.1 z.2) := by
    filter_upwards [twoTime_onSphere hN μ J β t] with z hz
    rw [norm_sub_sq_real, spin_norm hN z.2 hz.2, spin_norm hN z.1 hz.1,
      real_inner_comm (spin z.1) (spin z.2), spin_inner hN]
    ring
  rw [integral_congr_ae heq,
    integral_sub (integrable_const (2 : ℝ)) ((twoTime_overlap_integrable hN μ J β t).const_mul 2),
    integral_const, probReal_univ, one_smul, integral_const_mul]

lemma centered_spin_variance (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    ‖centeredL2 hN μ J β spin (spin_contDiff.of_le (by simp))‖^2 = 1 - ‖mean μ J β spin‖^2 := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  rw [centeredL2_variance]
  have heq : (fun x => ‖spin x‖^2) =ᵐ[mixtureGibbsLaw μ β J] (fun _ => (1 : ℝ)) := by
    filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
    rw [spin_norm hN x hx, one_pow]
  rw [integral_congr_ae heq, integral_const, probReal_univ, one_smul]

lemma vector_stationary_displacement_identity (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    (B : Vector N → Vector M) (hB : ContDiff ℝ 1 B) (t : ℝ≥0) :
    (∫ z, ‖B z.2 - B z.1‖^2 ∂twoTimeLaw μ J β t) =
      2 * inner ℝ (vectorL2 hN μ J β B hB)
        (vectorL2 hN μ J β B hB - vectorP hN μ J β t (vectorL2 hN μ J β B hB)) := by
  rw [PiLp.inner_apply]
  simp only [PiLp.sub_apply, vectorL2_apply, vectorP_apply]
  exact smooth_stationary_displacement_identity hN μ J β B hB t

/-- The literal overlap expectation under the actual stationary diffusion
is exactly the physical centered-spin Hilbert correlation. -/
theorem connectedSpinCorrelation_eq_inner (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    connectedSpinCorrelation μ J β t =
      inner ℝ (centeredL2 hN μ J β spin (spin_contDiff.of_le (by simp)))
        (vectorP hN μ J β t (centeredL2 hN μ J β spin (spin_contDiff.of_le (by simp)))) := by
  let hSpin : ContDiff ℝ 1 (spin : Vector N → Vector N) := spin_contDiff.of_le (by simp)
  let Z := centeredL2 hN μ J β spin hSpin
  have hd := vector_stationary_displacement_identity hN μ J β (centered μ J β spin)
    (centered_contDiff μ J β hSpin) t
  have heq : (∫ z, ‖centered μ J β spin z.2 - centered μ J β spin z.1‖^2 ∂twoTimeLaw μ J β t) =
      ∫ z, ‖spin z.2 - spin z.1‖^2 ∂twoTimeLaw μ J β t := by
    apply integral_congr_ae
    apply ae_of_all
    intro z
    have he : centered μ J β spin z.2 - centered μ J β spin z.1 = spin z.2 - spin z.1 := by
      change (spin z.2 - mean μ J β spin) - (spin z.1 - mean μ J β spin) = spin z.2 - spin z.1
      abel
    exact congrArg (fun v : Vector N => ‖v‖^2) he
  rw [heq] at hd
  change (∫ z, ‖spin z.2 - spin z.1‖^2 ∂twoTimeLaw μ J β t) =
    2 * inner ℝ Z (Z - vectorP hN μ J β t Z) at hd
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hd
  have hs := spin_displacement_integral hN μ J β t
  have hv := centered_spin_variance hN μ J β
  change connectedSpinCorrelation μ J β t = inner ℝ Z (vectorP hN μ J β t Z)
  unfold connectedSpinCorrelation
  linarith

/-- Source direct correlation bound stated in the literal stationary
overlap observable, with actual Gibbs energy and actual magnetization. -/
theorem direct_connected_correlation_lower (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, OnSphere x → ‖B x‖ ≤ 1) {a : ℝ}
    (ha : a ≤ ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β J) (t : ℝ≥0) :
    (max 0 (a - ‖mean μ J β spin‖ - Real.sqrt ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2)))^2 ≤
      connectedSpinCorrelation μ J β t := by
  rw [connectedSpinCorrelation_eq_inner (show 1 ≤ N by omega)]
  exact spin_direct_correlation_lower hN μ J β B hBs hB ha t

/-- Source projected correlation floor in the literal stationary overlap
observable, using the genuine positive low-mode spin projection. -/
theorem projected_connected_correlation_lower (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β Λ : ℝ) (t : ℝ≥0) :
    Real.exp (-(t : ℝ) * Λ) *
      ‖vectorCutoff hN μ J β Λ
        (centeredL2 (show 1 ≤ N by omega) μ J β spin (spin_contDiff.of_le (by simp)))‖^2 ≤
      connectedSpinCorrelation μ J β t := by
  rw [connectedSpinCorrelation_eq_inner (show 1 ≤ N by omega)]
  exact projected_physical_correlation hN μ J β Λ t _

/-- The full source projection alignment inequality for an arbitrary
actual Gibbs Hilbert vector Z and an ordinary smooth vector observable B. -/
theorem smooth_projection_alignment (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector M) (hBs : ContDiff ℝ 1 B)
    (Z : VectorSpace (Fin M) μ J β) {Λ : ℝ} (hΛ : 0 < Λ) :
    inner ℝ Z (centeredL2 (show 1 ≤ N by omega) μ J β B hBs) -
      ‖Z‖ * Real.sqrt (vectorDirichletEnergy β (potential μ J) B / Λ) ≤
        ‖vectorCutoff hN μ J β Λ Z‖ * ‖centeredL2 (show 1 ≤ N by omega) μ J β B hBs‖ := by
  have hE : 0 ≤ vectorDirichletEnergy β (potential μ J) B :=
    Finset.sum_nonneg (fun a _ => dirichletEnergy_nonneg _ _ _ _)
  have ht := centered_projection_tail hN μ J β B hBs hΛ
  rw [vectorCutoff_eq_starProjection] at ht
  have ha := orthogonal_projection_alignment (lowSpace (M := M) hN μ J β Λ) Z
    (centeredL2 (show 1 ≤ N by omega) μ J β B hBs)
    (vectorDirichletEnergy β (potential μ J) B) Λ hE hΛ ht
  rw [← vectorCutoff_eq_starProjection] at ha
  exact ha

/-- The literal stationary correlation lower bound simultaneously at
every time up to T, using the source direct energy estimate. -/
theorem direct_connected_correlation_uniform (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (B : Vector N → Vector N) (hBs : ContDiff ℝ 1 B)
    (hB : ∀ x, OnSphere x → ‖B x‖ ≤ 1) {a : ℝ}
    (ha : a ≤ ∫ x, inner ℝ (spin x) (B x) ∂mixtureGibbsLaw μ β J) (T : ℝ≥0) :
    ∀ t ≤ T,
      (max 0 (a - ‖mean μ J β spin‖ - Real.sqrt ((T : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2)))^2 ≤
        connectedSpinCorrelation μ J β t := by
  intro t ht
  have hE : 0 ≤ vectorDirichletEnergy β (potential μ J) B :=
    Finset.sum_nonneg (fun a _ => dirichletEnergy_nonneg _ _ _ _)
  have hsqrt : Real.sqrt ((t : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2) ≤
      Real.sqrt ((T : ℝ) * vectorDirichletEnergy β (potential μ J) B / 2) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht hE) (by norm_num)
  have hmax := max_le_max (show (0 : ℝ) ≤ 0 from le_rfl)
    (sub_le_sub_left hsqrt (a - ‖mean μ J β spin‖))
  exact (pow_le_pow_left₀ (le_max_left _ _) hmax 2).trans
    (direct_connected_correlation_lower hN μ J β B hBs hB ha t)

/-- The literal stationary projected correlation floor simultaneously
throughout a time interval, with its exact physical cutoff multiplier. -/
theorem projected_connected_correlation_uniform (hN : 2 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (T : ℝ≥0) :
    ∀ t ≤ T, Real.exp (-(T : ℝ) * Λ) *
      ‖vectorCutoff hN μ J β Λ
        (centeredL2 (show 1 ≤ N by omega) μ J β spin (spin_contDiff.of_le (by simp)))‖^2 ≤
      connectedSpinCorrelation μ J β t := by
  intro t ht
  have he : Real.exp (-(T : ℝ) * Λ) ≤ Real.exp (-(t : ℝ) * Λ) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg ht) hΛ
  exact (mul_le_mul_of_nonneg_right he (sq_nonneg _)).trans
    (projected_connected_correlation_lower hN μ J β Λ t)

end SlowEquilibration.SphericalSpinCorrelation
