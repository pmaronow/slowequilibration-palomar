-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1DriftStability
public import SlowEquilibration.SphericalInfiniteDynamics
public import SlowEquilibration.SphericalInfiniteIntrinsicJets
public import SlowEquilibration.SphericalInfiniteSpectralTruncation

/-! Actual finite homogeneous truncations converge to the infinite-field
spherical SDE on its proved regularity event, under the same Brownian law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set MeasureTheory Filter SphericalModel SphericalForm SphereHessian
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def firstJetTail {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) (P : ℕ) : ℝ :=
  ∑' q,blockJetEnvelope μ 1 (q+P) J

theorem firstJetTail_nonneg {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (P : ℕ) : 0≤firstJetTail μ J P :=
  tsum_nonneg (fun q => blockJetEnvelope_nonneg hN μ 1 (q+P) J)

theorem firstJetTail_tendsto_zero {N : ℕ} (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) :
    Tendsto (firstJetTail μ J) atTop (𝓝 0) := by
  have hs := hJ 1 (by omega)
  have he (P : ℕ) : firstJetTail μ J P=(∑' q,blockJetEnvelope μ 1 q J)-
      ∑ q∈Finset.range P,blockJetEnvelope μ 1 q J := by
    have hh := hs.sum_add_tsum_nat_add P
    unfold firstJetTail
    linarith
  change Tendsto (fun P => firstJetTail μ J P) atTop (𝓝 0)
  simp_rw [he]
  have ht : Tendsto (fun P => (∑' q,blockJetEnvelope μ 1 q J)-
      ∑ q∈Finset.range P,blockJetEnvelope μ 1 q J) atTop
      (𝓝 ((∑' q,blockJetEnvelope μ 1 q J)-(∑' q,blockJetEnvelope μ 1 q J))) :=
    tendsto_const_nhds.sub hs.tendsto_sum_tsum_nat
  simpa only [sub_self] using ht

theorem partialField_firstJet_error {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) (P : ℕ)
    (x : Vector N) (hx : ‖x‖≤Real.sqrt N) :
    ‖fderiv ℝ (partialField μ P J) x-firstJetSeries μ J x‖≤firstJetTail μ J P := by
  have hb (p : ℕ) : ‖fderiv ℝ (block μ p J) x‖≤blockJetEnvelope μ 1 p J := by
    simpa only [norm_iteratedFDeriv_one] using block_iteratedFDeriv_norm_le hN μ 1 p J x hx
  have hn : Summable (fun p => ‖fderiv ℝ (block μ p J) x‖) :=
    (hJ 1 (by omega)).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hs := hn.of_norm
  have hsum := hs.sum_add_tsum_nat_add P
  have hfd : fderiv ℝ (partialField μ P J) x=
      ∑ p∈Finset.range P,fderiv ℝ (block μ p J) x := by
    apply fderiv_fun_sum
    intro p _
    exact (block_contDiff μ p J).differentiable (by simp) x
  rw [hfd,firstJetSeries,← hsum]
  rw [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg]
  have hnP : Summable (fun q => ‖fderiv ℝ (block μ (q+P) J) x‖) :=
    hn.comp_injective (fun a b h => Nat.add_right_cancel h)
  exact (norm_tsum_le_tsum_norm hnP).trans
    (hnP.tsum_le_tsum (fun q => hb (q+P))
      ((hJ 1 (by omega)).comp_injective (fun a b h => Nat.add_right_cancel h)))

def partialGradient {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) :
    Vector N → Vector N := gradient (partialField μ P J)

theorem partialGradient_contDiff {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) :
    ContDiff ℝ 1 (partialGradient μ P J) := by
  unfold partialGradient gradient
  exact ((InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff).comp
    ((partialField_contDiff μ P J).fderiv_right (by norm_num))

theorem partial_surfaceGradient_error (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (P : ℕ)
    (x : Vector (n+1)) (hx : OnSphere x) :
    ‖surfaceGradient (partialField μ P J) x-surfaceGradient (regularAmbientField n μ J) x‖≤
      firstJetTail μ J P := by
  rw [infinite_surfaceGradient_eq_jet n μ J hJ x hx]
  have he : surfaceGradient (partialField μ P J) x-withinGradient (firstJetSeries μ J) x=
      withinGradient (fun y => fderiv ℝ (partialField μ P J) y-firstJetSeries μ J y) x := by
    simp only [surfaceGradient,withinGradient,gradient,map_sub]
  rw [he]
  apply (withinGradient_norm_le (by omega) _ x hx).trans
  apply partialField_firstJet_error (by omega) μ J hJ P x
  exact le_of_eq ((Real.sqrt_sq (norm_nonneg _)).symm.trans
    (congrArg Real.sqrt ((onSphere_iff_norm_sq x).mp hx)))

theorem partial_drift_error (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (P : ℕ)
    (x : Vector (n+1)) (hx : OnSphere x) :
    ‖drift β (partialGradient μ P J) x-drift β (infiniteGradient n μ J) x‖≤
      |β| * firstJetTail μ J P := by
  have he : drift β (partialGradient μ P J) x-drift β (infiniteGradient n μ J) x=
      β • (surfaceGradient (partialField μ P J) x-
        surfaceGradient (regularAmbientField n μ J) x) := by
    simp only [drift,partialGradient,infiniteGradient,surfaceGradient,tangentProjection_apply,
      smul_sub]
    abel
  rw [he,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (partial_surfaceGradient_error n μ J hJ P x hx) (abs_nonneg β)

/-- Actual finite-truncation terminal Brownian states converge in L² for
every regular disorder, every physical initial state and every finite time. -/
theorem partial_terminalValue_tendsto (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (x : Vector (n+1)) (hx : OnSphere x) (T t : ℝ≥0) :
    Tendsto (fun P => SphericalC1Dynamics.terminalValue β (partialGradient μ P J)
      (partialGradient_contDiff μ P J) x T t) atTop
      (𝓝 (SphericalC1Dynamics.terminalValue β (infiniteGradient n μ J)
        (infiniteGradient_contDiff n μ J) x T t)) := by
  apply SphericalC1Dynamics.terminalValue_tendsto_of_drift (by omega) β _
    (infiniteGradient_contDiff n μ J) (fun P => partialGradient μ P J)
    (fun P => partialGradient_contDiff μ P J) (fun P => |β| * firstJetTail μ J P)
  · exact fun P => mul_nonneg (abs_nonneg β) (firstJetTail_nonneg (by omega) μ J P)
  · exact fun P z hz => partial_drift_error n μ J hJ β P z hz
  · simpa only [mul_zero] using (firstJetTail_tendsto_zero μ J hJ).const_mul |β|
  · exact hx

theorem partial_expectation_tendsto (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (x : Vector (n+1)) (hx : OnSphere x) (t : ℝ≥0)
    (f : Vector (n+1) → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ z,‖f z‖≤C) :
    Tendsto (fun P => SphericalC1Dynamics.expectation β (partialGradient μ P J)
      (partialGradient_contDiff μ P J) t f x) atTop
      (𝓝 (SphericalC1Dynamics.expectation β (infiniteGradient n μ J)
        (infiniteGradient_contDiff n μ J) t f x)) := by
  apply SphericalC1Dynamics.expectation_tendsto_of_drift (by omega) β _
    (infiniteGradient_contDiff n μ J) (fun P => partialGradient μ P J)
    (fun P => partialGradient_contDiff μ P J) (fun P => |β| * firstJetTail μ J P)
  · exact fun P => mul_nonneg (abs_nonneg β) (firstJetTail_nonneg (by omega) μ J P)
  · exact fun P z hz => partial_drift_error n μ J hJ β P z hz
  · simpa only [mul_zero] using (firstJetTail_tendsto_zero μ J hJ).const_mul |β|
  · exact hx
  · exact hf
  · exact hC

end SlowEquilibration.SphericalInfiniteModel
