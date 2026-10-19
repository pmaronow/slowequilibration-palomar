-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothingApprox
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Genuine kernel Fubini and moment identities for the actual spherical
radial smoothing kernels. No zero-energy rigidity premise is built into any
construction. Constant smoothed moments are explicit hypotheses of the
measure-algebra implications proved here. -/

noncomputable section
namespace SlowEquilibration.SphericalForm

open MeasureTheory Filter Set
open SphericalModel SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace ContDiff

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

/-- Integrability of the literal weighted kernel product follows from the
genuine global bound 0 ≤ K ≤ 1 and ordinary product integrability. -/
theorem sphereSmoothingKernel_product_integrable
    (ν π : Measure (Vector N)) [SFinite ν] [SFinite π]
    {p w : Vector N → ℝ} (hp : Integrable p ν) (hw : Integrable w π) (ε : ℝ) :
    Integrable (fun q : Vector N × Vector N =>
      p q.1*w q.2*sphereSmoothingKernel ε q.1 q.2) (ν.prod π) := by
  have hi := hp.mul_prod hw
  apply hi.norm.mono'
    (hi.aestronglyMeasurable.mul (sphereSmoothingKernel_contDiff ε).continuous.aestronglyMeasurable)
  exact ae_of_all _ (fun q => by
    change ‖p q.1*w q.2*sphereSmoothingKernel ε q.1 q.2‖ ≤ ‖p q.1*w q.2‖
    rw [norm_mul, Real.norm_of_nonneg (sphereSmoothingKernel_nonneg ε q.1 q.2)]
    exact (mul_le_mul_of_nonneg_left (sphereSmoothingKernel_le_one ε q.1 q.2)
      (norm_nonneg _)).trans_eq (mul_one _))

/-- Actual Fubini identity for arbitrary integrable signed weights, using
the literal symmetric spherical radial kernel. -/
theorem sphereSmoothingMoment_swap (ν π : Measure (Vector N)) [SFinite ν] [SFinite π]
    {p w : Vector N → ℝ} (hp : Integrable p ν) (hw : Integrable w π) (ε : ℝ) :
    (∫ x, p x*sphereSmoothingMoment π ε w x ∂ν) =
      ∫ y, w y*sphereSmoothingMoment ν ε p y ∂π := by
  have hi : Integrable (Function.uncurry (fun x y =>
      p x*w y*sphereSmoothingKernel ε x y)) (ν.prod π) :=
    sphereSmoothingKernel_product_integrable ν π hp hw ε
  have hf := integral_integral_swap hi
  calc
    _ = ∫ x, ∫ y, p x*w y*sphereSmoothingKernel ε x y ∂π ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change p x*(∫ y, w y*sphereSmoothingKernel ε x y ∂π) = _
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by ring))
    _ = ∫ y, ∫ x, p x*w y*sphereSmoothingKernel ε x y ∂ν ∂π := hf
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        change _ = w y*(∫ x, p x*sphereSmoothingKernel ε y x ∂ν)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by
          change p x*w y*sphereSmoothingKernel ε x y = w y*(p x*sphereSmoothingKernel ε y x)
          rw [sphereSmoothingKernel_symm ε x y]
          ring))

/-- An integrable weight can be multiplied by any ambient continuous
observable under a measure supported on the actual compact sphere. -/
theorem weighted_continuous_integrable_onSphere
    (π : Measure (Vector N)) (hπ : ∀ᵐ x ∂π, OnSphere x)
    {w p : Vector N → ℝ} (hw : Integrable w π) (hp : Continuous p) :
    Integrable (fun x => w x*p x) π := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vector N) ((N : ℝ)+1)).exists_bound_of_continuousOn hp.continuousOn
  apply (hw.norm.const_mul C).mono' (hw.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards [hπ] with x hx
  have hxnorm : ‖x‖ ≤ (N : ℝ)+1 := by
    have hs := (onSphere_iff_norm_sq x).mp hx
    nlinarith [norm_nonneg x, Nat.cast_nonneg (α := ℝ) N]
  change ‖w x*p x‖ ≤ C*‖w x‖
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hC x (by simpa using hxnorm)) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The true mean of a constant smoothing row is determined by actual
positive kernel row mass and the original signed weight's mean. -/
theorem sphereSmoothingMoment_constant_mean (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsFiniteMeasure π] (hπ : ∀ᵐ x ∂π, OnSphere x)
    {w : Vector N → ℝ} (hw : Integrable w π) (ε c : ℝ)
    (hc : ∀ x, OnSphere x → sphereSmoothingMoment π ε w x = c) :
    c = sphereSmoothingMass hN ε*(∫ y, w y ∂π) := by
  have h := sphereSmoothingMoment_swap (sphereLaw N) π (integrable_const (1 : ℝ)) hw ε
  simp only [one_mul] at h
  have hl : (∫ x, sphereSmoothingMoment π ε w x ∂sphereLaw N) = c := by
    calc
      _ = ∫ _ : Vector N, c ∂sphereLaw N := by
        apply integral_congr_ae
        filter_upwards [sphereLaw_support hN] with x hx
        exact hc x ((onSphere_iff_norm_sq x).mpr hx)
      _ = c := by simp
  have hr : (∫ y, w y*sphereSmoothingMoment (sphereLaw N) ε (fun _ => 1) y ∂π) =
      sphereSmoothingMass hN ε*(∫ y, w y ∂π) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hπ] with y hy
    have hm : sphereSmoothingMoment (sphereLaw N) ε (fun _ => 1) y = sphereSmoothingMass hN ε := by
      simp only [sphereSmoothingMoment, one_mul]
      exact sphereSmoothingKernel_row_mass hN ε y hy
    rw [hm, mul_comm]
  exact hl.symm.trans (h.trans hr)

/-- Constant genuine signed smoothing moments give the exact normalized
observable moment identity by true kernel Fubini and positive row mass. -/
theorem sphericalSmoothObservable_weighted_of_constant (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsFiniteMeasure π] (hπ : ∀ᵐ x ∂π, OnSphere x)
    {w p : Vector N → ℝ} (hw : Integrable w π) (hp : Continuous p) (ε c : ℝ)
    (hc : ∀ x, OnSphere x → sphereSmoothingMoment π ε w x = c) :
    (∫ y, w y*sphericalSmoothObservable hN ε p y ∂π) =
      (∫ y, w y ∂π)*(∫ x, p x ∂sphereLaw N) := by
  let m := sphereSmoothingMass hN ε
  have hm : 0 < m := sphereSmoothingMass_pos hN ε
  have hmean := sphereSmoothingMoment_constant_mean hN π hπ hw ε c hc
  have hswap := sphereSmoothingMoment_swap (sphereLaw N) π
    (integrable_sphere_of_continuous hN hp) hw ε
  calc
    _ = m⁻¹*(∫ y, w y*sphereSmoothingMoment (sphereLaw N) ε p y ∂π) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by dsimp [sphericalSmoothObservable, m]; ring)
    _ = m⁻¹*(∫ x, p x*sphereSmoothingMoment π ε w x ∂sphereLaw N) := by rw [hswap]
    _ = m⁻¹*(c*(∫ x, p x ∂sphereLaw N)) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [sphereLaw_support hN] with x hx
      rw [hc x ((onSphere_iff_norm_sq x).mpr hx), mul_comm]
    _ = _ := by
      rw [hmean]
      change m⁻¹*(m*(∫ y, w y ∂π)*(∫ x, p x ∂sphereLaw N)) = _
      field_simp [hm.ne']

/-- A genuine uniform observable error bounds every integrable signed
weighted moment error by the actual integral of the weight's norm. -/
theorem sphericalSmoothObservable_weighted_error_le (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsFiniteMeasure π] (hπ : ∀ᵐ x ∂π, OnSphere x)
    {w p : Vector N → ℝ} (hw : Integrable w π) (hp : Continuous p)
    {ε δ : ℝ} (hε : 0 < ε) (_hδ : 0 ≤ δ)
    (herror : ∀ x, OnSphere x → |sphericalSmoothObservable hN ε p x-p x| ≤ δ) :
    |(∫ x, w x*sphericalSmoothObservable hN ε p x ∂π)-(∫ x, w x*p x ∂π)| ≤
      δ*(∫ x, ‖w x‖ ∂π) := by
  have hS := weighted_continuous_integrable_onSphere π hπ hw
    (sphericalSmoothObservable_contDiff_one hN hε hp).continuous
  have hpw := weighted_continuous_integrable_onSphere π hπ hw hp
  rw [← integral_sub hS hpw]
  change ‖∫ x, w x*sphericalSmoothObservable hN ε p x-w x*p x ∂π‖ ≤ _
  calc
    _ ≤ ∫ x, ‖w x*sphericalSmoothObservable hN ε p x-w x*p x‖ ∂π := norm_integral_le_integral_norm _
    _ ≤ ∫ x, δ*‖w x‖ ∂π := by
      apply integral_mono_ae (hS.sub hpw).norm (hw.norm.const_mul δ)
      filter_upwards [hπ] with x hx
      change ‖w x*sphericalSmoothObservable hN ε p x-w x*p x‖ ≤ δ*‖w x‖
      rw [← mul_sub, norm_mul]
      have he : ‖sphericalSmoothObservable hN ε p x-p x‖ ≤ δ := by
        simpa only [Real.norm_eq_abs] using herror x hx
      exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

/-- True convergence of all integrable weighted moments under the actual
normalized spherical smoothing sequence. Uniform approximation is proved
for the ordinary sphere; the weight may have either sign and any L¹ size. -/
theorem sphericalSmoothObservable_weighted_tendsto (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsFiniteMeasure π] (hπ : ∀ᵐ x ∂π, OnSphere x)
    {w p : Vector N → ℝ} (hw : Integrable w π) (hp : Continuous p) :
    Tendsto (fun n : ℕ => ∫ x, w x*sphericalSmoothObservable hN (1/((n : ℝ)+1)) p x ∂π)
      atTop (𝓝 (∫ x, w x*p x ∂π)) := by
  let I : ℝ := ∫ x, ‖w x‖ ∂π
  have hI : 0 ≤ I := integral_nonneg (fun _ => norm_nonneg _)
  have hwidth : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ := η/(I+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r, hr, happ⟩ := sphericalSmoothObservable_uniform_approx hN hp δ hδ
  filter_upwards [hwidth.eventually (gt_mem_nhds hr)] with n hn
  have hε : 0 < 1/((n : ℝ)+1) := by positivity
  have hb := sphericalSmoothObservable_weighted_error_le hN π hπ hw hp hε hδ.le
    (fun x hx => (happ _ hε hn x hx).le)
  rw [Real.dist_eq]
  apply hb.trans_lt
  change δ*I < η
  dsimp [δ]
  calc
    _ < (η/(I+1))*(I+1) := mul_lt_mul_of_pos_left (by linarith) (div_pos hη (by positivity))
    _ = η := div_mul_cancel₀ η (by positivity)

end SlowEquilibration.SphericalForm
