-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePressure
public import SlowEquilibration.CSTwoAtom

@[expose] public section

/-! The literal Dirac trial for the actual auxiliary latitude covariance.
This evaluates the ordinary Crisanti--Sommers functional and identifies the
proved physical latitude pressure upper with that concrete trial value. -/

namespace SlowEquilibration.FiniteMixture
noncomputable section

def auxiliaryCovariance (μ : FiniteMixture) (q t : ℝ) : ℝ :=
  μ.xi (q^2+(1-q^2)*t)-μ.xi (q^2)

theorem auxiliaryCovariance_continuous (μ : FiniteMixture) (q : ℝ) :
    Continuous (μ.auxiliaryCovariance q) := by
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr
    (fun r => (μ.hasDerivAt_xi r).continuousAt)
  exact (hxi.comp (continuous_const.add (continuous_const.mul continuous_id))).sub continuous_const

theorem auxiliaryCovariance_hasDerivAt (μ : FiniteMixture) (q t : ℝ) :
    HasDerivAt (μ.auxiliaryCovariance q)
      ((1-q^2)*μ.xi1 (q^2+(1-q^2)*t)) t := by
  have hlin := ((hasDerivAt_id t).const_mul (1-q^2)).const_add (q^2)
  convert ((μ.hasDerivAt_xi (q^2+(1-q^2)*t)).comp t hlin).sub_const (μ.xi (q^2)) using 1
  · funext x
    unfold auxiliaryCovariance
    simp only [Function.comp_apply, id_eq]
  · ring

end
end SlowEquilibration.FiniteMixture

namespace SlowEquilibration.CrisantiSommers
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def latitudeDiracLocation (q : ℝ) : ℝ := q/(1+q)

theorem latitudeDiracLocation_mem {q : ℝ} (hq : q ∈ Ico 0 1) :
    latitudeDiracLocation q ∈ Ico 0 1 := by
  have hd : 0 < 1+q := by linarith [hq.1]
  refine ⟨div_nonneg hq.1 hd.le, ?_⟩
  exact (div_lt_one hd).mpr (by linarith)

theorem xHat_dirac (q t : ℝ) : xHat (Measure.dirac q) t = 1-max t q := by
  simp [xHat]

theorem integral_inverse_xHat_dirac {q : ℝ} (hq : q ∈ Ico 0 1) :
    (∫ t in (0 : ℝ)..q, (xHat (Measure.dirac q) t)⁻¹) = q/(1-q) := by
  calc
    _ = ∫ _t in (0 : ℝ)..q, (1-q)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc 0 q := by simpa only [uIcc_of_le hq.1] using ht
      change (xHat (Measure.dirac q) t)⁻¹ = (1-q)⁻¹
      rw [xHat_dirac, max_eq_right ht'.2]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, div_eq_mul_inv]

/-- The actual functional at a one-atom probability measure, with its genuine
hatted measure and entropy integral evaluated analytically. -/
theorem functional_dirac (β : ℝ) (η : ℝ → ℝ) {q : ℝ} (hq : q ∈ Ico 0 1) :
    functional β η (Measure.dirac q) q =
      (β^2*(η 1-η q)+q/(1-q)+Real.log (1-q))/2 := by
  unfold functional
  rw [integral_dirac, integral_inverse_xHat_dirac hq]

def latitudeDiracCandidate (q : ℝ) (hq : q ∈ Ico 0 1) : Admissible :=
  ⟨Measure.dirac (latitudeDiracLocation q), inferInstance,
    ⟨latitudeDiracLocation q, dirac_hasCutoff (latitudeDiracLocation_mem hq)⟩⟩

theorem auxiliaryCovariance_energy (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) :
    μ.auxiliaryCovariance q 1-μ.auxiliaryCovariance q (latitudeDiracLocation q) =
      μ.xi 1-μ.xi q := by
  have hd : 1+q ≠ 0 := ne_of_gt (by linarith)
  have he : q^2+(1-q^2)*latitudeDiracLocation q=q := by
    unfold latitudeDiracLocation
    field_simp
    ring
  unfold FiniteMixture.auxiliaryCovariance
  rw [he, show q^2+(1-q^2)*(1 : ℝ)=1 by ring]
  ring

/-- Lemma pr-trial-value: the ordinary CS functional of the actual auxiliary
covariance at the literal atom q/(1+q). -/
theorem functional_auxiliary_dirac (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Ico 0 1) :
    functional β (μ.auxiliaryCovariance q) (Measure.dirac (latitudeDiracLocation q))
      (latitudeDiracLocation q) =
      (β^2*(μ.xi 1-μ.xi q)+q-Real.log (1+q))/2 := by
  have hd : 1+q ≠ 0 := ne_of_gt (by linarith [hq.1])
  have he : 1-latitudeDiracLocation q=(1+q)⁻¹ := by
    unfold latitudeDiracLocation
    field_simp
    ring
  have hratio : latitudeDiracLocation q/(1-latitudeDiracLocation q)=q := by
    rw [he]
    unfold latitudeDiracLocation
    field_simp
  rw [functional_dirac β _ (latitudeDiracLocation_mem hq), auxiliaryCovariance_energy μ hq.1,
    hratio, he, Real.log_inv]
  ring

theorem latitudeDiracCandidate_value (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Ico 0 1) :
    (latitudeDiracCandidate q hq).value β (μ.auxiliaryCovariance q) =
      SphericalModel.latitudePressureTrial μ β q := by
  rw [(latitudeDiracCandidate q hq).value_eq β _ (dirac_hasCutoff (latitudeDiracLocation_mem hq))]
  exact functional_auxiliary_dirac μ β hq

/-- The proved physical finite-Gaussian latitude upper is bounded by this
actual admissible CS trial; its value has not been assumed to be a minimizer. -/
theorem latitudePressure_eventually_le_diracTrial (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Ico (1/2 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : SphericalModel.Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : SphericalModel.Vector n →ₗᵢ[ℝ] SphericalModel.Vector (n+1)),
        (∀ x, inner ℝ (e x) u=0) →
      SphericalModel.latitudeQuenchedPressure n μ β u e q ≤
        (latitudeDiracCandidate q ⟨by linarith [hq.1],hq.2⟩).value β (μ.auxiliaryCovariance q)+ε := by
  rw [latitudeDiracCandidate_value]
  exact SphericalModel.latitudeQuenchedPressure_eventually_upper μ β ⟨hq.1,hq.2.le⟩ hε

end
end SlowEquilibration.CrisantiSommers
