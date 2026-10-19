module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterMeans
public import SlowEquilibration.SphericalBarycenterWeightCalculus
public import SlowEquilibration.SphericalObservableDisplacement

@[expose] public section

/-! # Genuine normalized Gibbs differentiation and barycenter covariance -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- A literal weighted scalar Gibbs moment. -/
def scalarNumerator (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ)
    (a : Vector N → ℝ) (x : Vector N) : ℝ :=
  ∫ u, (psi h x u)^2*a u ∂gibbsLaw N β H

/-- A literal normalized weighted scalar mean. -/
def scalarAverage (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ)
    (a : Vector N → ℝ) (x : Vector N) : ℝ :=
  (denominator β H h x)⁻¹*scalarNumerator β H h a x

lemma scalarNumerator_joint_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : Vector N → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun z : Vector N × Vector N => (psi h z.2 z.1)^2*a z.1) :=
  (psi_joint_contDiff hh |>.pow 2).mul (ha.comp contDiff_fst)

lemma scalarNumerator_contDiff (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : Vector N → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (scalarNumerator β H h a) :=
  gibbsIntegral_contDiff hN β hH _ (scalarNumerator_joint_contDiff hh ha)

lemma fderiv_logPsi_continuous (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (x : Vector N) : Continuous (fun u => fderiv ℝ (fun y => logPsi h y u) x) := by
  have he : (fun u => fderiv ℝ (fun y => logPsi h y u) x) =
      fun u => InnerProductSpace.toDual ℝ (Vector N) (-(deriv h (overlap x u)) • u) := by
    funext u
    exact (logPsi_hasGradientAt hN hh x u).hasFDerivAt.fderiv
  rw [he]
  exact (InnerProductSpace.toDual ℝ (Vector N)).continuous.comp
    (((hh.continuous_deriv (by simp)).comp
      ((continuous_const.inner continuous_id).div_const _)).neg.smul continuous_id)

/-- Differentiation under the actual Gibbs integral gives the actual
weighted derivative, including the source factor two. -/
theorem scalarNumerator_fderiv_apply (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : Vector N → ℝ} (ha : ContDiff ℝ ∞ a) (x v : Vector N) :
    (fderiv ℝ (scalarNumerator β H h a) x) v =
      2*∫ u, (psi h x u)^2*a u*(fderiv ℝ (fun y => logPsi h y u) x) v ∂gibbsLaw N β H := by
  have hfd (u : Vector N) : fderiv ℝ (fun y => (psi h y u)^2*a u) x =
      (2*(psi h x u)^2*a u) • fderiv ℝ (fun y => logPsi h y u) x := by
    rw [(psiSq_hasFDerivAt hh x u |>.mul_const (a u)).fderiv]
    ext w
    simp only [_root_.smul_apply, smul_eq_mul]
    ring
  have hp : Continuous (fun u : Vector N => (psi h x u)^2) :=
    ((psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hD : Continuous (fun u => (2*(psi h x u)^2*a u) •
      fderiv ℝ (fun y => logPsi h y u) x) :=
    ((continuous_const.mul hp).mul ha.continuous).smul (fderiv_logPsi_continuous hN hh x)
  change (fderiv ℝ (fun y => ∫ u, (psi h y u)^2*a u ∂gibbsLaw N β H) x) v = _
  rw [gibbsIntegral_fderiv hN β hH (fun u y => (psi h y u)^2*a u)
    (scalarNumerator_joint_contDiff hh ha) x]
  simp_rw [hfd]
  rw [ContinuousLinearMap.integral_apply (integrable_gibbs_of_continuous_vector hN β hH hD)]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by ring)

lemma denominator_fderiv_apply (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x v : Vector N) :
    (fderiv ℝ (denominator β H h) x) v =
      2*∫ u, (psi h x u)^2*(fderiv ℝ (fun y => logPsi h y u) x) v ∂gibbsLaw N β H := by
  have he : scalarNumerator β H h (fun _ => (1:ℝ)) = denominator β H h := by
    funext y; simp only [scalarNumerator, denominator, mul_one]
  have hd := scalarNumerator_fderiv_apply hN β hH hh (a := fun _ => (1:ℝ)) contDiff_const x v
  simpa only [he, mul_one] using hd

lemma scalarAverage_eq_integral (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : Vector N → ℝ) (x : Vector N) :
    scalarAverage β H h a x = ∫ u, a u ∂weightedLaw β H h x := by
  rw [integral_weightedLaw hN β hH hh x]
  rfl


end
end SlowEquilibration.SphericalBarycenter
