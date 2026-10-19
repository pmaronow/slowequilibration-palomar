module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalSmoothIntegrals
public import SlowEquilibration.SphericalCapMass
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! # The literal overlap-weighted spherical Gibbs barycenter -/

namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators

variable {N : ℕ}

/-- The actual normalized spin in the manuscript. -/
def spin (x : Vector N) : Vector N := (Real.sqrt (N:ℝ))⁻¹ • x

lemma spin_contDiff : ContDiff ℝ ∞ (spin : Vector N → Vector N) := by
  unfold spin
  exact contDiff_id.const_smul _

lemma spin_norm (hN : 1 ≤ N) (x : Vector N) (hx : OnSphere x) : ‖spin x‖ = 1 := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hroot := Real.sqrt_pos.mpr hNp
  have hxnorm : ‖x‖ = Real.sqrt (N:ℝ) := by
    rw [← (onSphere_iff_norm_sq x).mp hx, Real.sqrt_sq (norm_nonneg x)]
  rw [spin, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hroot.le), hxnorm,
    inv_mul_cancel₀ hroot.ne']

lemma spin_inner (hN : 1 ≤ N) (x u : Vector N) : inner ℝ (spin x) (spin u) = overlap x u := by
  have hNp : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hr : Real.sqrt (N:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [spin, spin, real_inner_smul_left, real_inner_smul_right, overlap]
  field_simp
  simp [hs, mul_comm]

/-- The actual positive overlap weight. -/
def psi (h : ℝ → ℝ) (x u : Vector N) : ℝ := Real.exp (-(N:ℝ)*h (overlap x u))

lemma psi_pos (h : ℝ → ℝ) (x u : Vector N) : 0 < psi h x u := Real.exp_pos _

lemma psi_sq (h : ℝ → ℝ) (x u : Vector N) :
    (psi h x u)^2 = Real.exp (-2*(N:ℝ)*h (overlap x u)) := by
  rw [psi, pow_two, ← Real.exp_add]
  congr 1
  ring

lemma psi_joint_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : Vector N × Vector N => psi h q.2 q.1) := by
  have hR : ContDiff ℝ ∞ (fun q : Vector N × Vector N => overlap q.2 q.1) :=
    (contDiff_snd.inner ℝ contDiff_fst).div_const _
  exact Real.contDiff_exp.comp (contDiff_const.mul (hh.comp hR))

/-- Literal denominator d_N, with the actual Gibbs measure. -/
def denominator (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x : Vector N) : ℝ :=
  ∫ u, (psi h x u)^2 ∂gibbsLaw N β H

/-- Literal unnormalized vector Gibbs moment. -/
def numerator (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x : Vector N) : Vector N :=
  ∫ u, (psi h x u)^2 • spin u ∂gibbsLaw N β H

/-- The actual overlap-weighted Gibbs mean B_N=n_N/d_N. -/
def barycenter (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x : Vector N) : Vector N :=
  (denominator β H h x)⁻¹ • numerator β H h x

lemma denominator_contDiff (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (denominator β H h) :=
  gibbsIntegral_contDiff hN β hH (fun u x => (psi h x u)^2) ((psi_joint_contDiff hh).pow 2)

lemma numerator_joint_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : Vector N × Vector N => (psi h q.2 q.1)^2 • spin q.1) :=
  ((psi_joint_contDiff hh).pow 2).smul (spin_contDiff.comp contDiff_fst)

lemma numerator_contDiff (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (numerator β H h) :=
  gibbsIntegral_contDiff hN β hH (fun u x => (psi h x u)^2 • spin u) (numerator_joint_contDiff hh)

lemma denominator_pos (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    0 < denominator β H h x := by
  let := gibbsLaw_probability hN β hH
  unfold denominator
  simp_rw [psi_sq]
  apply integral_exp_pos
  apply integrable_gibbs_of_continuous hN β hH
  have hR : Continuous (fun u : Vector N => overlap x u) := by unfold overlap; fun_prop
  exact Real.continuous_exp.comp ((hh.continuous.comp hR).const_mul (-2*(N:ℝ)))

/-- Smoothness of the literal Gibbs barycenter is a proved actual integral
and quotient result, with no barycenter regularity premise. -/
theorem barycenter_contDiff (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (barycenter β H h) :=
  ((denominator_contDiff hN β hH hh).inv (fun x => (denominator_pos hN β hH hh x).ne')).smul
    (numerator_contDiff hN β hH hh)

/-- The actual Gibbs denominator has the source's literal lower bound. -/
theorem denominator_lower (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K : ℝ)
    (hbound : ∀ r ∈ Icc (-1:ℝ) 1, h r ≤ K) (x : Vector N) (hx : OnSphere x) :
    Real.exp (-2*K*(N:ℝ)) ≤ denominator β H h x := by
  let := gibbsLaw_probability hN β hH
  have hp : Continuous (fun u : Vector N => (psi h x u)^2) :=
    ((psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hb : ∀ᵐ u ∂gibbsLaw N β H, Real.exp (-2*K*(N:ℝ)) ≤ (psi h x u)^2 := by
    filter_upwards [gibbsLaw_support hN β H] with u hu
    have hv := hbound (overlap x u)
      (overlap_mem_Icc_of_norm_sq hN x u ((onSphere_iff_norm_sq x).mp hx) hu)
    rw [psi_sq]
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hi := integral_mono_ae (integrable_const _) (integrable_gibbs_of_continuous hN β hH hp) hb
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  convert! hi using 1

/-- The actual barycenter is the mean of normalized spins, hence has norm
at most one at every ambient point. -/
theorem barycenter_norm_le_one (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    ‖barycenter β H h x‖ ≤ 1 := by
  have hpos := denominator_pos hN β hH hh x
  have he : (∫ u, ‖(psi h x u)^2 • spin u‖ ∂gibbsLaw N β H) = denominator β H h x := by
    apply integral_congr_ae
    filter_upwards [gibbsLaw_support hN β H] with u hu
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _),
      spin_norm hN u ((onSphere_iff_norm_sq u).mpr hu), mul_one]
  have hn : ‖numerator β H h x‖ ≤ denominator β H h x := by
    exact (norm_integral_le_integral_norm _).trans_eq he
  rw [barycenter, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hpos.le)).trans_eq (inv_mul_cancel₀ hpos.ne')

end
end SlowEquilibration.SphericalBarycenter
