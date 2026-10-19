module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterGradientBounds
public import SlowEquilibration.ConstantIntervalDerivative

@[expose] public section

/-! # Actual collar localization of the overlap-weighted barycenter energy -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- The literal overlap collar in the source. -/
def collar (x : Vector N) (q₁ q₂ : ℝ) : Set (Vector N) :=
  {u | overlap x u ∈ Icc q₁ q₂}

lemma collar_measurable (x : Vector N) (q₁ q₂ : ℝ) : MeasurableSet (collar x q₁ q₂) := by
  exact measurableSet_Icc.preimage (by unfold overlap; fun_prop)

lemma psiSq_le_one (hN : 1 ≤ N) {h : ℝ → ℝ}
    (hnonneg : ∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ h r) (x u : Vector N)
    (hx : OnSphere x) (hu : OnSphere u) : (psi h x u)^2 ≤ 1 := by
  rw [psi_sq, Real.exp_le_one_iff]
  have hr := hnonneg _ (overlap_mem_Icc_of_norm_sq hN x u ((onSphere_iff_norm_sq x).mp hx)
    ((onSphere_iff_norm_sq u).mp hu))
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) N]) hr

/-- Closed-interval plateaus really force vanishing weight derivative off
the collar, including either extreme overlap endpoint. -/
lemma deriv_zero_off_collar {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K q₁ q₂ : ℝ)
    (hq₁ : -1 < q₁) (hlow : ∀ r ∈ Icc (-1:ℝ) q₁, h r = K)
    (hhigh : ∀ r ∈ Icc q₂ 1, h r = 0) (r : ℝ) (hr : r ∈ Icc (-1:ℝ) 1)
    (hnot : r ∉ Icc q₁ q₂) : deriv h r = 0 := by
  by_cases hlo : r < q₁
  · exact SlowEquilibration.deriv_eq_zero_of_constant_Icc hq₁ ⟨hr.1,hlo.le⟩
      ((hh.differentiable (by simp)) r) hlow
  · have hgt : q₂ < r := by
      apply lt_of_not_ge
      intro he
      exact hnot ⟨le_of_not_gt hlo,he⟩
    exact SlowEquilibration.deriv_eq_zero_of_constant_Icc (hgt.trans_le hr.2) ⟨hgt.le,hr.2⟩
      ((hh.differentiable (by simp)) r) hhigh

/-- The actual ψ-gradient energy localizes to the literal Gibbs collar.
All derivative vanishing and ψ≤1 statements follow from true plateaus. -/
theorem weight_energy_le_collar (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K q₁ q₂ M : ℝ)
    (hq₁ : -1 < q₁) (hM : 0 ≤ M)
    (hnonneg : ∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ h r)
    (hd : ∀ r ∈ Icc (-1:ℝ) 1, |deriv h r| ≤ M)
    (hlow : ∀ r ∈ Icc (-1:ℝ) q₁, h r = K)
    (hhigh : ∀ r ∈ Icc q₂ 1, h r = 0) (x : Vector N) (hx : OnSphere x) :
    (∫ u, ‖surfaceGradient (fun y => psi h y u) x‖^2 ∂gibbsLaw N β H) ≤
      (N:ℝ)*M^2*(gibbsLaw N β H).real (collar x q₁ q₂) := by
  let := gibbsLaw_probability hN β hH
  have hp : Continuous (fun u : Vector N => psi h x u) :=
    (psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)
  have hg : Continuous (fun u : Vector N => surfaceGradient (fun y => psi h y u) x) := by
    have he : (fun u : Vector N => surfaceGradient (fun y => psi h y u) x) =
        fun u => psi h x u • score h x u := funext (psi_surfaceGradient hN hh x)
    rw [he]
    exact hp.smul (score_continuous hN hh x)
  have hgrad := integrable_gibbs_of_continuous hN β hH (hg.norm.pow 2)
  have hbound := integral_mono_ae hgrad
    ((integrable_const ((N:ℝ)*M^2)).indicator (collar_measurable x q₁ q₂)) (by
      filter_upwards [gibbsLaw_support hN β H] with u hu
      have huS := (onSphere_iff_norm_sq u).mpr hu
      change ‖surfaceGradient (fun y => psi h y u) x‖^2 ≤
        (collar x q₁ q₂).indicator (fun _ => (N:ℝ)*M^2) u
      by_cases hc : u ∈ collar x q₁ q₂
      · rw [Set.indicator_of_mem hc, psi_surfaceGradient hN hh, norm_smul,
          mul_pow, Real.norm_eq_abs, sq_abs]
        calc
          (psi h x u)^2*‖score h x u‖^2 ≤ 1*‖score h x u‖^2 :=
            mul_le_mul_of_nonneg_right (psiSq_le_one hN hnonneg x u hx huS) (sq_nonneg _)
          _ ≤ _ := by simpa only [one_mul] using score_norm_sq_le hN hh M hM hd x u hx huS
      · have hr := overlap_mem_Icc_of_norm_sq hN x u ((onSphere_iff_norm_sq x).mp hx) hu
        have hz := deriv_zero_off_collar hh K q₁ q₂ hq₁ hlow hhigh (overlap x u) hr hc
        rw [Set.indicator_of_notMem hc, psi_surfaceGradient hN hh, score_eq hN hh,
          hz, neg_zero, zero_smul, smul_zero, norm_zero, zero_pow (by norm_num)] )
  rw [integral_indicator (collar_measurable x q₁ q₂), setIntegral_const] at hbound
  simp only [smul_eq_mul] at hbound
  convert! hbound using 1 <;> ring

/-- The exact localized source Hilbert--Schmidt bound is obtained for the
actual smooth Gibbs barycenter. -/
theorem barycenter_jacobian_le_collar (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K q₁ q₂ M : ℝ)
    (hq₁ : -1 < q₁) (hM : 0 ≤ M)
    (hnonneg : ∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ h r)
    (hd : ∀ r ∈ Icc (-1:ℝ) 1, |deriv h r| ≤ M)
    (hlow : ∀ r ∈ Icc (-1:ℝ) q₁, h r = K)
    (hhigh : ∀ r ∈ Icc q₂ 1, h r = 0) (x : Vector N) (hx : OnSphere x) :
    surfaceJacobianNormSq (barycenter β H h) x ≤
      4*(N:ℝ)*M^2*(gibbsLaw N β H).real (collar x q₁ q₂)/denominator β H h x := by
  have he := barycenter_jacobian_le_weight_energy hN β hH hh x
  have hc := weight_energy_le_collar hN β hH hh K q₁ q₂ M hq₁ hM hnonneg hd hlow hhigh x hx
  have hdpos := denominator_pos hN β hH hh x
  have hm := mul_le_mul_of_nonneg_left hc (div_nonneg (by norm_num : (0:ℝ) ≤ 4) hdpos.le)
  exact he.trans (by convert! hm using 1 <;> ring)

end
end SlowEquilibration.SphericalBarycenter
