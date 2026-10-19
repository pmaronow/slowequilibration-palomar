module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterCollar
public import SlowEquilibration.SphericalBarycenterAlignment

@[expose] public section

/-! # Literal barycenter energy from deterministic collar ratios -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- The literal barycenter's vector Dirichlet energy follows from a true
collar/denominator bound on a measurable good set and its Gibbs complement
mass. The analytic energy is derived, rather than supplied as a premise. -/
theorem barycenter_energy_le_of_collar_ratio (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K q₁ q₂ M A : ℝ)
    (hq₁ : -1 < q₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hnonneg : ∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ h r)
    (hd : ∀ r ∈ Icc (-1:ℝ) 1, |deriv h r| ≤ M)
    (hlow : ∀ r ∈ Icc (-1:ℝ) q₁, h r = K)
    (hhigh : ∀ r ∈ Icc q₂ 1, h r = 0) (G : Set (Vector N)) (hG : MeasurableSet G)
    (hRatio : ∀ x ∈ G, OnSphere x →
      (gibbsLaw N β H).real (collar x q₁ q₂)/denominator β H h x ≤ A) :
    vectorDirichletEnergy β H (barycenter β H h) ≤
      4*(N:ℝ)*M^2*(A+(gibbsLaw N β H).real Gᶜ) := by
  let := gibbsLaw_probability hN β hH
  let C : ℝ := 4*(N:ℝ)*M^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : ContDiff ℝ 1 (barycenter β H h) := (barycenter_contDiff hN β hH hh).of_le (by simp)
  have hJ : Continuous (surfaceJacobianNormSq (barycenter β H h)) := by
    unfold surfaceJacobianNormSq
    exact continuous_finsetSum _ (fun a _ => (surfaceGradient_continuous
      (contDiff_vector_coordinate hB a)).norm.pow 2)
  have hiGood : Integrable (G.indicator (fun _ => C*A)) (gibbsLaw N β H) :=
    (integrable_const (C*A)).indicator hG
  have hiBad : Integrable (Gᶜ.indicator (fun _ => C)) (gibbsLaw N β H) :=
    (integrable_const C).indicator hG.compl
  have hpt : ∀ᵐ x ∂gibbsLaw N β H,
      surfaceJacobianNormSq (barycenter β H h) x ≤
        G.indicator (fun _ => C*A) x+Gᶜ.indicator (fun _ => C) x := by
    filter_upwards [gibbsLaw_support hN β H] with x hx
    have hxS := (onSphere_iff_norm_sq x).mpr hx
    by_cases hxG : x ∈ G
    · rw [Set.indicator_of_mem hxG, Set.indicator_of_notMem (show x ∉ Gᶜ from by simpa), add_zero]
      have he := barycenter_jacobian_le_collar hN β hH hh K q₁ q₂ M hq₁ hM hnonneg hd hlow hhigh x hxS
      have hm := mul_le_mul_of_nonneg_left (hRatio x hxG hxS) hC
      exact he.trans (by convert! hm using 1 <;> ring)
    · rw [Set.indicator_of_notMem hxG, Set.indicator_of_mem (show x ∈ Gᶜ from hxG), zero_add]
      exact barycenter_jacobian_le hN β hH hh M hM hd x hxS
  have hi := integral_mono_ae (integrable_gibbs_of_continuous hN β hH hJ) (hiGood.add hiBad) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add hiGood hiBad, integral_indicator hG, integral_indicator hG.compl,
    setIntegral_const, setIntegral_const] at hi
  simp only [smul_eq_mul] at hi
  rw [vectorDirichletEnergy_eq_integral hN β hH hB]
  have hm : (gibbsLaw N β H).real G ≤ 1 := measureReal_le_one
  have hbound := mul_le_mul_of_nonneg_right hm (mul_nonneg hC hA)
  change (∫ x, surfaceJacobianNormSq (barycenter β H h) x ∂gibbsLaw N β H) ≤ C*(A+(gibbsLaw N β H).real Gᶜ)
  nlinarith

end
end SlowEquilibration.SphericalBarycenter
