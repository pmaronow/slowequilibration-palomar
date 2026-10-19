-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCuspContact
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

@[expose] public section
noncomputable section
namespace SlowEquilibration.RealAnalyticCuspNormalForm
open Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An analytic unit can be absorbed into a genuine analytic coordinate, with
an actual local analytic inverse tangent to the identity. -/
theorem analytic_unit_coordinate {k : ℕ} (hk : 0 < k) {ψ : ℝ → ℝ}
    (hψ : AnalyticAt ℝ ψ 0) (hψ0 : ψ 0 = 1) :
    ∃ (T g : ℝ → ℝ), AnalyticAt ℝ T 0 ∧ AnalyticAt ℝ g 0 ∧
      T 0 = 0 ∧ g 0 = 0 ∧ HasDerivAt T 1 0 ∧ HasDerivAt g 1 0 ∧
      (∀ᶠ y in 𝓝 (0 : ℝ), T y ^ k = y ^ k * ψ y) ∧
      (∀ᶠ y in 𝓝 (0 : ℝ), g (T y) = y) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), T (g t) = t) ∧
      (fun t : ℝ => g t - t) =O[𝓝 (0 : ℝ)] (fun t => t ^ 2) := by
  let η : ℝ → ℝ := fun y => Real.exp (Real.log (ψ y) / (k : ℝ))
  let T : ℝ → ℝ := fun y => y * η y
  have hη : AnalyticAt ℝ η 0 := ((hψ.log (by rw [hψ0]; norm_num)).div_const).rexp'
  have hη0 : η 0 = 1 := by simp [η, hψ0]
  have hT : AnalyticAt ℝ T 0 := analyticAt_id.mul hη
  have hT0 : T 0 = 0 := by simp [T]
  have hd : HasDerivAt T 1 0 := by
    simpa only [Pi.mul_def, id_eq, hη0, one_mul, zero_mul, add_zero, T] using
      (hasDerivAt_id (0 : ℝ)).mul hη.differentiableAt.hasDerivAt
  have hdn : deriv T 0 ≠ 0 := by rw [hd.deriv]; norm_num
  let g := hT.hasStrictDerivAt.localInverse T (deriv T 0) 0 hdn
  have hg : AnalyticAt ℝ g 0 := by
    simpa only [hT0] using hT.analyticAt_localInverse hdn
  have hl : ∀ᶠ y in 𝓝 (0 : ℝ), g (T y) = y :=
    hT.hasStrictDerivAt.eventually_left_inverse hdn
  have hr : ∀ᶠ t in 𝓝 (0 : ℝ), T (g t) = t := by
    simpa only [hT0] using hT.hasStrictDerivAt.eventually_right_inverse hdn
  have hg0 : g 0 = 0 := by simpa only [hT0] using hl.self_of_nhds
  have hgd : HasDerivAt g 1 0 := by
    simpa only [hT0, hd.deriv, inv_one] using
      (hT.hasStrictDerivAt.to_localInverse hdn).hasDerivAt
  refine ⟨T, g, hT, hg, hT0, hg0, hd, hgd, ?_, hl, hr, ?_⟩
  · have hp : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < ψ y :=
      hψ.continuousAt.eventually (lt_mem_nhds (by rw [hψ0]; norm_num))
    filter_upwards [hp] with y hy
    dsimp only [T, η]
    rw [mul_pow, ← Real.exp_nat_mul]
    have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [mul_div_cancel₀ _ hkr, Real.exp_log hy]
  · have hgO : (fun t : ℝ => g t) =O[𝓝 (0 : ℝ)] (fun t => t) := by
      simpa only [hg0, sub_zero] using hgd.differentiableAt.isBigO_sub
    have hηat : DifferentiableAt ℝ η (g 0) := by simpa only [hg0] using hη.differentiableAt
    have hηg : DifferentiableAt ℝ (fun t => η (g t)) 0 :=
      hηat.comp 0 hgd.differentiableAt
    have hηO : (fun t : ℝ => η (g t) - 1) =O[𝓝 (0 : ℝ)] (fun t => t) := by
      simpa only [hg0, hη0, sub_zero] using hηg.isBigO_sub
    have hprod := (hgO.mul hηO).neg_left
    apply hprod.congr' ?_ ?_
    · filter_upwards [hr] with t ht
      change g t * η (g t) = t at ht
      nlinarith
    · exact Filter.Eventually.of_forall (fun t => by ring)

/-- The exact cusp factorization admits a local root coordinate with the
source's temperature parameter `ε = a*t^k`, rather than a modified parameter. -/
theorem rational_normal_form {A : ℝ → ℝ} {q M a : ℝ} {k : ℕ}
    (hk : 0 < k) {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 1)
    (hfact : ∀ᶠ y in 𝓝 (0 : ℝ), A (q + y) = M * (1 - a * y ^ k * φ y)) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ g 0 = 0 ∧ HasDerivAt g 1 0 ∧
      (fun t : ℝ => g t - t) =O[𝓝 (0 : ℝ)] (fun t => t ^ 2) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), A (q + g t) = M / (1 + a * t ^ k) := by
  let d : ℝ → ℝ := fun y => 1 - a * y ^ k * φ y
  have hd : AnalyticAt ℝ d 0 := analyticAt_const.sub
    ((analyticAt_const.mul (analyticAt_id.pow k)).mul hφ)
  have hd0 : d 0 = 1 := by simp [d, zero_pow hk.ne']
  let ψ : ℝ → ℝ := fun y => φ y / d y
  have hψ : AnalyticAt ℝ ψ 0 := hφ.div hd (by rw [hd0]; norm_num)
  have hψ0 : ψ 0 = 1 := by simp [ψ, hφ0, hd0]
  obtain ⟨T,g,hT,hg,hT0,hg0,hTd,hgd,hpow,hl,hr,hO⟩ :=
    analytic_unit_coordinate hk hψ hψ0
  refine ⟨g,hg,hg0,hgd,hO,?_⟩
  have ht : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [hg0] using hg.continuousAt.tendsto
  have hdn : ∀ᶠ y in 𝓝 (0 : ℝ), d y ≠ 0 :=
    hd.continuousAt.eventually_ne (by rw [hd0]; norm_num)
  filter_upwards [ht.eventually hfact, ht.eventually hpow, ht.eventually hdn,hr]
    with t hfactt hpowt hdnt hrt
  rw [hrt] at hpowt
  have he : (1 + a * t ^ k) * d (g t) = 1 := by
    dsimp only [ψ] at hpowt
    have heq := (eq_div_iff hdnt).mp (by simpa only [← mul_div_assoc] using hpowt)
    calc
      _ = d (g t) + a * (t ^ k * d (g t)) := by ring
      _ = d (g t) + a * (g t ^ k * φ (g t)) := by rw [heq]
      _ = 1 := by dsimp only [d]; ring
  have hn : 1 + a * t ^ k ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    norm_num at he
  apply (eq_div_iff hn).mpr
  rw [hfactt]
  change M * d (g t) * (1 + a * t ^ k) = M
  calc
    _ = M * ((1 + a * t ^ k) * d (g t)) := by ring
    _ = _ := by rw [he, mul_one]

end SlowEquilibration.RealAnalyticCuspNormalForm

namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology

/-- Actual source normal form at the literal rightmost maximizer. Both signs
of its coordinate parameterize the two roots at `ε = a*h^(2m)`. -/
theorem qD_rational_normal_form (μ : InfiniteMixture)
    (hgap : Thresholds.dynamicalThreshold μ.xi < Thresholds.staticThreshold μ.xi) :
    ∃ (m : ℕ) (a : ℝ) (g : ℝ → ℝ), 1 ≤ m ∧ 0 < a ∧
      AnalyticAt ℝ g 0 ∧ g 0 = 0 ∧ HasDerivAt g 1 0 ∧
      (fun t : ℝ => g t - t) =O[𝓝 (0 : ℝ)] (fun t => t ^ 2) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), μ.A (μ.qD + g t) = μ.Amax / (1 + a * t ^ (2 * m)) := by
  obtain ⟨m,a,φ,hm,ha,hφ,hφ0,hfact⟩ := μ.qD_even_contact hgap
  obtain ⟨g,hg,hg0,hgd,hO,hform⟩ :=
    RealAnalyticCuspNormalForm.rational_normal_form (by omega : 0 < 2 * m) hφ hφ0 hfact
  exact ⟨m,a,g,hm,ha,hg,hg0,hgd,hO,hform⟩

end SlowEquilibration.InfiniteMixture
