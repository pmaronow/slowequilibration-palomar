-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoConvexSpread

/-! The symmetric pressure second difference at a fixed temperature. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoSymmetricSpread

open Set Filter
open scoped Topology
set_option autoImplicit false

def symmetricSecantSpread (f : ℝ → ℝ) (β δ : ℝ) : ℝ :=
  (f (β+δ)+f (β-δ)-2*f β)/δ

theorem symmetricSecantSpread_tendsto_of_pointwise
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β δ : ℝ)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t))) :
    Tendsto (fun n => symmetricSecantSpread (f n) β δ) atTop
      (𝓝 (symmetricSecantSpread g β δ)) := by
  unfold symmetricSecantSpread
  exact (((hpoint (β+δ)).add (hpoint (β-δ))).sub
    ((hpoint β).const_mul 2)).div_const δ

theorem symmetricSecantSpread_tendsto_zero_of_differentiable
    (g : ℝ → ℝ) (β : ℝ) (hg : DifferentiableAt ℝ g β) :
    Tendsto (fun δ => symmetricSecantSpread g β δ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    change 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ)
    exact nhdsWithin_le_nhds
  have harg (c : ℝ) (hc : c ≠ 0) :
      Tendsto (fun δ : ℝ => β+c*δ) (𝓝[>] (0:ℝ)) (𝓝[≠] β) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert (tendsto_const_nhds.add (tendsto_const_nhds.mul hid)) using 1; simp
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change β+c*δ ≠ β
      intro he
      have hm : c*δ = 0 := by linarith
      exact (mul_ne_zero hc (ne_of_gt hδ)) hm
  have hs (c : ℝ) (hc : c ≠ 0) :
      Tendsto (fun δ : ℝ => slope g β (β+c*δ))
        (𝓝[>] (0:ℝ)) (𝓝 (deriv g β)) := by
    simpa only [Function.comp_def] using
      (hg.hasDerivAt.tendsto_slope).comp (harg c hc)
  have hlimit : Tendsto
      (fun δ : ℝ => slope g β (β+δ)-slope g β (β-δ))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := (hs 1 (by norm_num)).sub (hs (-1) (by norm_num))
    convert h using 1
    · funext δ
      simp only [one_mul, neg_one_mul, sub_eq_add_neg]
    · simp
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδne : δ ≠ 0 := ne_of_gt hδ
  unfold symmetricSecantSpread
  simp only [slope_def_field, show β+δ-β=δ by ring,
    show β-δ-β= -δ by ring]
  field_simp
  ring

/-- A nonnegative error bounded by the physical pressure's symmetric
second difference and a vanishing finite-size term is sublinear at every
differentiability point of the limiting pressure. -/
theorem error_tendsto_zero_of_symmetric_spread
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β : ℝ)
    (err concentration : ℕ → ℝ)
    (herr : ∀ n, 0 ≤ err n)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hg : DifferentiableAt ℝ g β)
    (hc : Tendsto concentration atTop (𝓝 0))
    (hbound : ∀ n δ, 0 < δ → δ ≤ 1 →
      err n ≤ symmetricSecantSpread (f n) β δ + concentration n/δ) :
    Tendsto err atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Filter.Eventually.of_forall fun n => hr.trans_le (herr n)
  · intro r hr
    have hs := symmetricSecantSpread_tendsto_zero_of_differentiable g β hg
    have he : ∀ᶠ δ in 𝓝[>] (0:ℝ), symmetricSecantSpread g β δ < r/2 :=
      hs.eventually (gt_mem_nhds (by linarith : (0:ℝ) < r/2))
    have hpositive : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
    have hsmall : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 :=
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    obtain ⟨δ, hδ, hδsmall, houter⟩ :=
      (hpositive.and (hsmall.and he)).exists
    have hspread : ∀ᶠ n in atTop,
        symmetricSecantSpread (f n) β δ < r/2 :=
      (symmetricSecantSpread_tendsto_of_pointwise f g β δ hpoint).eventually
        (gt_mem_nhds houter)
    have hcdiv : Tendsto (fun n => concentration n/δ) atTop (𝓝 0) := by
      simpa using hc.div_const δ
    have hconcentration : ∀ᶠ n in atTop, concentration n/δ < r/2 :=
      hcdiv.eventually (gt_mem_nhds (by linarith : (0:ℝ) < r/2))
    filter_upwards [hspread, hconcentration] with n hs hc'
    exact (hbound n δ hδ hδsmall.le).trans_lt (by linarith)

end SlowEquilibration.PureCapturePhysicalPanchenkoSymmetricSpread
