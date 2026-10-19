-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit

/-! A local convexity estimate used in the unperturbed Panchenko
self-averaging argument. It bounds the spread of two finite-volume energy
means by four values of the same finite-volume pressure. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoConvexSpread

open Set Filter
open scoped Topology
set_option autoImplicit false

def outerSecantSpread (f : ℝ → ℝ) (β δ : ℝ) : ℝ :=
  (f (β+2*δ)-f (β+δ))/δ -
    (f (β-δ)-f (β-2*δ))/δ

theorem derivative_spread_le_outer_secants
    (f : ℝ → ℝ) (β δ : ℝ) (hδ : 0 < δ)
    (hconv : ConvexOn ℝ univ f)
    (hminus : DifferentiableAt ℝ f (β-δ))
    (hplus : DifferentiableAt ℝ f (β+δ)) :
    deriv f (β+δ)-deriv f (β-δ) ≤ outerSecantSpread f β δ := by
  have hp := hconv.deriv_le_slope (mem_univ (β+δ))
    (mem_univ (β+2*δ)) (by linarith : β+δ < β+2*δ) hplus
  have hm := hconv.slope_le_deriv (mem_univ (β-2*δ))
    (mem_univ (β-δ)) (by linarith : β-2*δ < β-δ) hminus
  have hp' : deriv f (β+δ) ≤ (f (β+2*δ)-f (β+δ))/δ := by
    simpa [slope_def_field, show β+2*δ-(β+δ)=δ by ring] using hp
  have hm' : (f (β-δ)-f (β-2*δ))/δ ≤ deriv f (β-δ) := by
    simpa [slope_def_field, show β-δ-(β-2*δ)=δ by ring] using hm
  dsimp [outerSecantSpread]
  linarith

theorem outerSecantSpread_tendsto_of_pointwise
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β δ : ℝ)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t))) :
    Tendsto (fun n => outerSecantSpread (f n) β δ) atTop
      (𝓝 (outerSecantSpread g β δ)) := by
  unfold outerSecantSpread
  exact (((hpoint (β+2*δ)).sub (hpoint (β+δ))).div_const δ).sub
    (((hpoint (β-δ)).sub (hpoint (β-2*δ))).div_const δ)

/-- The four outer secants collapse at any differentiability point of the
thermodynamic pressure; no differentiability away from that point is used. -/
theorem outerSecantSpread_tendsto_zero_of_differentiable
    (g : ℝ → ℝ) (β : ℝ) (hg : DifferentiableAt ℝ g β) :
    Tendsto (fun δ => outerSecantSpread g β δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
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
      (fun δ : ℝ =>
        2*slope g β (β+2*δ)-slope g β (β+δ)+
          slope g β (β-δ)-2*slope g β (β-2*δ))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h2 := hs 2 (by norm_num)
    have h1 := hs 1 (by norm_num)
    have hm1 := hs (-1) (by norm_num)
    have hm2 := hs (-2) (by norm_num)
    have h := ((h2.const_mul 2).sub h1).add hm1 |>.sub (hm2.const_mul 2)
    convert h using 1
    all_goals simp only [one_mul, neg_mul, sub_eq_add_neg]
    all_goals ring
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδne : δ ≠ 0 := ne_of_gt hδ
  unfold outerSecantSpread
  simp only [slope_def_field, show β+2*δ-β=2*δ by ring,
    show β+δ-β=δ by ring, show β-δ-β= -δ by ring,
    show β-2*δ-β= -(2*δ) by ring]
  field_simp
  ring

theorem eventually_derivative_spread_lt
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β δ r : ℝ) (hδ : 0 < δ)
    (hconv : ∀ n, ConvexOn ℝ univ (f n))
    (hdiff : ∀ n t, DifferentiableAt ℝ (f n) t)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hr : outerSecantSpread g β δ < r) :
    ∀ᶠ n in atTop, deriv (f n) (β+δ)-deriv (f n) (β-δ) < r := by
  filter_upwards [(outerSecantSpread_tendsto_of_pointwise f g β δ hpoint).eventually
    (gt_mem_nhds hr)] with n hn
  exact (derivative_spread_le_outer_secants (f n) β δ hδ
    (hconv n) (hdiff n _) (hdiff n _)).trans_lt hn

/-- A differentiable convex pointwise limit makes the finite-volume
derivative spread arbitrarily small on one fixed neighborhood, eventually
in volume. This is the deterministic core of energy self-averaging. -/
theorem eventually_derivative_spread_small
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β r : ℝ) (hr : 0 < r)
    (hconv : ∀ n, ConvexOn ℝ univ (f n))
    (hdiff : ∀ n t, DifferentiableAt ℝ (f n) t)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hg : DifferentiableAt ℝ g β) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n in atTop, deriv (f n) (β+δ)-deriv (f n) (β-δ) < r := by
  have hs := outerSecantSpread_tendsto_zero_of_differentiable g β hg
  have he : ∀ᶠ δ in 𝓝[>] (0:ℝ), outerSecantSpread g β δ < r :=
    hs.eventually (gt_mem_nhds hr)
  have hpositive : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hsmall⟩ := (hpositive.and he).exists
  exact ⟨δ, hδ, eventually_derivative_spread_lt f g β δ r hδ
    hconv hdiff hpoint hsmall⟩

/-- An energy-fluctuation error controlled by a convex derivative spread
and an asymptotically negligible pressure-concentration term vanishes at a
differentiability point. The physical Gaussian comparison supplies the
bound in applications. -/
theorem error_tendsto_zero_of_convex_spread
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β : ℝ)
    (err concentration : ℕ → ℝ)
    (herr : ∀ n, 0 ≤ err n)
    (hconv : ∀ n, ConvexOn ℝ univ (f n))
    (hdiff : ∀ n t, DifferentiableAt ℝ (f n) t)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hg : DifferentiableAt ℝ g β)
    (hc : Tendsto concentration atTop (𝓝 0))
    (hbound : ∀ n δ, 0 < δ → δ ≤ 1 →
      err n ≤ deriv (f n) (β+δ)-deriv (f n) (β-δ)+
        concentration n/δ) :
    Tendsto err atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Filter.Eventually.of_forall fun n => hr.trans_le (herr n)
  · intro r hr
    have hs := outerSecantSpread_tendsto_zero_of_differentiable g β hg
    have he : ∀ᶠ δ in 𝓝[>] (0:ℝ),
        outerSecantSpread g β δ < r/2 :=
      hs.eventually (gt_mem_nhds (by linarith : (0:ℝ) < r/2))
    have hpositive : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
    have hsmall : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 :=
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    obtain ⟨δ, hδ, hδsmall, houter⟩ :=
      (hpositive.and (hsmall.and he)).exists
    have hspread := eventually_derivative_spread_lt
      f g β δ (r/2) hδ hconv hdiff hpoint houter
    have hcdiv : Tendsto (fun n => concentration n/δ) atTop (𝓝 0) := by
      simpa using hc.div_const δ
    have hconcentration : ∀ᶠ n in atTop, concentration n/δ < r/2 :=
      hcdiv.eventually (gt_mem_nhds (by linarith : (0:ℝ) < r/2))
    filter_upwards [hspread, hconcentration] with n hs hc'
    exact (hbound n δ hδ hδsmall.le).trans_lt (by linarith)

end SlowEquilibration.PureCapturePhysicalPanchenkoConvexSpread
