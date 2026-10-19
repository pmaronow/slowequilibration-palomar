-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit

@[expose] public section
noncomputable section

namespace SlowEquilibration.LocalConvexDerivativeLimit

open Set Filter
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Convex finite-volume derivatives converge at an interior point using
only local pointwise pressure convergence. -/
theorem deriv_tendsto_of_convex_local_pointwise
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a δ : ℝ) (hδ : 0 < δ)
    (hconv : ∀ n, ConvexOn ℝ univ (f n))
    (hdiff : ∀ n, DifferentiableAt ℝ (f n) a)
    (hpoint : ∀ t ∈ Ioo (a-δ) (a+δ),
      Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hg : DifferentiableAt ℝ g a) :
    Tendsto (fun n => deriv (f n) a) atTop (𝓝 (deriv g a)) := by
  have ha : a ∈ Ioo (a-δ) (a+δ) := by constructor <;> linarith
  have hlocal : Ioo (a-δ) (a+δ) ∈ 𝓝 a := isOpen_Ioo.mem_nhds ha
  have hslope (x y : ℝ) (hx : x ∈ Ioo (a-δ) (a+δ))
      (hy : y ∈ Ioo (a-δ) (a+δ)) :
      Tendsto (fun n => slope (f n) x y) atTop (𝓝 (slope g x y)) := by
    simpa only [slope_def_field] using
      ((hpoint y hy).sub (hpoint x hx)).div_const (y - x)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    have hs : Tendsto (slope g a) (𝓝[<] a) (𝓝 (deriv g a)) :=
      (hg.hasDerivAt.tendsto_slope).mono_left (nhdsLT_le_nhdsNE a)
    obtain ⟨x, hxall⟩ :=
      (((tendsto_order.1 hs).1 c hc).and self_mem_nhdsWithin).and
        (nhdsWithin_le_nhds hlocal) |>.exists
    rcases hxall with ⟨⟨hcx,hxa⟩,hx⟩
    have hsl : ∀ᶠ n in atTop, c < slope (f n) x a := by
      have hcx' : c < slope g x a := by rwa [slope_comm] at hcx
      exact (tendsto_order.1 (hslope x a hx ha)).1 c hcx'
    filter_upwards [hsl] with n hn
    exact hn.trans_le ((hconv n).slope_le_deriv (mem_univ x)
      (mem_univ a) hxa (hdiff n))
  · intro c hc
    have hs : Tendsto (slope g a) (𝓝[>] a) (𝓝 (deriv g a)) :=
      (hg.hasDerivAt.tendsto_slope).mono_left (nhdsGT_le_nhdsNE a)
    obtain ⟨y, hyall⟩ :=
      (((tendsto_order.1 hs).2 c hc).and self_mem_nhdsWithin).and
        (nhdsWithin_le_nhds hlocal) |>.exists
    rcases hyall with ⟨⟨hcy,hay⟩,hy⟩
    have hsr : ∀ᶠ n in atTop, slope (f n) a y < c :=
      (tendsto_order.1 (hslope a y ha hy)).2 c hcy
    filter_upwards [hsr] with n hn
    exact ((hconv n).deriv_le_slope (mem_univ a)
      (mem_univ y) hay (hdiff n)).trans_lt hn

end SlowEquilibration.LocalConvexDerivativeLimit
