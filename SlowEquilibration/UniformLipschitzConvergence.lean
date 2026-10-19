-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Real.Lemmas

/-! A uniformly Lipschitz family converging pointwise converges uniformly on
any compact set. The proof uses an actual finite metric cover. -/

@[expose] public section
namespace SlowEquilibration.UniformLipschitzConvergence

open Set Filter Metric
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compact uniform convergence from a common positive Lipschitz constant. -/
theorem uniform_on_compact {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {L : ℝ≥0}
    (hL : 0<L) (hF : ∀ n,LipschitzWith L (F n)) (hf : LipschitzWith L f)
    (ht : ∀ k,Tendsto (fun n => F n k) atTop (𝓝 (f k)))
    {S : Set ℝ} (hS : IsCompact S) : TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let δ : ℝ := eps/(4*(L:ℝ))
  have hδ : 0<δ := div_pos heps (mul_pos (by norm_num) hL)
  obtain ⟨T,hcover⟩ := hS.elim_finite_subcover
    (fun c : S => Metric.ball (c : ℝ) δ) (fun _ => Metric.isOpen_ball) (by
      intro k hk
      exact mem_iUnion.mpr ⟨⟨k,hk⟩,by simpa using hδ⟩)
  have hevent : ∀ c∈T,∀ᶠ n : ℕ in atTop,dist (F n c.val) (f c.val)<eps/2 := by
    intro c hc
    exact (ht c).eventually (ball_mem_nhds (f c.val) (by positivity))
  filter_upwards [T.eventually_all.mpr hevent] with n hn
  intro k hk
  obtain ⟨c,hc,hkc⟩ := mem_iUnion₂.mp (hcover hk)
  have hkd : dist k c.val<δ := hkc
  have hnd := (hF n).dist_le_mul k c.val
  have hfd := hf.dist_le_mul c.val k
  rw [dist_comm c.val k] at hfd
  have hlocal : (L:ℝ)*dist k c.val<eps/4 := by
    have h := mul_lt_mul_of_pos_left hkd hL
    have he : (L:ℝ)*δ=eps/4 := by dsimp only [δ];field_simp
    exact lt_of_lt_of_eq h he
  rw [dist_comm (f k) (F n k)]
  calc
    dist (F n k) (f k)≤dist (F n k) (F n c.val)+dist (F n c.val) (f c.val)+dist (f c.val) (f k) :=
      (dist_triangle _ _ _).trans (by linarith [dist_triangle (F n c.val) (f c.val) (f k)])
    _<eps := by linarith [hn c hc]

end SlowEquilibration.UniformLipschitzConvergence
