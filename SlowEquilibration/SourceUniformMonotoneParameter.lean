-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.UniformLipschitzConvergence

/-! A Pólya-type criterion: increasing functions converging pointwise to a
continuous limit converge uniformly on compact parameter sets. -/
@[expose] public section
namespace SlowEquilibration.SourceUniformMonotoneParameter
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Monotonicity in the parameter supplies the uniformity needed in the
pure-model Laplace estimates, without differentiating the parameterized integral. -/
theorem uniform_on_compact_of_monotone
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, Monotone (F n)) (hf : Continuous f)
    (hpoint : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (f t)))
    {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε4 : 0 < ε/4 := by positivity
  let δ : S → ℝ := fun x =>
    Classical.choose ((Metric.continuous_iff.mp hf) x.val (ε/4) hε4)
  have hδ (x : S) : 0 < δ x ∧
      ∀ y, dist y x.val < δ x → dist (f y) (f x.val) < ε/4 := by
    exact Classical.choose_spec ((Metric.continuous_iff.mp hf) x.val (ε/4) hε4)
  obtain ⟨T,hcover⟩ := hS.elim_finite_subcover
    (fun c : S => Metric.ball c.val (δ c/4))
    (fun _ => Metric.isOpen_ball) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y,hy⟩,by simp [hδ ⟨y,hy⟩ |>.1]⟩)
  have hevent : ∀ c∈T,∀ᶠ n : ℕ in atTop,
      dist (F n (c.val-δ c/2)) (f (c.val-δ c/2)) < ε/4 ∧
      dist (F n (c.val+δ c/2)) (f (c.val+δ c/2)) < ε/4 := by
    intro c hc
    exact ((hpoint (c.val-δ c/2)).eventually
      (ball_mem_nhds (f (c.val-δ c/2)) hε4)).and
      ((hpoint (c.val+δ c/2)).eventually
      (ball_mem_nhds (f (c.val+δ c/2)) hε4))
  filter_upwards [T.eventually_all.mpr hevent] with n hn y hy
  obtain ⟨c,hc,hcy⟩ := mem_iUnion₂.mp (hcover hy)
  have hcy' : |y-c.val| < δ c/4 := by simpa [Real.dist_eq] using hcy
  have hleft : c.val-δ c/2 ≤ y := by
    rcases abs_lt.mp hcy' with ⟨hlo,_⟩
    linarith [hδ c |>.1]
  have hright : y ≤ c.val+δ c/2 := by
    rcases abs_lt.mp hcy' with ⟨_,hhi⟩
    linarith [hδ c |>.1]
  have hcLeft : dist (c.val-δ c/2) c.val < δ c := by
    rw [Real.dist_eq]
    have hp := hδ c |>.1
    have hq : 0 ≤ δ c/2 := by positivity
    rw [show c.val-δ c/2-c.val = -(δ c/2) by ring, abs_neg, abs_of_nonneg hq]
    linarith
  have hcRight : dist (c.val+δ c/2) c.val < δ c := by
    rw [Real.dist_eq]
    have hp := hδ c |>.1
    have hq : 0 ≤ δ c/2 := by positivity
    rw [show c.val+δ c/2-c.val = δ c/2 by ring, abs_of_nonneg hq]
    linarith
  have hcY : dist y c.val < δ c := by
    rw [Real.dist_eq]
    exact hcy'.trans (by linarith [hδ c |>.1])
  have hfl := (hδ c).2 _ hcLeft
  have hfr := (hδ c).2 _ hcRight
  have hfy := (hδ c).2 _ hcY
  have hnl := (hn c hc).1
  have hnr := (hn c hc).2
  have hmonoL := hF n hleft
  have hmonoR := hF n hright
  simp only [Real.dist_eq] at hfl hfr hfy hnl hnr ⊢
  rw [abs_sub_comm (f y) (F n y)]
  apply abs_lt.mpr
  constructor <;> rcases abs_lt.mp hfl with ⟨hfl₁,hfl₂⟩
    <;> rcases abs_lt.mp hfr with ⟨hfr₁,hfr₂⟩
    <;> rcases abs_lt.mp hfy with ⟨hfy₁,hfy₂⟩
    <;> rcases abs_lt.mp hnl with ⟨hnl₁,hnl₂⟩
    <;> rcases abs_lt.mp hnr with ⟨hnr₁,hnr₂⟩
    <;> linarith

end
end SlowEquilibration.SourceUniformMonotoneParameter
