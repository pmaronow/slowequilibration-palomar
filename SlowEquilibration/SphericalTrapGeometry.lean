module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenter
public import SlowEquilibration.BumpGeometry

@[expose] public section

/-! # Literal spherical cap geometry for trapping image balls -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace
variable {N : ℕ}

/-- Positive alignment constructs an actual spherical cap center for every
nearby aligned image, at the exact source latitude q−ρ. -/
theorem displacementBall_cap (hN : 1 ≤ N) (B : Vector N → Vector N)
    (G : Set (Vector N)) (q ρ : ℝ) (hρ : 0 ≤ ρ) (hρq : ρ < q)
    (hB : ∀ y, OnSphere y → ‖B y‖ ≤ 1)
    (hA : ∀ y ∈ G, OnSphere y → q ≤ inner ℝ (spin y) (B y))
    (x : Vector N) (hx : OnSphere x) (hxG : x ∈ G) :
    ∃ v : Vector N, OnSphere v ∧ ∀ y, OnSphere y → y ∈ G →
      ‖B y-B x‖ ≤ ρ → y ∈ cap v (q-ρ) := by
  have hq : 0 < q := hρ.trans_lt hρq
  have hpos := SlowEquilibration.norm_pos_of_unit_alignment (spin x) (B x) q
    (spin_norm hN x hx) (hA x hxG hx) hq
  let b := ‖B x‖⁻¹ • B x
  have hb : ‖b‖ = 1 := SlowEquilibration.normalized_direction_norm (B x) hpos
  let v : Vector N := Real.sqrt (N:ℝ) • b
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hr : Real.sqrt (N:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNp).ne'
  have hv : OnSphere v := by
    rw [onSphere_iff_norm_sq]
    dsimp [v]
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), hb, mul_one,
      Real.sq_sqrt hNp.le]
  have hspin : spin v = b := by
    dsimp [spin, v]
    rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
  refine ⟨v,hv,?_⟩
  intro y hy hyG hdist
  have hc := SlowEquilibration.normalized_direction_cap (spin x) (spin y) (B x) (B y) q (ρ/2)
    (spin_norm hN x hx) (spin_norm hN y hy) (hA x hxG hx) (hA y hyG hy)
    (hB x hx) (by linarith) (by positivity) (by linarith)
  change q-ρ ≤ overlap y v
  rw [← spin_inner hN, hspin]
  convert hc.2 using 1 <;> ring

end
end SlowEquilibration.SphericalBarycenter
