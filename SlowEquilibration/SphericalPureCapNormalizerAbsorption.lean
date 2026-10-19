-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapExteriorTailPackage
public import SlowEquilibration.SphericalLatitudeNormalization

@[expose] public section

/-! The literal spherical coarea factor is subexponential on pure cap tails. -/

namespace SlowEquilibration.SphericalPureCapNormalizerAbsorption
noncomputable section
open Set Filter
open SphericalModel
set_option autoImplicit false

/-- Every fixed prefactor times the genuine `(N−1)`-dimensional coarea
normalizer is absorbed by an arbitrarily small exponential rate. -/
theorem latitudeNormalization_mul_fixed_eventually_le_exp
    {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 2 ≤ N →
      C*(latitudeNormalization (N-1)).toReal ≤
        Real.exp ((N:ℝ)*η) := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp
    (latitudeNormalization_log_eventually_le (show 0 < η/2 by positivity))
  obtain ⟨n₁,hn₁large⟩ := exists_nat_gt (Real.log (C+1)/(η/2))
  let N₀ := max (n₀+1) (max n₁ 2)
  refine ⟨N₀,?_⟩
  intro N hNN₀ hN2
  have hn : n₀ ≤ N-1 := by dsimp [N₀] at hNN₀; omega
  have hn₁ : n₁ ≤ N := by dsimp [N₀] at hNN₀; omega
  have hdim : 1 ≤ N-1 := by omega
  have hpositive : 0 < (latitudeNormalization (N-1)).toReal :=
    ENNReal.toReal_pos (latitudeNormalization_pos hdim).ne'
      (latitudeNormalization_ne_top (N-1))
  have hlog := hn₀ (N-1) hn
  have hden : (((N-1:ℕ):ℝ)+1)=(N:ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hden] at hlog
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNorm : Real.log (latitudeNormalization (N-1)).toReal ≤
      (N:ℝ)*(η/2) := by simpa only [mul_comm] using (div_le_iff₀ hNr).mp hlog
  have hnormBound : (latitudeNormalization (N-1)).toReal ≤
      Real.exp ((N:ℝ)*(η/2)) := by
    calc
      _ = Real.exp (Real.log (latitudeNormalization (N-1)).toReal) :=
        (Real.exp_log hpositive).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogNorm
  have hC1 : 0 < C+1 := by linarith
  have hn₁r : (n₁:ℝ) ≤ N := by exact_mod_cast hn₁
  have hlogC : Real.log (C+1) ≤ (N:ℝ)*(η/2) := by
    have hh := (le_of_lt hn₁large).trans hn₁r
    simpa only [mul_comm] using (div_le_iff₀ (show 0 < η/2 by positivity)).mp hh
  have hCBound : C ≤ Real.exp ((N:ℝ)*(η/2)) := by
    calc
      C ≤ C+1 := by linarith
      _ = Real.exp (Real.log (C+1)) := (Real.exp_log hC1).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogC
  calc
    C*(latitudeNormalization (N-1)).toReal ≤
        Real.exp ((N:ℝ)*(η/2))*(latitudeNormalization (N-1)).toReal :=
      mul_le_mul_of_nonneg_right hCBound hpositive.le
    _ ≤ Real.exp ((N:ℝ)*(η/2))*Real.exp ((N:ℝ)*(η/2)) :=
      mul_le_mul_of_nonneg_left hnormBound (Real.exp_pos _).le
    _ = Real.exp ((N:ℝ)*η) := by
      rw [←Real.exp_add]
      congr 1
      ring

end
end SlowEquilibration.SphericalPureCapNormalizerAbsorption
