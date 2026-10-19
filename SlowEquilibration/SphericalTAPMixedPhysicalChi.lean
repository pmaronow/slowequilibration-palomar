-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPlaneLaplaceUpper
public import SlowEquilibration.GOEPhysicalMeanRateBound
public import SlowEquilibration.SphericalCountRectangles

@[expose] public section

/-! The literal determinant prefactor `χ_N(k)` in the mixed source proof,
formed by dividing the genuine `N-1` dimensional GOE determinant mean by
its ambient-`N` semicircle exponential rate. -/

namespace SlowEquilibration.SphericalTAPMixedPhysicalChi
noncomputable section
open Set MeasureTheory GOEPhysicalPotential GOEPhysicalNormalizedMoments
open SphericalMarkedWindows
set_option autoImplicit false

def sourceMixedChi (n : ℕ) (μ : FiniteMixture) (Q k : ℝ) : ℝ :=
  let b := Q^2*μ.xi2 Q
  physicalMean n (n+2) b k /
    Real.exp ((n+2 : ℕ)*(Real.log (Real.sqrt b)+
      SemicirclePotential.potential (k/Real.sqrt b)))

theorem sourceMixedChi_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (sourceMixedChi n μ Q) := by
  unfold sourceMixedChi
  apply (physicalMean_measurable n (n+2) (Q^2*μ.xi2 Q)).div
  have hp : Continuous SemicirclePotential.potential :=
    SemicircleWholeLine.potential_continuous
  fun_prop

theorem sourceMixedChi_bounds (μ : FiniteMixture) {Q L R : ℝ}
    (hQ : 0 < Q) (hL : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, ∀ k ∈ Icc L R,
      c ≤ sourceMixedChi n μ Q k ∧ sourceMixedChi n μ Q k ≤ C := by
  let b := Q^2*μ.xi2 Q
  let g := L-2*Real.sqrt b
  have hb : 0 < b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hg : 0 < g := by dsimp [g,b] at *; linarith
  obtain ⟨B,hB,hbound⟩ := physicalMean_log_error_bound hb hg (Z := R)
  refine ⟨Real.exp (-B),Real.exp B,Real.exp_pos _,Real.exp_pos _,?_⟩
  intro n k hk
  have hstart : 2*Real.sqrt b+g=L := by dsimp [g]; ring
  have hk' : k ∈ Icc (2*Real.sqrt b+g) R := by
    rw [hstart]
    exact hk
  have hlog := hbound n k hk'
  let T := (n+2 : ℕ)*(Real.log (Real.sqrt b)+
    SemicirclePotential.potential (k/Real.sqrt b))
  have hm : 0 < physicalMean n (n+2) b k :=
    physicalMean_pos n 1 hb (by dsimp [b] at *; linarith [hk.1])
  have hlow : -B+T ≤ Real.log (physicalMean n (n+2) b k) := by
    dsimp [T] at *
    linarith [(abs_le.mp hlog).1]
  have hupp : Real.log (physicalMean n (n+2) b k) ≤ B+T := by
    dsimp [T] at *
    linarith [(abs_le.mp hlog).2]
  have hLowExp : Real.exp (-B)*Real.exp T ≤ physicalMean n (n+2) b k := by
    rw [← Real.exp_add, ← Real.exp_log hm]
    exact Real.exp_le_exp.mpr hlow
  have hUppExp : physicalMean n (n+2) b k ≤ Real.exp B*Real.exp T := by
    rw [← Real.exp_add, ← Real.exp_log hm]
    exact Real.exp_le_exp.mpr hupp
  change Real.exp (-B) ≤ physicalMean n (n+2) b k / Real.exp T ∧
    physicalMean n (n+2) b k / Real.exp T ≤ Real.exp B
  exact ⟨(le_div_iff₀ (Real.exp_pos T)).mpr hLowExp,
    (div_le_iff₀ (Real.exp_pos T)).mpr hUppExp⟩

end
end SlowEquilibration.SphericalTAPMixedPhysicalChi
