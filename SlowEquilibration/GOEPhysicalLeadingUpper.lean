-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalWholeLinePotential
public import SlowEquilibration.SemicircleDimensionScaling

/-! Actual physical GOE determinant upper bounds with the exact manuscript
leading exponent and a fixed finite-codimension prefactor, all real shifts. -/

@[expose] public section
namespace SlowEquilibration.GOEPhysicalLeadingUpper

noncomputable section
open Set Filter
open scoped Topology
open GOEScaling GOEPhysicalPotential GOEPhysicalPrefactors GOEPhysicalWholeLinePotential SemicirclePotential
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma physicalRate_leading_le (n j : ℕ) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    physicalRate n j b k ≤ (n+1+j : ℕ)*(Real.log b/2+potential (k/Real.sqrt b))+
      (j:ℝ)*(1+|Real.log b|)/2 := by
  let N : ℕ := n+1+j
  let τ : ℝ := (n+1 : ℝ)/(N:ℝ)
  have hN : 0 < (N:ℝ) := by dsimp only [N];positivity
  have hτ : 0 < τ := div_pos (by positivity) hN
  have hτ1 : τ ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    dsimp only [N]
    norm_cast
    omega
  have ht := physical_rate_dimension_scaling_le hb hτ hτ1 k
  have ha : scaleFactor n N b=Real.sqrt (b*τ) := by
    unfold scaleFactor
    dsimp only [τ]
    congr 1
    ring
  have hp : 0 < b*τ := mul_pos hb hτ
  have hrate : physicalRate n j b k=
      (n+1 : ℝ)*(Real.log (b*τ)/2+potential (k/Real.sqrt (b*τ))) := by
    unfold physicalRate
    rw [ha,Real.log_sqrt hp.le]
  rw [hrate]
  have hh := mul_le_mul_of_nonneg_left ht hN.le
  have hleft : (N:ℝ)*τ=(n+1 : ℝ) := by dsimp only [τ];field_simp
  have hright : (N:ℝ)*(1-τ)=j := by
    dsimp only [τ,N]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  rw [← mul_assoc,hleft] at hh
  have he : (N:ℝ)*((1-τ)*(1+|Real.log b|)/2)=(j:ℝ)*(1+|Real.log b|)/2 := by
    rw [mul_div_assoc,← mul_assoc,hright]
    ring
  conv_rhs at hh => rw [mul_add]
  rw [he] at hh
  exact hh

/-- The true ordinary mean has a whole-line compact-uniform leading rate,
with the exact fixed codimension correction retained as a finite prefactor. -/
theorem physical_mean_leading_upper_uniform (j : ℕ) {b Z eps : ℝ}
    (hb : 0 < b) (hZ : 0 ≤ Z) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,∀ k : ℝ,|k| ≤ Z →
      physicalMean n (n+1+j) b k ≤ Real.exp
        ((n+1+j : ℕ)*(Real.log b/2+potential (k/Real.sqrt b)+eps)+
          (j:ℝ)*(1+|Real.log b|)/2) := by
  filter_upwards [physical_mean_upper_uniform j hb hZ heps] with n hn
  intro k hk
  apply (hn k hk).trans
  apply Real.exp_le_exp.mpr
  have hrate := physicalRate_leading_le n j hb k
  have hm : (n+1 : ℝ) ≤ (n+1+j : ℕ) := by norm_cast;omega
  have he := mul_le_mul_of_nonneg_right hm heps.le
  nlinarith

end
end SlowEquilibration.GOEPhysicalLeadingUpper
