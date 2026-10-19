-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEAsymptotics

/-! Actual clipped outside-edge GOE resolvent convergence, derived from
the proved ordinary resolvent limit and genuine spectral confinement. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def clippedResolvent (n : ℕ) (s ρ : ℝ) (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  (∑ i,(max ρ (2+s-eigenvalues n W i))⁻¹)/(n+1)

def clippedBad (n : ℕ) (s ρ ε : ℝ) :=
  {W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ | ε < |clippedResolvent n s ρ W-semicircleResolvent s|}

lemma clippedResolvent_measurable (n : ℕ) (s ρ : ℝ) : Measurable (clippedResolvent n s ρ) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _=>(measurable_const.max
    (measurable_const.sub ((measurable_pi_apply i).comp (eigenvalues_measurable n)))).inv)

lemma clippedBad_measurable (n : ℕ) (s ρ ε : ℝ) : MeasurableSet (clippedBad n s ρ ε) :=
  measurableSet_lt measurable_const ((clippedResolvent_measurable n s ρ).sub_const _).abs

lemma clippedResolvent_bounds (n : ℕ) (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    0 ≤ clippedResolvent n s ρ W ∧ clippedResolvent n s ρ W ≤ 1/ρ := by
  have hden : 0 < (n+1:ℝ) := by positivity
  have hterm (i : Fin (n+1)) : 0 ≤ (max ρ (2+s-eigenvalues n W i))⁻¹ :=
    inv_nonneg.mpr (hρ.le.trans (le_max_left _ _))
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _=>hterm i)) hden.le
  · apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ ∑ _i : Fin (n+1),1/ρ := Finset.sum_le_sum (fun i _=>by
        rw [one_div]
        exact inv_anti₀ hρ (le_max_left _ _))
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring

lemma clippedResolvent_eq_of_not_edgeBad (n : ℕ) {s ρ : ℝ} (_hs : 0 < s) (hρ : ρ ≤ s/2)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hW : W ∉ edgeBad n (s/2)) :
    clippedResolvent n s ρ W=GOEAsymptotics.empiricalResolvent n s W := by
  unfold clippedResolvent GOEAsymptotics.empiricalResolvent
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hLambda : |eigenvalues n W i| ≤ 2+s/2 := by
    apply le_of_not_gt
    intro h
    exact hW ⟨i,h⟩
  rw [max_eq_right (by have hh:=le_abs_self (eigenvalues n W i);linarith)]

lemma clippedBad_subset (n : ℕ) {s ρ ε : ℝ} (hs : 0 < s) (hρ : ρ ≤ s/2) :
    clippedBad n s ρ ε ⊆ resolventBad n s ε ∪ edgeBad n (s/2) := by
  intro W hW
  by_cases hE : W ∈ edgeBad n (s/2)
  · exact Or.inr hE
  · apply Or.inl
    change ε < |clippedResolvent n s ρ W-semicircleResolvent s| at hW
    change ε < |GOEAsymptotics.empiricalResolvent n s W-semicircleResolvent s|
    rwa [clippedResolvent_eq_of_not_edgeBad n hs hρ W hE] at hW

/-- Actual bounded clipped GOE resolvent converges in probability to its
true semicircle value, with no asymptotic or edge event supplied as a premise. -/
theorem clippedResolvent_converges_in_probability {s ρ ε : ℝ} (hs : 0 < s)
    (hρ : ρ ≤ s/2) (hε : 0 < ε) :
    Tendsto (fun n:ℕ=>(goeLaw (n+1) (n+1) 1).real (clippedBad n s ρ ε)) atTop (𝓝 0) := by
  have ht:=(empirical_resolvent_converges_in_probability hs hε).add
    (spectrum_converges_to_semicircle_support (by linarith : 0 < s/2))
  simp only [add_zero] at ht
  apply squeeze_zero (fun n=>measureReal_nonneg) (fun n=>?_ ) ht
  exact (measureReal_mono (clippedBad_subset n hs hρ)).trans (measureReal_union_le _ _)

end
end SlowEquilibration.GOEClippedResolvent
