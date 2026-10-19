-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureThresholds

/-! Genuine finite nonnegative coefficient truncations of the source infinite
mixture, with their literal covariance polynomials. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite truncation, before the harmless nonzero witness is selected. -/
def cutoffCoefficients (μ : InfiniteMixture) (P : ℕ) : ℕ →₀ ℝ :=
  Finsupp.onFinset (Finset.range (P+1)) (fun p => if p≤P then μ.coeff p else 0)
    (fun p hp => by by_contra hh; simp only [Finset.mem_range,not_lt] at hh; simp [show ¬p≤P by omega] at hp)

theorem cutoffCoefficients_apply (μ : InfiniteMixture) (P p : ℕ) :
    cutoffCoefficients μ P p=if p≤P then μ.coeff p else 0 := rfl

/-- The cutoff is an actual `FiniteMixture`, once it contains one positive term. -/
def finiteCutoff (μ : InfiniteMixture) (P : ℕ) (hP : ∃ p,p≤P ∧ 0<μ.coeff p) : FiniteMixture where
  coeff := cutoffCoefficients μ P
  nonneg p := by rw [cutoffCoefficients_apply];split_ifs;exact μ.nonneg p;exact le_rfl
  zero_below_two p hp := by rw [cutoffCoefficients_apply,μ.zero_below_two p hp];simp
  nonzero := by
    obtain ⟨p,hp,hc⟩ := hP
    intro he
    have hh := congrArg (fun c : ℕ →₀ ℝ => c p) he
    simp only [cutoffCoefficients_apply,if_pos hp,Finsupp.zero_apply] at hh
    exact hc.ne' hh

theorem finiteCutoff_coeff (μ : InfiniteMixture) (P : ℕ) (hP : ∃ p,p≤P ∧ 0<μ.coeff p) (p : ℕ) :
    (finiteCutoff μ P hP).coeff p=if p≤P then μ.coeff p else 0 := rfl

theorem finiteCutoff_exists_eventually (μ : InfiniteMixture) :
    ∀ᶠ P in atTop,∃ p,p≤P ∧ 0<μ.coeff p := by
  obtain ⟨p,_,hp⟩ := μ.exists_positive_coefficient
  exact Filter.eventually_atTop.2 ⟨p,fun P hP => ⟨p,hP,hp⟩⟩

theorem finiteCutoff_xi (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) (r : ℝ) :
    (finiteCutoff μ P hP).xi r=∑ p∈Finset.range (P+1),μ.coeff p*r^p := by
  have hs : (finiteCutoff μ P hP).coeff.support⊆Finset.range (P+1) := by
    intro p hp
    have hh := Finsupp.mem_support_iff.mp hp
    rw [finiteCutoff_coeff] at hh
    by_contra h
    simp only [Finset.mem_range,not_lt] at h
    simp [show ¬p≤P by omega] at hh
  change (finiteCutoff μ P hP).coeff.sum (fun p c => c*r^p)=_
  rw [Finsupp.sum_of_support_subset _ hs (fun p c => c*r^p) (by intro p _;simp)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [finiteCutoff_coeff,if_pos (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hp)]

theorem finiteCutoff_xi_le (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) {r : ℝ} (hr : r∈Icc 0 1) :
    (finiteCutoff μ P hP).xi r≤μ.xi r := by
  rw [finiteCutoff_xi]
  exact (μ.summable_xi (abs_le.mpr ⟨by linarith [hr.1],hr.2⟩)).sum_le_tsum
    (Finset.range (P+1)) (fun p _ => mul_nonneg (μ.nonneg p) (pow_nonneg hr.1 p))

end SlowEquilibration.InfiniteMixture
