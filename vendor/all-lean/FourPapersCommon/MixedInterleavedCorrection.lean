module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedSecondCorrection
public import Targets.Section5InterleavedCovariance

@[expose] public section

/-! Exact physical theta correction of the genuine tagged interleaving.
The sorting/regrouping proof adapts the Apache-2.0 finite-tag correction proof. -/
noncomputable section
open Real
open SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

@[simp] theorem correction_neg (ξ : AdmissibleEvenMixture) (x : ℝ) :
    ξ.correction (-x) = ξ.correction x := by
  simp only [AdmissibleEvenMixture.correction, ξ.value_even, ξ.first_odd]
  ring

theorem correction_trialSign_mul (ξ : AdmissibleEvenMixture) (v x : ℝ) :
    ξ.correction (section5TrialSign v * x) = ξ.correction x := by
  unfold section5TrialSign
  split_ifs <;> simp

def mixedTaggedTrialIncrement (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (u : ℝ) (j : ℕ) : Section5MassTag k → ℝ :=
  Sum.elim (fun _ => 0) (fun p => ξ.correction (section5Rho s j u (p + 1)) -
    ξ.correction (section5Rho s j u p))

theorem mixedInterleavedRho_trial_increment (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) {j : ℕ} (hj : j ≤ k + 1) (u : ℝ)
    (i : Fin ((k + 2) + (k + 3))) :
    ξ.correction (section5InterleavedRho s r j u (i + 1)) -
      ξ.correction (section5InterleavedRho s r j u i) =
      mixedTaggedTrialIncrement ξ s u j (section5Interleaving s r j i) := by
  have he : i = (section5Interleaving s r j).symm (section5Interleaving s r j i) :=
    (Equiv.symm_apply_apply _ _).symm
  cases h : section5Interleaving s r j i with
  | inl p =>
    rw [h] at he
    rw [he, section5InterleavedRho_physical_succ]
    simp [mixedTaggedTrialIncrement]
  | inr p =>
    rw [h] at he
    rw [he, section5InterleavedRho_interpolating_succ s r hj,
      section5InterleavedRho_at_interpolating s r hj]
    simp [mixedTaggedTrialIncrement]

theorem mixedInterleaving_correction (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (u : ℝ) (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) :
    (∑ i, (if i < section5InterleavingCutoff s r hj then (2 : ℝ) else 1) *
      section5InterleavedMass s r j i *
        mixedTaggedTrialIncrement ξ s u j (section5Interleaving s r j i)) =
      2 * mixedSchemeCorrection ξ s := by
  have hcut (p : Fin (k + 3)) :
      (section5Interleaving s r j).symm (Sum.inr p) < section5InterleavingCutoff s r hj ↔
        (p : ℕ) < j :=
    (strictMono_section5Interleaving_interpolating s r hj).lt_iff_lt
  have H := section5Interleaving_sum s r j (fun tag =>
    (if (section5Interleaving s r j).symm tag < section5InterleavingCutoff s r hj
      then (2 : ℝ) else 1) * section5TaggedMass s r j tag *
      mixedTaggedTrialIncrement ξ s u j tag)
  simp only [Equiv.symm_apply_apply] at H
  simp only [mixedTaggedTrialIncrement, Sum.elim_inl, Sum.elim_inr,
    mul_zero, Finset.sum_const_zero, zero_add] at H
  simp_rw [hcut] at H
  refine H.trans ?_
  have hc := mixedLeftPairCorrection_eq ξ s u (s.m (j - 1)) hj0 hj
  rw [mixedPairCascadeCorrection_eq_split] at hc
  simp only [sub_self, zero_mul, add_zero] at hc
  convert hc using 1
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

theorem mixedInterleavedCross_correction (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (r : ℕ) {j : ℕ} (hj0 : 1 ≤ j) (hj : j ≤ k + 1) (v : ℝ) :
    mixedPairCascadeCorrection ξ (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |v|) (section5InterleavedCross s r hj v) (2 * k + 4) =
      2 * mixedSchemeCorrection ξ s := by
  have he : mixedPairCascadeCorrection ξ (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |v|) (section5InterleavedCross s r hj v) (2 * k + 4) =
      mixedPairCascadeCorrection ξ (section5InterleavedMassNat s r j)
      (section5InterleavedRho s r j |v|)
      (fun l => section5InterleavedRho s r j |v| (min l (section5InterleavingCutoff s r hj))) (2 * k + 4) := by
    unfold mixedPairCascadeCorrection mixedPairTrialEnergy
    apply Finset.sum_congr rfl
    intro p _
    simp only [section5InterleavedCross, correction_trialSign_mul]
  rw [he, mixedPairCascadeCorrection_eq_split]
  have hN : 2 * k + 4 + 1 = (k + 2) + (k + 3) := by omega
  rw [hN, ← Fin.sum_univ_eq_sum_range]
  simp only [section5InterleavedMassNat_coe]
  simp_rw [mixedInterleavedRho_trial_increment ξ s r hj]
  exact mixedInterleaving_correction ξ s |v| r hj0 hj

end FourPapersCommon
