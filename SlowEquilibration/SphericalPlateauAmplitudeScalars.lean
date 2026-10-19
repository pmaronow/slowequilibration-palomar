-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! # Exact transverse degree-one and degree-two scalar amplitudes

These are the source binomial latitude coefficients and their Dirac trial
amplitude shifts. All continuity, bounds, and strict positivity come from
the actual nonnegative coefficients and physical latitude interval.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeScalars
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal squared coefficient a_{p,k}(r)^2. -/
def amplitudeSq (c : ℝ) (p k : ℕ) (r : ℝ) : ℝ :=
  c*(Nat.choose p k : ℝ)*r^(2*(p-k))*(1-r^2)^k

/-- The literal source coefficient, with its positive square roots. -/
def amplitude (c : ℝ) (p k : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (c*(Nat.choose p k : ℝ))*r^(p-k)*(Real.sqrt (1-r^2))^k

theorem amplitude_continuous (c : ℝ) (p k : ℕ) : Continuous (amplitude c p k) := by
  unfold amplitude
  fun_prop

theorem amplitudeSq_continuous (c : ℝ) (p k : ℕ) : Continuous (amplitudeSq c p k) := by
  unfold amplitudeSq
  fun_prop

theorem amplitude_sq_eq {c r : ℝ} (hc : 0 ≤ c) (hr : |r| ≤ 1) (p k : ℕ) :
    (amplitude c p k r)^2=amplitudeSq c p k r := by
  have hnon : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hpowr : (r^(p-k))^2=r^(2*(p-k)) := by
    rw [← pow_mul,Nat.mul_comm (p-k) 2]
  have hpows : ((Real.sqrt (1-r^2))^k)^2=(1-r^2)^k := by
    rw [← pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt hnon]
  unfold amplitude amplitudeSq
  rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hc (Nat.cast_nonneg _)),hpowr,hpows]

theorem amplitudeSq_nonneg {c r : ℝ} (hc : 0 ≤ c) (hr : |r| ≤ 1) (p k : ℕ) :
    0 ≤ amplitudeSq c p k r := by
  have hnon : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hpow : 0 ≤ r^(2*(p-k)) := by
    rw [Nat.mul_comm 2 (p-k),pow_mul]
    exact sq_nonneg _
  unfold amplitudeSq
  exact mul_nonneg (mul_nonneg (mul_nonneg hc (Nat.cast_nonneg _))
    hpow) (pow_nonneg hnon k)

theorem amplitudeSq_le_coefficient {c r : ℝ} (hc : 0 ≤ c) (hr : |r| ≤ 1) (p k : ℕ) :
    amplitudeSq c p k r ≤ c*(Nat.choose p k : ℝ) := by
  have hnon : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hpow : 0 ≤ r^(2*(p-k)) := by
    rw [Nat.mul_comm 2 (p-k),pow_mul]
    exact sq_nonneg _
  have hrpow : r^(2*(p-k)) ≤ 1 := by
    have h := pow_le_one₀ (abs_nonneg r) hr (n := 2*(p-k))
    rw [← abs_pow,abs_of_nonneg hpow] at h
    exact h
  have hspow := pow_le_one₀ hnon (show 1-r^2 ≤ 1 by nlinarith [sq_nonneg r]) (n := k)
  have hcoef : 0 ≤ c*(Nat.choose p k : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
  unfold amplitudeSq
  calc
    _ ≤ (c*(Nat.choose p k : ℝ)*1)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrpow hcoef) hspow
        (pow_nonneg hnon k) (by simpa only [mul_one] using hcoef)
    _ = _ := by ring

theorem amplitudeSq_pos {c r : ℝ} (hc : 0 < c) (hr : r ∈ Ioo (0 : ℝ) 1)
    {p k : ℕ} (hk : k ≤ p) : 0 < amplitudeSq c p k r := by
  have hchoose : 0 < (Nat.choose p k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hnon : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  unfold amplitudeSq
  exact mul_pos (mul_pos (mul_pos hc hchoose) (pow_pos hr.1 _)) (pow_pos hnon _)

/-- The Dirac trial point at a possibly negative latitude uses its absolute
value; it stays strictly below one and varies continuously. -/
def trialAtom (r : ℝ) : ℝ := |r|/(1+|r|)

theorem trialAtom_continuous : Continuous trialAtom := by
  unfold trialAtom
  apply continuous_abs.div (continuous_const.add continuous_abs)
  intro r
  change 1+|r| ≠ 0
  have h := abs_nonneg r
  linarith

theorem trialAtom_mem_Ico (r : ℝ) : trialAtom r ∈ Ico (0 : ℝ) 1 := by
  have hd : 0 < 1+|r| := by linarith [abs_nonneg r]
  constructor
  · exact div_nonneg (abs_nonneg r) hd.le
  · exact (div_lt_one hd).mpr (by linarith)

/-- The literal coefficient of τ(2+τ) in a source Dirac upper trial. -/
def trialShiftCoefficient (β c : ℝ) (p k : ℕ) (r : ℝ) : ℝ :=
  (β^2/2)*amplitudeSq c p k r*(1-(trialAtom r)^k)

theorem trialShiftCoefficient_continuous (β c : ℝ) (p k : ℕ) :
    Continuous (trialShiftCoefficient β c p k) := by
  unfold trialShiftCoefficient
  exact (continuous_const.mul (amplitudeSq_continuous c p k)).mul
    (continuous_const.sub (trialAtom_continuous.pow k))

theorem trialShiftCoefficient_nonneg {β c r : ℝ} (hc : 0 ≤ c) (hr : |r| ≤ 1)
    (p k : ℕ) : 0 ≤ trialShiftCoefficient β c p k r := by
  have ht := trialAtom_mem_Ico r
  have hp := pow_le_one₀ ht.1 ht.2.le (n := k)
  unfold trialShiftCoefficient
  exact mul_nonneg (mul_nonneg (by positivity) (amplitudeSq_nonneg hc hr p k)) (by linarith)

theorem trialShiftCoefficient_le_coefficient {β c r : ℝ} (hc : 0 ≤ c) (hr : |r| ≤ 1)
    (p k : ℕ) : trialShiftCoefficient β c p k r ≤ (β^2/2)*c*(Nat.choose p k : ℝ) := by
  have ht := trialAtom_mem_Ico r
  have hpower : 0 ≤ (trialAtom r)^k := pow_nonneg ht.1 k
  have hmargin : 0 ≤ 1-(trialAtom r)^k := by
    have hp := pow_le_one₀ ht.1 ht.2.le (n := k)
    linarith
  have hfirst : 0 ≤ (β^2/2)*amplitudeSq c p k r :=
    mul_nonneg (by positivity) (amplitudeSq_nonneg hc hr p k)
  unfold trialShiftCoefficient
  calc
    _ ≤ (β^2/2)*amplitudeSq c p k r*1 :=
      mul_le_mul_of_nonneg_left (show 1-(trialAtom r)^k ≤ 1 by linarith) hfirst
    _ ≤ (β^2/2)*(c*(Nat.choose p k : ℝ)) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (amplitudeSq_le_coefficient hc hr p k) (by positivity)
    _ = _ := by ring

theorem twice_trialShiftCoefficient_of_nonneg (β c : ℝ) (p k : ℕ) {r : ℝ}
    (hr : 0 ≤ r) : 2*trialShiftCoefficient β c p k r=
      β^2*amplitudeSq c p k r*(1-(r/(1+r))^k) := by
  unfold trialShiftCoefficient trialAtom
  rw [abs_of_nonneg hr]
  ring

theorem trialShiftCoefficient_pos {β c r : ℝ} (hβ : β ≠ 0) (hc : 0 < c)
    (hr : r ∈ Ioo (0 : ℝ) 1) {p k : ℕ} (hk₀ : 0 < k) (hkp : k ≤ p) :
    0 < trialShiftCoefficient β c p k r := by
  have ht := trialAtom_mem_Ico r
  have hp : (trialAtom r)^k < 1 := pow_lt_one₀ ht.1 ht.2 (by omega)
  unfold trialShiftCoefficient
  exact mul_pos (mul_pos (by positivity) (amplitudeSq_pos hc hr hkp)) (by linarith)

/-- Both actual transverse probes remain strictly positive even when the
original mixture has no physical degree-two term. -/
theorem degree_one_two_trialShiftCoefficient_pos {β c r : ℝ} (hβ : β ≠ 0)
    (hc : 0 < c) (hr : r ∈ Ioo (0 : ℝ) 1) {p : ℕ} (hp : 2 ≤ p) :
    0 < trialShiftCoefficient β c p 1 r ∧ 0 < trialShiftCoefficient β c p 2 r :=
  ⟨trialShiftCoefficient_pos hβ hc hr (by omega) (by omega),
    trialShiftCoefficient_pos hβ hc hr (by omega) hp⟩

end
end SlowEquilibration.SphericalPlateauAmplitudeScalars
