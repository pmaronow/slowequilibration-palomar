-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianHermiteSmoothIBP

/-! Repeated Gaussian integration by parts, with the normalization factor
proved from the coordinate raising rule. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianHermiteDerivative

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open GaussianMaximalCorrelation
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential envelopes used for smooth integration by parts also
give genuine square integrability under the product Gaussian law. -/
theorem ExponentialFirstJet.memLp_two {f : (ι → ℝ) → ℝ}
    (hf : ExponentialFirstJet f) : MemLp f 2 (γpi ι) := by
  obtain ⟨C, c, hC, hc, hb, _⟩ := hf.bound
  apply (memLp_two_iff_integrable_sq hf.smooth.continuous.aestronglyMeasurable).mpr
  apply Integrable.mono'
    ((SYK.integrable_exp_c_sum_abs_pi (2 * c)).const_mul (C ^ 2))
  · exact (hf.smooth.continuous.pow 2).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hs := mul_self_le_mul_self (abs_nonneg (f x)) (hb x)
    have he : (C * Real.exp (c * ∑ j, |x j|)) ^ 2 =
        C ^ 2 * Real.exp ((2 * c) * ∑ j, |x j|) := by
      calc
        _ = C ^ 2 * (Real.exp (c * ∑ j, |x j|) * Real.exp (c * ∑ j, |x j|)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    simpa only [← pow_two, sq_abs, he] using hs

/-- Ordered coordinate derivatives; the last direction is differentiated
last. This matches the repeated directional derivative convention. -/
def mixedCoordinatePartial (f : (ι → ℝ) → ℝ) :
    (n : ℕ) → (Fin n → ι) → (ι → ℝ) → ℝ
  | 0, _ => f
  | n + 1, d => coordinatePartial
      (mixedCoordinatePartial f n (fun k => d k.castSucc)) (d (Fin.last n))

def raisedIndex : (n : ℕ) → (Fin n → ι) → (ι → ℕ) → (ι → ℕ)
  | 0, _, a => a
  | n + 1, d, a => raisedIndex n (fun k => d k.castSucc) (bump (d (Fin.last n)) a)

def raisingWeight : (n : ℕ) → (Fin n → ι) → (ι → ℕ) → ℝ
  | 0, _, _ => 1
  | n + 1, d, a => Real.sqrt (a (d (Fin.last n)) + 1 : ℝ) *
      raisingWeight n (fun k => d k.castSucc) (bump (d (Fin.last n)) a)

/-- Full repeated coefficient identity. The only analytic assumptions are
square integrability and exponential first-jet bounds for the actual
successive derivatives. -/
theorem coeff_mixedCoordinatePartial (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d))
    (hL2 : ∀ n d, MemLp (mixedCoordinatePartial f n d) 2 (γpi ι))
    (n : ℕ) (d : Fin n → ι) (a : ι → ℕ) :
    coeff (mixedCoordinatePartial f n d) a =
      raisingWeight n d a * coeff f (raisedIndex n d a) := by
  induction n generalizing a with
  | zero => simp [mixedCoordinatePartial, raisingWeight, raisedIndex]
  | succ n ih =>
    rw [mixedCoordinatePartial, coeff_coordinatePartial _ (hjet n _) (hL2 n _)
      (d (Fin.last n)) (hL2 (n + 1) d), ih]
    simp only [raisingWeight, raisedIndex]
    ring

def factorialProduct (a : ι → ℕ) : ℝ := ∏ i, ((a i).factorial : ℝ)

lemma factorialProduct_bump (a : ι → ℕ) (i : ι) :
    factorialProduct (bump i a) = (a i + 1 : ℝ) * factorialProduct a := by
  have hprod : factorialProduct a =
      ((a i).factorial : ℝ) * ∏ j ∈ Finset.univ.erase i, ((a j).factorial : ℝ) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [factorialProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [bump, Function.update_self, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [hprod]
  have hrest : (∏ j ∈ Finset.univ.erase i, ((Function.update a i (a i + 1) j).factorial : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((a j).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest]
  ring

lemma raisingWeight_square_factorial (n : ℕ) (d : Fin n → ι) (a : ι → ℕ) :
    (raisingWeight n d a) ^ 2 * factorialProduct a =
      factorialProduct (raisedIndex n d a) := by
  induction n generalizing a with
  | zero => simp [raisingWeight, raisedIndex]
  | succ n ih =>
    simp only [raisingWeight, raisedIndex, mul_pow]
    rw [Real.sq_sqrt (show 0 ≤ (a (d (Fin.last n)) : ℝ) + 1 by positivity)]
    rw [show (a (d (Fin.last n)) + 1 : ℝ) *
        raisingWeight n (fun k => d k.castSucc) (bump (d (Fin.last n)) a) ^ 2 *
          factorialProduct a =
      raisingWeight n (fun k => d k.castSucc) (bump (d (Fin.last n)) a) ^ 2 *
        ((a (d (Fin.last n)) + 1 : ℝ) * factorialProduct a) by ring,
      ← factorialProduct_bump, ih]

lemma degree_raisedIndex (n : ℕ) (d : Fin n → ι) (a : ι → ℕ) :
    degree (raisedIndex n d a) = degree a + n := by
  induction n generalizing a with
  | zero => simp [raisedIndex]
  | succ n ih => simp only [raisedIndex, ih, degree_bump]; omega

lemma factorialProduct_one_le (a : ι → ℕ) : 1 ≤ factorialProduct a := by
  apply Finset.one_le_prod₀
  intro i _
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (a i))

lemma exists_raisedIndex_add (n : ℕ) (a : ι → ℕ) (ha : degree a = n)
    (base : ι → ℕ) :
    ∃ d : Fin n → ι, raisedIndex n d base = fun i => base i + a i := by
  induction n generalizing a base with
  | zero =>
    have ha0 : a = 0 := (degree_eq_zero_iff a).mp ha
    subst a
    exact ⟨Fin.elim0, by simp [raisedIndex]⟩
  | succ n ih =>
    have hex : ∃ i, 0 < a i := by
      by_contra hn
      push_neg at hn
      have ha0 : a = 0 := funext (fun i => by simpa using hn i)
      rw [ha0] at ha
      simp [degree] at ha
    obtain ⟨i, hi⟩ := hex
    let b : ι → ℕ := Function.update a i (a i - 1)
    have hbump : bump i b = a := by
      ext j
      by_cases hj : j = i
      · subst j
        simp only [bump, b, Function.update_self]
        omega
      · simp [bump, b, Function.update_of_ne hj]
    have hb : degree b = n := by
      have he := degree_bump i b
      rw [hbump, ha] at he
      omega
    obtain ⟨d, hd⟩ := ih b hb (bump i base)
    refine ⟨Fin.snoc d i, ?_⟩
    simp only [raisedIndex, Fin.snoc_last, Fin.snoc_castSucc]
    rw [hd]
    ext j
    by_cases hj : j = i
    · subst j
      simp only [bump, b, Function.update_self]
      omega
    · simp [bump, b, Function.update_of_ne hj]

lemma exists_raisedIndex_zero (n : ℕ) (a : ι → ℕ) (ha : degree a = n) :
    ∃ d : Fin n → ι, raisedIndex n d 0 = a := by
  simpa only [Pi.zero_apply, zero_add] using exists_raisedIndex_add n a ha 0

/-- At the zero Hermite index the coefficient is the mean. In particular,
an ordered expected derivative equals the corresponding chaos coefficient
times its exact product-factorial normalization. -/
theorem integral_mixedCoordinatePartial_square (f : (ι → ℝ) → ℝ)
    (hjet : ∀ n d, ExponentialFirstJet (mixedCoordinatePartial f n d))
    (hL2 : ∀ n d, MemLp (mixedCoordinatePartial f n d) 2 (γpi ι))
    (n : ℕ) (d : Fin n → ι) :
    (∫ x, mixedCoordinatePartial f n d x ∂γpi ι) ^ 2 =
      factorialProduct (raisedIndex n d 0) * (coeff f (raisedIndex n d 0)) ^ 2 := by
  have hc := coeff_mixedCoordinatePartial f hjet hL2 n d 0
  rw [coeff_zero] at hc
  rw [hc, mul_pow]
  have hw := raisingWeight_square_factorial n d (0 : ι → ℕ)
  simp only [factorialProduct, Pi.zero_apply, Nat.factorial_zero, Nat.cast_one,
    Finset.prod_const_one, mul_one] at hw
  rw [hw]
  rfl

end SlowEquilibration.GaussianHermiteDerivative
