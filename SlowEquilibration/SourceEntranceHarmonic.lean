-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic

/-! Explicit scalar harmonic coefficients for manuscript `lem:ent-harmonic`.
The Gegenbauer polynomials and weights below use the literal finite sums and
Gamma formula in Section 8. The Gamma quotient is reduced to a finite product;
positivity, the first-order relative asymptotic, and the weight bound are proved
for every source dimension and sector. The uniform estimates for the zonal
polynomial and all its first finitely many derivatives are also proved. The
arbitrary-degree reconstruction identity and Gaussian harmonic projections
are not constructed in this module.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceHarmonic

open Filter Asymptotics
open scoped BigOperators Topology
set_option autoImplicit false

/-- The source parameter `(N - 2) / 2`. -/
def alpha (N : ℕ) : ℝ := ((N : ℝ) - 2) / 2

/-- The rising factorial, including its empty product. -/
def rising (a : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (a + i)

/-- The literal finite Gegenbauer sum preceding `(eq:ent-zonal)`. -/
def gegenbauer (N ell : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (ell / 2 + 1),
    (-1 : ℝ) ^ j * rising (alpha N) (ell - j) /
      ((j.factorial : ℝ) * ((ell - 2*j).factorial : ℝ)) *
        (2*r) ^ (ell - 2*j)

/-- The normalized zonal polynomial `(eq:ent-zonal)`. -/
def zonal (N ell : ℕ) (r : ℝ) : ℝ :=
  (ell.factorial : ℝ) / rising (2*alpha N) ell * gegenbauer N ell r

/-- The literal Gamma formula for `(eq:ent-harmonic)`. -/
def gammaWeight (N p j : ℕ) : ℝ :=
  (p.factorial : ℝ) * Real.Gamma (alpha N) * ((p - 2*j : ℕ) + alpha N) /
    (2^p * (j.factorial : ℝ) * Real.Gamma ((p-j : ℕ) + alpha N + 1)) *
      (rising (2*alpha N) (p-2*j) / ((p-2*j).factorial : ℝ))

/-- The same coefficient expressed without special functions. -/
def weight (N p j : ℕ) : ℝ :=
  (p.factorial : ℝ) * ((p-2*j : ℕ) + alpha N) *
    rising (2*alpha N) (p-2*j) /
    (2^p * (j.factorial : ℝ) * rising (alpha N) (p-j+1) *
      ((p-2*j).factorial : ℝ))

/-- The source dimensions have positive Gegenbauer parameter. -/
theorem alpha_pos {N : ℕ} (hN : 3 ≤ N) : 0 < alpha N := by
  unfold alpha
  have : (3 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- Every finite rising product is strictly positive at a positive argument. -/
theorem rising_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < rising a k := by
  exact Finset.prod_pos (fun i _ => add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg i))

/-- Iterating the Gamma functional equation requires no asymptotic theorem. -/
theorem gamma_add_nat {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a + k) = Real.Gamma a * rising a k := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih]
    simp only [rising, Finset.prod_range_succ]
    ring

/-- Exact finite-product version of the printed Gamma coefficient. -/
theorem gammaWeight_eq_weight {N : ℕ} (hN : 3 ≤ N) (p j : ℕ) :
    gammaWeight N p j = weight N p j := by
  have hG := (Real.Gamma_pos_of_pos (alpha_pos hN)).ne'
  have hR := (rising_pos (alpha_pos hN) (p-j+1)).ne'
  have he : (p-j : ℕ) + alpha N + 1 = alpha N + (p-j+1 : ℕ) := by
    push_cast
    ring
  unfold gammaWeight weight
  rw [he, gamma_add_nat (alpha_pos hN)]
  field_simp

/-- Every manuscript harmonic coefficient is positive, including degree zero. -/
theorem weight_pos {N : ℕ} (hN : 3 ≤ N) (p j : ℕ) :
    0 < weight N p j := by
  unfold weight
  have hα := alpha_pos hN
  have hR := rising_pos hα (p-j+1)
  have hS := rising_pos (by linarith : 0 < 2*alpha N) (p-2*j)
  positivity

/-- Positivity directly for the literal Gamma expression. -/
theorem gammaWeight_pos {N : ℕ} (hN : 3 ≤ N) (p j : ℕ) :
    0 < gammaWeight N p j := by
  rw [gammaWeight_eq_weight hN]
  exact weight_pos hN p j

/-- The constant zonal harmonic is exactly one. -/
theorem zonal_zero (N : ℕ) (r : ℝ) : zonal N 0 r = 1 := by
  simp [zonal, gegenbauer, rising]

/-- The degree-one zonal harmonic has no dimension correction. -/
theorem zonal_one {N : ℕ} (hN : 3 ≤ N) (r : ℝ) : zonal N 1 r = r := by
  have hα := (alpha_pos hN).ne'
  simp [zonal, gegenbauer, rising]
  field_simp

/-- Literal quadratic zonal polynomial. -/
theorem zonal_two {N : ℕ} (hN : 3 ≤ N) (r : ℝ) :
    zonal N 2 r = ((N : ℝ)*r^2-1)/((N : ℝ)-1) := by
  have hN2 : (N : ℝ)-2 ≠ 0 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNm : (N : ℝ)-1 ≠ 0 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  norm_num [zonal, gegenbauer, rising, Finset.sum_range_succ, Finset.prod_range_succ, alpha]
  field_simp
  ring_nf
  have hNm' : -1+(N : ℝ) ≠ 0 := by simpa [sub_eq_add_neg, add_comm] using hNm
  field_simp [hNm']
  ring

/-- Literal quartic zonal polynomial. -/
theorem zonal_four {N : ℕ} (hN : 3 ≤ N) (r : ℝ) :
    zonal N 4 r =
      (((N : ℝ)+2)*((N : ℝ)+4)*r^4 - 6*((N : ℝ)+2)*r^2 + 3) /
        (((N : ℝ)-1)*((N : ℝ)+1)) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (N : ℝ)-2 ≠ 0 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNm : (N : ℝ)-1 ≠ 0 := by linarith
  have hNp : (N : ℝ)+1 ≠ 0 := by linarith
  norm_num [zonal, gegenbauer, rising, Finset.sum_range_succ, Finset.prod_range_succ, alpha]
  field_simp
  ring_nf
  have hSq : -1+(N : ℝ)^2 ≠ 0 := by nlinarith
  field_simp [hSq]
  ring

/-- The literal quartic expansion printed after `lem:ent-harmonic`. -/
theorem quartic_expansion {N : ℕ} (hN : 3 ≤ N) (r : ℝ) :
    r^4 =
      (((N : ℝ)-1)*((N : ℝ)+1)/(((N : ℝ)+2)*((N : ℝ)+4))) * zonal N 4 r +
      (6*((N : ℝ)-1)/((N : ℝ)*((N : ℝ)+4))) * zonal N 2 r +
      3/((N : ℝ)*((N : ℝ)+2)) := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (N : ℝ) ≠ 0 := by linarith
  have hm : (N : ℝ)-1 ≠ 0 := by linarith
  have h1 : (N : ℝ)+1 ≠ 0 := by linarith
  have h2 : (N : ℝ)+2 ≠ 0 := by linarith
  have h4 : (N : ℝ)+4 ≠ 0 := by linarith
  rw [zonal_four hN, zonal_two hN]
  field_simp
  ring

/-- Normalization of the literal quadratic and quartic zonal polynomials. -/
theorem zonal_two_four_at_one {N : ℕ} (hN : 3 ≤ N) :
    zonal N 2 1 = 1 ∧ zonal N 4 1 = 1 := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : (N : ℝ)-1 ≠ 0 := by linarith
  have h1 : (N : ℝ)+1 ≠ 0 := by linarith
  rw [zonal_two hN, zonal_four hN]
  constructor
  · field_simp
  · field_simp
    ring

/-- A rational function of inverse dimension, regular at zero, encoding the
scaled harmonic coefficient. -/
def weightProfile (p j : ℕ) (t : ℝ) : ℝ :=
  (p.factorial : ℝ) / (2^p * (j.factorial : ℝ) * ((p-2*j).factorial : ℝ)) *
    (1/2 + ((p-2*j : ℕ) - 1 : ℝ)*t) *
      (∏ i ∈ Finset.range (p-2*j), (1 + ((i : ℝ)-2)*t)) /
      (∏ i ∈ Finset.range (p-j+1), (1/2 + ((i : ℝ)-1)*t))

private theorem rising_alpha_scale {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    rising (alpha N) k = (N : ℝ)^k *
      ∏ i ∈ Finset.range k, (1/2 + ((i : ℝ)-1)*(N : ℝ)⁻¹) := by
  have h0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  calc
    rising (alpha N) k = ∏ i ∈ Finset.range k,
        (N : ℝ)*(1/2 + ((i : ℝ)-1)*(N : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro i _
      unfold alpha
      field_simp
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

private theorem rising_two_alpha_scale {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    rising (2*alpha N) k = (N : ℝ)^k *
      ∏ i ∈ Finset.range k, (1 + ((i : ℝ)-2)*(N : ℝ)⁻¹) := by
  have h0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  calc
    rising (2*alpha N) k = ∏ i ∈ Finset.range k,
        (N : ℝ)*(1 + ((i : ℝ)-2)*(N : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro i _
      unfold alpha
      field_simp
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- Exact rational-in-inverse-dimension representation, before taking limits. -/
theorem weight_mul_dimension_pow {N p j : ℕ} (hN : 3 ≤ N) (hj : 2*j ≤ p) :
    weight N p j * (N : ℝ)^j = weightProfile p j (N : ℝ)⁻¹ := by
  have h0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hk : p-j+1 = (p-2*j)+j+1 := by omega
  have hp : p = (p-2*j)+2*j := by omega
  have hA : (p-2*j : ℕ) + alpha N =
      (N : ℝ)*(1/2 + ((p-2*j : ℕ)-1 : ℝ)*(N : ℝ)⁻¹) := by
    unfold alpha
    field_simp
    ring
  unfold weight weightProfile
  rw [rising_alpha_scale hN, rising_two_alpha_scale hN, hA]
  rw [hk]
  simp only [pow_add, pow_one]
  field_simp

/-- The leading coefficient printed in `(eq:ent-harmonic-asymp)`. -/
def leadingWeight (p j : ℕ) : ℝ :=
  (p.factorial : ℝ) / (2^j * (j.factorial : ℝ) * ((p-2*j).factorial : ℝ))

/-- Evaluation of the scaled coefficient at infinite dimension. -/
theorem weightProfile_zero {p j : ℕ} (hj : 2*j ≤ p) :
    weightProfile p j 0 = leadingWeight p j := by
  have hp : p = (p-2*j)+2*j := by omega
  have hk : p-j+1 = (p-2*j)+j+1 := by omega
  simp only [weightProfile, leadingWeight, mul_zero, add_zero,
    Finset.prod_const, Finset.card_range, one_pow, mul_one]
  have hpow : (2 : ℝ)^p = 2^(p-2*j)*(2^j)^2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hk, hpow]
  simp only [pow_add, pow_one, div_pow, one_pow]
  field_simp

/-- The fixed rational profile is differentiable at inverse dimension zero. -/
theorem differentiableAt_weightProfile (p j : ℕ) :
    DifferentiableAt ℝ (weightProfile p j) 0 := by
  unfold weightProfile
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · simp

/-- Literal first-order relative asymptotic in `(eq:ent-harmonic-asymp)`:
after multiplication by `N^j`, the error is `O(1/N)`. -/
theorem weight_asymptotic {p j : ℕ} (hj : 2*j ≤ p) :
    (fun N : ℕ => weight N p j * (N : ℝ)^j - leadingWeight p j)
      =O[atTop] (fun N : ℕ => (N : ℝ)⁻¹) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (differentiableAt_weightProfile p j).isBigO_sub.comp_tendsto ht
  simp only [sub_zero, weightProfile_zero hj] at h
  apply h.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [weight_mul_dimension_pow hN hj]
  rfl

/-- The coefficient of `r^(ell-2*j)` in the literal normalized zonal sum. -/
def zonalCoefficient (N ell j : ℕ) : ℝ :=
  (ell.factorial : ℝ) / rising (2*alpha N) ell *
    ((-1 : ℝ)^j * rising (alpha N) (ell-j) /
      ((j.factorial : ℝ)*((ell-2*j).factorial : ℝ))) * 2^(ell-2*j)

/-- The zonal polynomial written with its individual scalar coefficients. -/
theorem zonal_eq_sum (N ell : ℕ) (r : ℝ) :
    zonal N ell r = ∑ j ∈ Finset.range (ell/2+1),
      zonalCoefficient N ell j * r^(ell-2*j) := by
  unfold zonal gegenbauer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold zonalCoefficient
  rw [mul_pow]
  ring

/-- Smooth rational profile for an individual zonal coefficient. -/
def zonalCoefficientProfile (ell j : ℕ) (t : ℝ) : ℝ :=
  (ell.factorial : ℝ)*(-1 : ℝ)^j*2^(ell-2*j) /
    ((j.factorial : ℝ)*((ell-2*j).factorial : ℝ)) *
      (∏ i ∈ Finset.range (ell-j), (1/2 + ((i : ℝ)-1)*t)) /
      (∏ i ∈ Finset.range ell, (1 + ((i : ℝ)-2)*t))

/-- Exact scaled coefficient identity. -/
theorem zonalCoefficient_mul_dimension_pow {N ell j : ℕ}
    (hN : 3 ≤ N) (hj : 2*j ≤ ell) :
    zonalCoefficient N ell j * (N : ℝ)^j =
      zonalCoefficientProfile ell j (N : ℝ)⁻¹ := by
  have h0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpow : (N : ℝ)^ell = (N : ℝ)^(ell-j)*(N : ℝ)^j := by
    rw [← pow_add]
    congr 1
    omega
  unfold zonalCoefficient zonalCoefficientProfile
  rw [rising_alpha_scale hN, rising_two_alpha_scale hN]
  rw [hpow]
  field_simp

/-- The top zonal coefficient converges to one. -/
theorem zonalCoefficientProfile_top_zero (ell : ℕ) :
    zonalCoefficientProfile ell 0 0 = 1 := by
  simp [zonalCoefficientProfile]
  field_simp

/-- Regularity of the rational zonal coefficient profile at zero. -/
theorem differentiableAt_zonalCoefficientProfile (ell j : ℕ) :
    DifferentiableAt ℝ (zonalCoefficientProfile ell j) 0 := by
  unfold zonalCoefficientProfile
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · simp

/-- Every coefficient of `Z_ell,N-r^ell` is `O(1/N)`.
This is the scalar ingredient for all uniform derivative estimates in
`lem:ent-harmonic`(3). -/
theorem zonalCoefficient_error_asymptotic {ell j : ℕ} (hj : 2*j ≤ ell) :
    (fun N : ℕ => zonalCoefficient N ell j - if j = 0 then 1 else 0)
      =O[atTop] (fun N : ℕ => (N : ℝ)⁻¹) := by
  let F : ℝ → ℝ := fun t => t^j * zonalCoefficientProfile ell j t
  have hd : DifferentiableAt ℝ F 0 := by
    apply DifferentiableAt.mul
    · fun_prop
    · exact differentiableAt_zonalCoefficientProfile ell j
  have hF : F 0 = if j = 0 then 1 else 0 := by
    by_cases hj0 : j = 0
    · simp [F, hj0, zonalCoefficientProfile_top_zero]
    · simp [F, hj0]
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hd.isBigO_sub.comp_tendsto ht
  simp only [sub_zero, hF] at h
  apply h.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop 3] with N hN
  have h0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc := zonalCoefficient_mul_dimension_pow hN hj
  dsimp [Function.comp_def, F]
  rw [← hc, inv_pow, mul_left_comm, inv_mul_cancel₀ (pow_ne_zero j h0), mul_one]

private theorem bound_all_dimensions_of_bigO {f : ℕ → ℝ}
    (hf : f =O[atTop] (fun N : ℕ => (N : ℝ)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → |f N| ≤ C/(N : ℝ) := by
  obtain ⟨C, hC, hb⟩ := isBigO_iff'.mp hf
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hb
  let S : ℝ := ∑ i ∈ Finset.range N0, |f i| *(i : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨C+S+1, by positivity, ?_⟩
  intro N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  apply (le_div_iff₀ hn).mpr
  by_cases hlarge : N0 ≤ N
  · have hbN : |f N| ≤ C/(N : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), div_eq_mul_inv]
        using hN0 N hlarge
    have := (le_div_iff₀ hn).mp hbN
    linarith
  · have hmem : N ∈ Finset.range N0 := Finset.mem_range.mpr (by omega)
    have hterm : |f N| *(N : ℝ) ≤ S := by
      change |f N| *(N : ℝ) ≤ ∑ i ∈ Finset.range N0, |f i| *(i : ℝ)
      exact Finset.single_le_sum (f := fun i : ℕ => |f i| * (i : ℝ))
        (fun i _ => by positivity) hmem
    linarith

/-- The `O(1/N)` coefficient estimate holds uniformly for every `N ≥ 3`,
after absorbing finitely many small dimensions into the constant. -/
theorem zonalCoefficient_error_bound {ell j : ℕ} (hj : 2*j ≤ ell) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      |zonalCoefficient N ell j - if j = 0 then 1 else 0| ≤ C/(N : ℝ) :=
  bound_all_dimensions_of_bigO (zonalCoefficient_error_asymptotic hj)

/-- The literal finite-sum zonal polynomials are smooth. -/
theorem contDiff_zonal (N ell : ℕ) : ContDiff ℝ ⊤ (zonal N ell) := by
  have he : zonal N ell = fun r => ∑ j ∈ Finset.range (ell/2+1),
      zonalCoefficient N ell j * r^(ell-2*j) := funext (zonal_eq_sum N ell)
  rw [he]
  fun_prop

private theorem zonal_sub_pow_eq_sum (N ell : ℕ) :
    (fun r : ℝ => zonal N ell r - r^ell) = fun r =>
      ∑ j ∈ Finset.range (ell/2+1),
        (zonalCoefficient N ell j - if j = 0 then 1 else 0)*r^(ell-2*j) := by
  funext r
  rw [zonal_eq_sum]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  simp

/-- Manuscript `lem:ent-harmonic`(3), with every derivative order and every
source dimension: the normalized zonal polynomial differs from the monomial
by at most `C_{ell,m}/N` in uniform derivative norm on `[-1,1]`. -/
theorem zonal_sub_pow_derivatives_bound (ell m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (r : ℝ), |r| ≤ 1 →
      |iteratedDeriv m (fun x : ℝ => zonal N ell x - x^ell) r| ≤ C/(N : ℝ) := by
  have hCs : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → 2*j ≤ ell →
      |zonalCoefficient N ell j - if j = 0 then 1 else 0| ≤ C/(N : ℝ) := by
    intro j
    by_cases hj : 2*j ≤ ell
    · obtain ⟨C, hC, hb⟩ := zonalCoefficient_error_bound hj
      exact ⟨C, hC, fun N hN _ => hb N hN⟩
    · exact ⟨1, zero_lt_one, fun _ _ h => (hj h).elim⟩
  choose C hC hbound using hCs
  let D : ℝ := ∑ j ∈ Finset.range (ell/2+1),
    C j * ((ell-2*j).descFactorial m : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg
    (fun j _ => mul_nonneg (hC j).le (Nat.cast_nonneg _))
  refine ⟨D+1, by positivity, ?_⟩
  intro N hN r hr
  rw [zonal_sub_pow_eq_sum]
  rw [iteratedDeriv_fun_sum (fun j _ => by fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow, ← mul_assoc]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ j ∈ Finset.range (ell/2+1),
        |(zonalCoefficient N ell j - if j = 0 then 1 else 0) *
          ((ell-2*j).descFactorial m : ℝ) * r^(ell-2*j-m)|) ≤
        ∑ j ∈ Finset.range (ell/2+1),
          (C j * ((ell-2*j).descFactorial m : ℝ))/(N : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : 2*j ≤ ell := by
        have := Finset.mem_range.mp hj
        omega
      have hrpow : |r|^(ell-2*j-m) ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
      have hDf : (0 : ℝ) ≤ ((ell-2*j).descFactorial m : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hDf]
      calc
        _ ≤ (C j/(N : ℝ))*((ell-2*j).descFactorial m : ℝ)*1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right (hbound j N hN hj') hDf) hrpow
            (pow_nonneg (abs_nonneg r) _)
            (mul_nonneg (div_nonneg (hC j).le (Nat.cast_nonneg N)) hDf)
        _ = _ := by ring
    _ = D/(N : ℝ) := by rw [← Finset.sum_div]
    _ ≤ (D+1)/(N : ℝ) := by gcongr; linarith

/-- The sharper first-derivative estimate `(eq:ent-zonal-derivative)`. -/
theorem zonal_derivative_bound (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (r : ℝ), |r| ≤ 1 →
      |deriv (zonal N ell) r| ≤ C*(|r|^(ell-1)+(N : ℝ)⁻¹) := by
  obtain ⟨C, hC, hb⟩ := zonal_sub_pow_derivatives_bound ell 1
  refine ⟨C+(ell : ℝ)+1, by positivity, ?_⟩
  intro N hN r hr
  have hd : Differentiable ℝ (zonal N ell) :=
    (contDiff_zonal N ell).differentiable (by simp)
  have he : deriv (fun x : ℝ => zonal N ell x-x^ell) r =
      deriv (zonal N ell) r - (ell : ℝ)*r^(ell-1) :=
    ((hd r).hasDerivAt.sub (hasDerivAt_pow ell r)).deriv
  have hb' : |deriv (zonal N ell) r-(ell : ℝ)*r^(ell-1)| ≤ C/(N : ℝ) := by
    simpa only [iteratedDeriv_one, he] using hb N hN r hr
  have hn : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  have hp : 0 ≤ |r|^(ell-1) := pow_nonneg (abs_nonneg r) _
  calc
    |deriv (zonal N ell) r| =
        |(deriv (zonal N ell) r-(ell : ℝ)*r^(ell-1))+(ell : ℝ)*r^(ell-1)| := by
      congr 1
      ring
    _ ≤ |deriv (zonal N ell) r-(ell : ℝ)*r^(ell-1)| +
        |(ell : ℝ)*r^(ell-1)| := abs_add_le _ _
    _ ≤ C/(N : ℝ)+(ell : ℝ)*|r|^(ell-1) := by
      have hEll : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
      rw [abs_mul, abs_of_nonneg hEll, abs_pow]
      gcongr
    _ ≤ (C+(ell : ℝ)+1)*(|r|^(ell-1)+(N : ℝ)⁻¹) := by
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg (show 0 ≤ C+1 by linarith) hp,
        mul_nonneg (show 0 ≤ (ell : ℝ)+1 by positivity) hn]

/-- The Gamma formula has exactly the source asymptotic, with its stated
`O(1/N)` remainder after multiplication by `N^j`. -/
theorem gammaWeight_asymptotic {p j : ℕ} (hj : 2*j ≤ p) :
    (fun N : ℕ => gammaWeight N p j * (N : ℝ)^j - leadingWeight p j)
      =O[atTop] (fun N : ℕ => (N : ℝ)⁻¹) := by
  apply (weight_asymptotic hj).congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [gammaWeight_eq_weight hN]

/-- The scaled harmonic weights converge to the explicit leading constant. -/
theorem weight_scaled_tendsto {p j : ℕ} (hj : 2*j ≤ p) :
    Tendsto (fun N : ℕ => weight N p j*(N : ℝ)^j)
      atTop (𝓝 (leadingWeight p j)) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (differentiableAt_weightProfile p j).continuousAt.tendsto.comp ht
  rw [weightProfile_zero hj] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  exact (weight_mul_dimension_pow hN hj).symm

/-- The bound accompanying `(eq:ent-harmonic-asymp)`, initially in its
asymptotic form with the dimension threshold explicit through `eventually`. -/
theorem weight_bound_eventually {p j : ℕ} (hj : 2*j ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      weight N p j ≤ C/(N : ℝ)^j := by
  obtain ⟨C, hC, hb⟩ := isBigO_iff'.mp ((weight_scaled_tendsto hj).isBigO_one ℝ)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop 3] with N hb hN
  have hn : 0 < (N : ℝ)^j := pow_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hw : 0 < weight N p j := weight_pos hN p j
  have hb' : weight N p j*(N : ℝ)^j ≤ C := by
    simpa only [Real.norm_eq_abs, abs_of_pos (mul_pos hw hn), norm_one, mul_one] using hb
  exact (le_div_iff₀ hn).mpr hb'

/-- Relative-error form of the manuscript asymptotic, with an explicit
`O(1/N)` function and equality in every source dimension. -/
theorem gammaWeight_asymptotic_literal {p j : ℕ} (hj : 2*j ≤ p) :
    ∃ e : ℕ → ℝ, e =O[atTop] (fun N : ℕ => (N : ℝ)⁻¹) ∧
      ∀ N : ℕ, 3 ≤ N → gammaWeight N p j =
        leadingWeight p j/(N : ℝ)^j*(1+e N) := by
  have hL : leadingWeight p j ≠ 0 := by unfold leadingWeight; positivity
  let e : ℕ → ℝ := fun N => weight N p j*(N : ℝ)^j/leadingWeight p j-1
  refine ⟨e, ?_, ?_⟩
  · have h := (weight_asymptotic hj).const_mul_left (leadingWeight p j)⁻¹
    apply h.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
    exact Filter.Eventually.of_forall fun N => by
      dsimp [e]
      field_simp
  · intro N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [gammaWeight_eq_weight hN]
    dsimp [e]
    field_simp
    ring

/-- One positive constant and one dimension threshold work for every
harmonic sector of the fixed degree, as in `(eq:ent-harmonic-asymp)`. -/
theorem gammaWeights_bound (p : ℕ) :
    ∃ (C : ℝ) (N0 : ℕ), 0 < C ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ j : ℕ, 2*j ≤ p → gammaWeight N p j ≤ C/(N : ℝ)^j := by
  have hCs : ∀ j : Fin (p/2+1), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, weight N p j ≤ C/(N : ℝ)^(j : ℕ) := by
    intro j
    apply weight_bound_eventually
    have := j.isLt
    omega
  choose C hC hb using hCs
  have hsum : 0 ≤ ∑ j : Fin (p/2+1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  have hAll := Filter.eventually_all.mpr hb
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hAll
  refine ⟨(∑ j : Fin (p/2+1), C j)+1, max N0 3, by positivity, ?_⟩
  intro N hN j hj
  have hN3 : 3 ≤ N := (le_max_right N0 3).trans hN
  have hN0' : N0 ≤ N := (le_max_left N0 3).trans hN
  let i : Fin (p/2+1) := ⟨j, by omega⟩
  rw [gammaWeight_eq_weight hN3]
  apply (hN0 N hN0' i).trans
  have hi : C i ≤ ∑ j : Fin (p/2+1), C j :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The source weight bound with one constant depending only on the degree,
uniform over every sector and every dimension `N ≥ 3`. -/
theorem gammaWeights_bound_all_dimensions (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → ∀ j : ℕ, 2*j ≤ p →
      gammaWeight N p j ≤ C/(N : ℝ)^j := by
  obtain ⟨C, N0, hC, hb⟩ := gammaWeights_bound p
  let T : ℕ → ℝ := fun N => ∑ j ∈ Finset.range (p/2+1),
    |gammaWeight N p j| * (N : ℝ)^j
  have hT : ∀ N, 0 ≤ T N := fun N =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (by positivity))
  let D : ℝ := ∑ N ∈ Finset.range N0, T N
  have hD : 0 ≤ D := Finset.sum_nonneg (fun N _ => hT N)
  refine ⟨C+D+1, by positivity, ?_⟩
  intro N hN j hj
  have hn : 0 < (N : ℝ)^j := pow_pos (by exact_mod_cast (show 0 < N by omega)) _
  by_cases hlarge : N0 ≤ N
  · apply (hb N hlarge j hj).trans
    exact div_le_div_of_nonneg_right (by linarith) hn.le
  · have hmemN : N ∈ Finset.range N0 := Finset.mem_range.mpr (by omega)
    have hmemj : j ∈ Finset.range (p/2+1) := Finset.mem_range.mpr (by omega)
    have hinner : |gammaWeight N p j| * (N : ℝ)^j ≤ T N := by
      change |gammaWeight N p j| * (N : ℝ)^j ≤
        ∑ i ∈ Finset.range (p/2+1), |gammaWeight N p i| * (N : ℝ)^i
      exact Finset.single_le_sum
        (f := fun i : ℕ => |gammaWeight N p i| * (N : ℝ)^i)
        (fun i _ => by positivity) hmemj
    have houter : T N ≤ D := by
      change T N ≤ ∑ i ∈ Finset.range N0, T i
      exact Finset.single_le_sum (fun i _ => hT i) hmemN
    rw [abs_of_pos (gammaWeight_pos hN p j)] at hinner
    apply (le_div_iff₀ hn).mpr
    linarith

/-- One constant controls the function and all its first `m` derivatives,
with the exact simultaneous quantifiers in `lem:ent-harmonic`(3). -/
theorem zonal_sub_pow_all_derivatives_bound (ell m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (r : ℝ), |r| ≤ 1 →
      ∀ k : ℕ, k ≤ m →
        |iteratedDeriv k (fun x : ℝ => zonal N ell x-x^ell) r| ≤ C/(N : ℝ) := by
  choose C hC hb using (fun k : ℕ => zonal_sub_pow_derivatives_bound ell k)
  let D : ℝ := ∑ k ∈ Finset.range (m+1), C k
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => (hC k).le)
  refine ⟨D+1, by positivity, ?_⟩
  intro N hN r hr k hk
  apply (hb k N hN r hr).trans
  have hmem : k ∈ Finset.range (m+1) := Finset.mem_range.mpr (by omega)
  have hCk : C k ≤ D := by
    change C k ≤ ∑ i ∈ Finset.range (m+1), C i
    exact Finset.single_le_sum (fun i _ => (hC i).le) hmem
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

end SlowEquilibration.SourceEntranceHarmonic
