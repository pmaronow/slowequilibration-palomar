-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceEntranceHarmonic
public import SlowEquilibration.GaussianRegression
public import SlowEquilibration.SourceSphericalSharpMoments
public import SlowEquilibration.PureTensorJetFeatures
public import Mathlib.Algebra.BigOperators.Intervals

/-! Exact finite-degree scalar identities for manuscript `lem:ent-harmonic`.
The arbitrary power expansion and sum-to-one use the printed Gamma weights.
The finite Gegenbauer sum is normalized at one in every degree and satisfies
the printed differential equation. Together with `SourceEntranceHarmonic`,
this proves all scalar clauses of the lemma without a literature interface.

The Gaussian lemmas use actual orthogonal projections of the coefficient
vector and prove centering, joint Gaussianity, Gram covariance, and full-field
independence. The actual degree-zero sector of each even-degree field is
constructed as its uniform spherical mean, with its exact Gamma-weight
covariance and independence from the full remainder field and from other
original degrees. The construction and identification of the positive-degree
harmonic sectors remain separate mathematical obligations.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic
open scoped BigOperators Topology
set_option autoImplicit false

private theorem rising_succ (a : ℝ) (k : ℕ) :
    rising a (k+1) = rising a k * (a+k) := by
  simp [rising, Finset.prod_range_succ]

/-- Adjacent coefficients cancel in the Gegenbauer differential equation. -/
theorem zonalCoefficient_adjacent {N ell j : ℕ} (hN : 3 ≤ N)
    (hj : 2*(j+1) ≤ ell) :
    zonalCoefficient N ell (j+1) *
        (4 * (j+1 : ℕ) * (alpha N + (ell-(j+1) : ℕ))) =
      -zonalCoefficient N ell j * (ell-2*j : ℕ) * (ell-2*j-1 : ℕ) := by
  have hi : ell-j = (ell-(j+1))+1 := by omega
  have hk : ell-2*j = (ell-2*(j+1))+2 := by omega
  have hk1 : ell-2*j-1 = (ell-2*(j+1))+1 := by omega
  have hR := (rising_pos (by linarith [alpha_pos hN] : 0 < 2*alpha N) ell).ne'
  unfold zonalCoefficient
  rw [hi, hk1, hk, rising_succ, Nat.factorial_succ j]
  rw [show (ell-2*(j+1))+2 = ((ell-2*(j+1))+1)+1 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ, pow_succ]
  push_cast
  field_simp
  ring1

private theorem monomial_first (k : ℕ) (r : ℝ) :
    r * ((k : ℝ) * r^(k-1)) = (k : ℝ) * r^k := by
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel, pow_succ]; ring1

private theorem monomial_second (k : ℕ) (r : ℝ) :
    r^2 * ((k.descFactorial 2 : ℝ) * r^(k-2)) =
      ((k : ℝ) * (k-1 : ℕ)) * r^k := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp
    | succ k =>
      have hd : (k+1+1).descFactorial 2 = (k+1+1)*(k+1) := by
        simp [Nat.descFactorial_succ, mul_comm]
      rw [hd, show k+1+1-2 = k by omega, show k+1+1-1 = k+1 by omega]
      push_cast
      simp only [pow_succ]
      ring1

private theorem monomial_ode (N ell k : ℕ) (c r : ℝ) :
    (1-r^2) * (c * (k.descFactorial 2 : ℝ) * r^(k-2)) -
        ((N : ℝ)-1)*r*(c*(k : ℝ)*r^(k-1)) +
        (ell : ℝ)*(ell+(N : ℝ)-2)*(c*r^k) =
      c * (k.descFactorial 2 : ℝ) * r^(k-2) +
        c*((ell : ℝ)*(ell+(N : ℝ)-2)-(k : ℝ)*(k+(N : ℝ)-2))*r^k := by
  have h1 := monomial_first k r
  have h2 := monomial_second k r
  have hdf : (k.descFactorial 2 : ℝ) = (k : ℝ)*(k-1 : ℕ) := by
    simp [Nat.descFactorial_succ, mul_comm]
  rw [hdf] at h2 ⊢
  have hc : (k : ℝ) * (k-1 : ℕ) = (k : ℝ)*((k : ℝ)-1) := by
    cases k with
    | zero => simp
    | succ k => simp
  rw [hc] at h2 ⊢
  linear_combination -c*h2 - ((N : ℝ)-1)*c*h1

/-- Differentiating the literal finite sum gives its coefficient formula
at every derivative order. -/
theorem iteratedDeriv_zonal (N ell m : ℕ) (r : ℝ) :
    iteratedDeriv m (zonal N ell) r =
      ∑ j ∈ Finset.range (ell/2+1), zonalCoefficient N ell j *
        ((ell-2*j).descFactorial m : ℝ) * r^(ell-2*j-m) := by
  have he : zonal N ell = fun x => ∑ j ∈ Finset.range (ell/2+1),
      zonalCoefficient N ell j * x^(ell-2*j) := funext (zonal_eq_sum N ell)
  rw [he, iteratedDeriv_fun_sum (fun j _ => by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow, mul_assoc]

private theorem zonalCoefficient_eigenvalue {N ell j : ℕ} (hN : 3 ≤ N)
    (hj : 2*(j+1) ≤ ell) :
    zonalCoefficient N ell j * ((ell-2*j).descFactorial 2 : ℝ) =
      -zonalCoefficient N ell (j+1) *
        ((ell : ℝ)*(ell+(N : ℝ)-2) -
          (ell-2*(j+1) : ℕ)*((ell-2*(j+1) : ℕ)+(N : ℝ)-2)) := by
  have h := zonalCoefficient_adjacent hN hj
  have he : (ell : ℝ) = (ell-2*(j+1) : ℕ) + 2*((j : ℝ)+1) := by
    exact_mod_cast (show ell = (ell-2*(j+1))+2*(j+1) by omega)
  have he' : (ell-(j+1) : ℕ) = (ell-2*(j+1) : ℕ)+(j+1 : ℕ) := by
    omega
  have hdf : ((ell-2*j).descFactorial 2 : ℝ) =
      (ell-2*j : ℕ)*(ell-2*j-1 : ℕ) := by
    simp [Nat.descFactorial_succ, mul_comm]
  rw [hdf]
  rw [he', alpha] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [he]
  linear_combination h

/-- The literal normalized Gegenbauer sum satisfies `(eq:ent-zonal-ode)`
at every real argument, in every manuscript dimension. -/
theorem zonal_ode {N : ℕ} (hN : 3 ≤ N) (ell : ℕ) (r : ℝ) :
    (1-r^2) * deriv (deriv (zonal N ell)) r -
      ((N : ℝ)-1)*r*deriv (zonal N ell) r +
      (ell : ℝ)*(ell+(N : ℝ)-2)*zonal N ell r = 0 := by
  let A : ℕ → ℝ := fun j => zonalCoefficient N ell j *
    ((ell-2*j).descFactorial 2 : ℝ) * r^(ell-2*j-2)
  let B : ℕ → ℝ := fun j => zonalCoefficient N ell j *
    ((ell : ℝ)*(ell+(N : ℝ)-2) -
      (ell-2*j : ℕ)*((ell-2*j : ℕ)+(N : ℝ)-2))*r^(ell-2*j)
  have hA : A (ell/2) = 0 := by
    have hk : ell-2*(ell/2) < 2 := by omega
    have hz : (ell-2*(ell/2)).descFactorial 2 = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr hk
    change zonalCoefficient N ell (ell/2) *
      ((ell-2*(ell/2)).descFactorial 2 : ℝ) * r^(ell-2*(ell/2)-2) = 0
    rw [hz]
    simp
  have hB : B 0 = 0 := by simp [B]
  have hAB : ∀ j ∈ Finset.range (ell/2), B (j+1) = -A j := by
    intro j hj
    have hj' : 2*(j+1) ≤ ell := by
      have := Finset.mem_range.mp hj
      omega
    have hc := zonalCoefficient_eigenvalue hN hj'
    have hp : ell-2*j-2 = ell-2*(j+1) := by omega
    change zonalCoefficient N ell (j+1) *
      ((ell : ℝ)*(ell+(N : ℝ)-2) -
        (ell-2*(j+1) : ℕ)*((ell-2*(j+1) : ℕ)+(N : ℝ)-2))*r^(ell-2*(j+1)) =
      -(zonalCoefficient N ell j * ((ell-2*j).descFactorial 2 : ℝ) * r^(ell-2*j-2))
    rw [hp]
    linear_combination r^(ell-2*(j+1)) * hc
  have hsum : (∑ j ∈ Finset.range (ell/2+1), (A j + B j)) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_range_succ A,
      Finset.sum_range_succ' B, hA, hB]
    simp only [add_zero]
    rw [Finset.sum_congr rfl hAB, Finset.sum_neg_distrib]
    ring1
  have he : deriv (zonal N ell) r = ∑ j ∈ Finset.range (ell/2+1),
      zonalCoefficient N ell j * (ell-2*j : ℕ) * r^(ell-2*j-1) := by
    simpa only [iteratedDeriv_one, Nat.descFactorial_one] using
      iteratedDeriv_zonal N ell 1 r
  have he2 : deriv (deriv (zonal N ell)) r =
      ∑ j ∈ Finset.range (ell/2+1), zonalCoefficient N ell j *
        ((ell-2*j).descFactorial 2 : ℝ) * r^(ell-2*j-2) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      iteratedDeriv_zonal N ell 2 r
  rw [he, he2, zonal_eq_sum]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (ell/2+1), (A j+B j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact monomial_ode N ell (ell-2*j) (zonalCoefficient N ell j) r
    _ = 0 := hsum

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic
open scoped BigOperators

private theorem expansion_rising_add (a : ℝ) (m n : ℕ) :
    rising a (m+n) = rising a m * rising (a+m) n := by
  unfold rising
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Nat.cast_add]
  ring1

private theorem expansion_rising_succ_left (a : ℝ) (n : ℕ) :
    rising a (n+1) = a * rising (a+1) n := by
  unfold rising
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring1

private def expansionTelescoper (b : ℝ) (s k : ℕ) : ℝ :=
  (-1 : ℝ)^k * (k : ℝ) * ((s+1-k : ℕ) : ℝ) /
    (((s+1-k).factorial : ℝ) * (k.factorial : ℝ) * rising (b+k) s)

private theorem expansion_telescoping_step {b : ℝ} (hb : 0 < b)
    (s k : ℕ) (hk : k ≤ s) :
    (s : ℝ) * ((-1 : ℝ)^k * (b+2*k) /
      (((s-k).factorial : ℝ) * (k.factorial : ℝ) * rising (b+k) (s+1))) =
      expansionTelescoper b s k - expansionTelescoper b s (k+1) := by
  have hr : 0 < rising (b+k) s := rising_pos (by positivity) s
  have hr' : rising (b+(k+1 : ℕ)) s =
      rising (b+k) s * (b+k+s) / (b+k) := by
    apply (eq_div_iff (by positivity : b+(k : ℝ) ≠ 0)).mpr
    calc
      rising (b+(k+1 : ℕ)) s * (b+k) = rising (b+k) (s+1) := by
        rw [expansion_rising_succ_left]
        push_cast
        simp only [add_assoc]
        ring1
      _ = rising (b+k) s * (b+k+s) := by rw [rising_succ]
  have hsub : s+1-k = (s-k)+1 := by omega
  have hsub' : s+1-(k+1) = s-k := by omega
  have hcast : ((s-k : ℕ) : ℝ) = (s : ℝ)-(k : ℝ) := by
    exact Nat.cast_sub hk
  have hkreal : (k : ℝ) ≤ s := by exact_mod_cast hk
  have hne : (1 : ℝ)+s-k ≠ 0 := by linarith
  have hbk : b+(k : ℝ) ≠ 0 := by positivity
  have hbks : b+(k : ℝ)+(s : ℝ) ≠ 0 := by positivity
  unfold expansionTelescoper
  rw [hsub, hsub', Nat.factorial_succ, Nat.factorial_succ, hr', rising_succ,
    pow_succ]
  push_cast
  rw [hcast]
  field_simp [hr.ne', hne, hbk, hbks]
  ring_nf
  field_simp [hne, hbk, hbks, hr.ne']
  ring1

/-- The finite inverse-Gegenbauer coefficient sum cancels in every lower degree. -/
theorem inverse_gegenbauer_coefficient_sum {b : ℝ} (hb : 0 < b) (s : ℕ) :
    (∑ k ∈ Finset.range (s+1),
      (-1 : ℝ)^k * (b+2*k) /
        (((s-k).factorial : ℝ) * (k.factorial : ℝ) * rising (b+k) (s+1))) =
      if s = 0 then 1 else 0 := by
  by_cases hs : s = 0
  · subst s
    simp [rising, hb.ne']
  · rw [ite_eq_right_iff.mpr (fun h => (hs h).elim)]
    have hsum : (s : ℝ) * (∑ k ∈ Finset.range (s+1),
        (-1 : ℝ)^k * (b+2*k) /
          (((s-k).factorial : ℝ) * (k.factorial : ℝ) * rising (b+k) (s+1))) = 0 := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ k ∈ Finset.range (s+1),
            (expansionTelescoper b s k - expansionTelescoper b s (k+1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact expansion_telescoping_step hb s k (by
            have := Finset.mem_range.mp hk
            omega)
        _ = 0 := by rw [Finset.sum_range_sub']; simp [expansionTelescoper]
    exact (mul_eq_zero.mp hsum).resolve_left (by exact_mod_cast hs)

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic
open scoped BigOperators

/-- A product of a harmonic weight and a zonal coefficient has the exact
inverse-Gegenbauer summand used in the reconstruction identity. -/
theorem weight_mul_zonalCoefficient {N p s j : ℕ} (hN : 3 ≤ N)
    (hs : 2*s ≤ p) (hj : j ≤ s) :
    weight N p j * zonalCoefficient N (p-2*j) (s-j) =
      (p.factorial : ℝ) / (2^(2*s) * ((p-2*s).factorial : ℝ)) *
        ((-1 : ℝ)^(s-j) *
          (alpha N + (p-2*s : ℕ) + 2*(s-j : ℕ)) /
          ((j.factorial : ℝ) * ((s-j).factorial : ℝ) *
            rising (alpha N + (p-2*s : ℕ) + (s-j : ℕ)) (s+1))) := by
  have hsub : p-2*j-2*(s-j) = p-2*s := by omega
  have hidx : p-2*j-(s-j) = p-s-j := by omega
  have hden : p-j+1 = (p-s-j)+(s+1) := by omega
  have harg : p-s-j = (p-2*s)+(s-j) := by omega
  have hdeg : p-2*j = (p-2*s)+2*(s-j) := by omega
  have hpow : (2 : ℝ)^p = 2^(2*s) * 2^(p-2*s) := by
    rw [← pow_add]
    congr 1
    omega
  have hR := (rising_pos (by linarith [alpha_pos hN] : 0 < 2*alpha N) (p-2*j)).ne'
  have hA := (rising_pos (alpha_pos hN) (p-s-j)).ne'
  have hR' : rising (alpha N*2) (p-j*2) ≠ 0 := by
    simpa only [mul_comm] using hR
  unfold weight zonalCoefficient
  rw [hsub, hidx, hden, expansion_rising_add, hpow]
  have he : alpha N + (p-s-j : ℕ) =
      alpha N + (p-2*s : ℕ) + (s-j : ℕ) := by rw [harg]; push_cast; ring1
  rw [he]
  have he' : (p-2*j : ℕ) + alpha N =
      alpha N + (p-2*s : ℕ) + 2*(s-j : ℕ) := by rw [hdeg]; push_cast; ring1
  rw [he']
  field_simp [hR, hA]
  ring_nf
  field_simp [hR']

/-- All coefficient convolutions in the arbitrary-degree power expansion. -/
theorem weight_zonalCoefficient_convolution {N p s : ℕ} (hN : 3 ≤ N)
    (hs : 2*s ≤ p) :
    (∑ j ∈ Finset.range (s+1),
      weight N p j * zonalCoefficient N (p-2*j) (s-j)) =
      if s = 0 then 1 else 0 := by
  have hb : 0 < alpha N + (p-2*s : ℕ) := by
    exact add_pos_of_pos_of_nonneg (alpha_pos hN) (Nat.cast_nonneg _)
  calc
    _ = (p.factorial : ℝ) / (2^(2*s) * ((p-2*s).factorial : ℝ)) *
        (∑ j ∈ Finset.range (s+1),
          (-1 : ℝ)^(s-j) *
            (alpha N + (p-2*s : ℕ) + 2*(s-j : ℕ)) /
            ((j.factorial : ℝ) * ((s-j).factorial : ℝ) *
              rising (alpha N + (p-2*s : ℕ) + (s-j : ℕ)) (s+1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact weight_mul_zonalCoefficient hN hs (by
        have := Finset.mem_range.mp hj
        omega)
    _ = (p.factorial : ℝ) / (2^(2*s) * ((p-2*s).factorial : ℝ)) *
        (if s = 0 then 1 else 0) := by
      congr 1
      rw [← Finset.sum_range_reflect _ (s+1)]
      calc
        _ = ∑ k ∈ Finset.range (s+1),
            (-1 : ℝ)^k * (alpha N + (p-2*s : ℕ) + 2*k) /
              (((s-k).factorial : ℝ) * (k.factorial : ℝ) *
                rising (alpha N + (p-2*s : ℕ) + k) (s+1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k ≤ s := by have := Finset.mem_range.mp hk; omega
          have hss : s-(s-k) = k := by omega
          simp only [Nat.add_sub_cancel, hss]
        _ = _ := inverse_gegenbauer_coefficient_sum hb s
    _ = if s = 0 then 1 else 0 := by
      by_cases hs0 : s = 0 <;> simp [hs0, Nat.factorial_ne_zero]

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option autoImplicit false

section GaussianProjections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual orthogonal projection of the standard Gaussian coefficient vector
has jointly Gaussian evaluations. This supplies the probability step of
`lem:ent-harmonic`(4); the harmonic coefficient subspaces themselves are not
constructed here. -/
theorem projected_evaluations_jointGaussian {ι : Type*} [Fintype ι]
    (V : ι → Submodule ℝ E) (v : ι → E) :
    HasGaussianLaw (fun z : E => fun i => inner ℝ (v i) ((V i).starProjection z))
      (stdGaussian E) := by
  simpa using
      (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
        (ContinuousLinearMap.pi (fun i =>
          (innerSL ℝ (v i)).comp (V i).starProjection))

/-- Every actual projected field evaluation is centered. -/
theorem projected_evaluation_mean (V : Submodule ℝ E) (v : E) :
    (∫ z : E, inner ℝ v (V.starProjection z) ∂stdGaussian E) = 0 := by
  simpa only [id_eq, integral_id_stdGaussian, map_zero,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
      ((innerSL ℝ v).comp V.starProjection).integral_comp_comm
        (IsGaussian.integrable_id (μ := stdGaussian E))

/-- Exact covariance of genuine projected Gaussian coefficients, before the
harmonic-subspace Gram kernel is identified with its zonal formula. -/
theorem projected_evaluations_covariance (V W : Submodule ℝ E) (v w : E) :
    cov[fun z : E => inner ℝ v (V.starProjection z),
      fun z : E => inner ℝ w (W.starProjection z); stdGaussian E] =
        inner ℝ (V.starProjection v) (W.starProjection w) := by
  have hv : (fun z : E => inner ℝ v (V.starProjection z)) =
      fun z => inner ℝ (V.starProjection v) z := by
    funext z
    exact (V.starProjection_isSymmetric v z).symm
  have hw : (fun z : E => inner ℝ w (W.starProjection z)) =
      fun z => inner ℝ (W.starProjection w) z := by
    funext z
    exact (W.starProjection_isSymmetric w z).symm
  rw [hv, hw, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

/-- Pairwise orthogonal coefficient subspaces yield independent genuine
Gaussian coefficient vectors, simultaneously for all subspaces. -/
theorem orthogonal_gaussian_projections_independent {ι : Type*} [Fintype ι]
    (V : ι → Submodule ℝ E)
    (hV : Pairwise (fun i j => V i ⟂ V j)) :
    iIndepFun (fun i (z : E) => (V i).starProjection z) (stdGaussian E) := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
    (ContinuousLinearMap.pi (fun i => (V i).starProjection))
  apply hG.iIndepFun_of_covariance_inner
  intro i j hij x y
  change cov[fun z : E => inner ℝ x ((V i).starProjection z),
    fun z : E => inner ℝ y ((V j).starProjection z); stdGaussian E] = 0
  rw [projected_evaluations_covariance]
  exact (hV hij).inner_eq ((V i).starProjection_apply_mem x)
    ((V j).starProjection_apply_mem y)

/-- Independence holds for the complete projected fields with the sigma
algebra of evaluations, including an arbitrary, possibly uncountable, sphere
index set. This is stronger than independence of a chosen finite list. -/
theorem orthogonal_gaussian_fields_independent {ι S : Type*} [Fintype ι]
    (V : ι → Submodule ℝ E) (hV : Pairwise (fun i j => V i ⟂ V j))
    (v : S → E) :
    iIndepFun (fun i (z : E) => fun x : S => inner ℝ (v x) ((V i).starProjection z))
      (stdGaussian E) := by
  exact (orthogonal_gaussian_projections_independent V hV).comp
    (fun _ z x => inner ℝ (v x) z)
    (fun _ => Measurable.of_eval (fun x => by fun_prop))

end GaussianProjections

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic
open scoped BigOperators
set_option autoImplicit false

private def endpointTerm (a : ℝ) (n j : ℕ) : ℝ :=
  if 2*j ≤ n then
    (-1 : ℝ)^j * rising a (n-j) /
      ((j.factorial : ℝ)*((n-2*j).factorial : ℝ)) * 2^(n-2*j)
  else 0

private def endpointSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), endpointTerm a n j

private theorem endpointTerm_zero_index (a : ℝ) (n : ℕ) :
    (n+2 : ℝ) * endpointTerm a (n+2) 0 =
      2*(n+a+1)*endpointTerm a (n+1) 0 := by
  simp only [endpointTerm, Nat.mul_zero, Nat.zero_le, ↓reduceIte, pow_zero,
    Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [rising_succ a (n+1), Nat.factorial_succ (n+1), pow_succ]
  push_cast
  have hn : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp [hn]
  ring1

private theorem endpointTerm_succ_index (a : ℝ) (n j : ℕ) :
    (n+2 : ℝ)*endpointTerm a (n+2) (j+1) =
      2*(n+a+1)*endpointTerm a (n+1) (j+1) -
        (n+2*a)*endpointTerm a n j := by
  by_cases hj : 2*j ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    cases m with
    | zero =>
      have h₁ : 2*j+0+2-(j+1) = j+1 := by omega
      have h₂ : 2*j+0-j = j := by omega
      have h₃ : 2*j+0+2-2*(j+1) = 0 := by omega
      have h₄ : 2*j+0-2*j = 0 := by omega
      simp only [endpointTerm, ite_eq_left (show 2*(j+1) ≤ 2*j+0+2 by omega),
        ite_eq_right (show ¬2*(j+1) ≤ 2*j+0+1 by omega),
        ite_eq_left (show 2*j ≤ 2*j+0 by omega), h₁, h₂, h₃, h₄,
        Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero]
      rw [rising_succ, Nat.factorial_succ, pow_succ]
      push_cast
      have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
      have hj1 : (j : ℝ)+1 ≠ 0 := by positivity
      field_simp [hjf, hj1]
      ring1
    | succ m =>
      have h₁ : 2*j+(m+1)+2-(j+1) = (j+m+1)+1 := by omega
      have h₂ : 2*j+(m+1)+1-(j+1) = j+m+1 := by omega
      have h₃ : 2*j+(m+1)-j = j+m+1 := by omega
      have h₄ : 2*j+(m+1)+2-2*(j+1) = m+1 := by omega
      have h₅ : 2*j+(m+1)+1-2*(j+1) = m := by omega
      have h₆ : 2*j+(m+1)-2*j = m+1 := by omega
      simp only [endpointTerm, ite_eq_left (show 2*(j+1) ≤ 2*j+(m+1)+2 by omega),
        ite_eq_left (show 2*(j+1) ≤ 2*j+(m+1)+1 by omega),
        ite_eq_left (show 2*j ≤ 2*j+(m+1) by omega), h₁, h₂, h₃, h₄, h₅, h₆]
      rw [rising_succ]
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
      have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
      have hj1 : (j : ℝ)+1 ≠ 0 := by positivity
      have hm1 : (m : ℝ)+1 ≠ 0 := by positivity
      field_simp [hjf, hmf, hj1, hm1]
      ring1
  · simp only [endpointTerm, ite_eq_right hj,
      ite_eq_right (show ¬2*(j+1) ≤ n+2 by omega),
      ite_eq_right (show ¬2*(j+1) ≤ n+1 by omega), mul_zero, sub_zero]

private theorem endpointSum_recurrence (a : ℝ) (n : ℕ) :
    (n+2 : ℝ)*endpointSum a (n+2) =
      2*(n+a+1)*endpointSum a (n+1) - (n+2*a)*endpointSum a n := by
  have ht₁ : endpointTerm a (n+1) (n+2) = 0 := by
    simp [endpointTerm, show ¬2*(n+2) ≤ n+1 by omega]
  have ht₂ : endpointTerm a n (n+1) = 0 := by
    simp [endpointTerm, show ¬2*(n+1) ≤ n by omega]
  have hs₁ : (∑ j ∈ Finset.range (n+2), endpointTerm a (n+1) (j+1)) +
      endpointTerm a (n+1) 0 = endpointSum a (n+1) := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ, ht₁, add_zero]
    rfl
  have hs₂ : (∑ j ∈ Finset.range (n+2), endpointTerm a n j) =
      endpointSum a n := by
    rw [Finset.sum_range_succ, ht₂, add_zero]
    rfl
  calc
    (n+2 : ℝ)*endpointSum a (n+2) =
        (∑ j ∈ Finset.range (n+2),
          (n+2 : ℝ)*endpointTerm a (n+2) (j+1)) +
            (n+2 : ℝ)*endpointTerm a (n+2) 0 := by
      rw [endpointSum, Finset.sum_range_succ', mul_add, Finset.mul_sum]
    _ = (∑ j ∈ Finset.range (n+2),
          (2*(n+a+1)*endpointTerm a (n+1) (j+1) -
            (n+2*a)*endpointTerm a n j)) +
              2*(n+a+1)*endpointTerm a (n+1) 0 := by
      rw [endpointTerm_zero_index]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => endpointTerm_succ_index a n j)
    _ = 2*(n+a+1)*endpointSum a (n+1) - (n+2*a)*endpointSum a n := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs₂]
      rw [← hs₁]
      ring1

private theorem rising_factorial_recurrence (a : ℝ) (n : ℕ) :
    (n+2 : ℝ)*(rising (2*a) (n+2) / ((n+2).factorial : ℝ)) =
      2*(n+a+1)*(rising (2*a) (n+1) / ((n+1).factorial : ℝ)) -
        (n+2*a)*(rising (2*a) n / (n.factorial : ℝ)) := by
  rw [rising_succ (2*a) (n+1), rising_succ (2*a) n,
    Nat.factorial_succ (n+1), Nat.factorial_succ n]
  push_cast
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp [hnf, hn1, hn2]
  ring1

private theorem endpointSum_eq (a : ℝ) (n : ℕ) :
    endpointSum a n = rising (2*a) n / (n.factorial : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [endpointSum, endpointTerm, rising]
  | one =>
    norm_num [endpointSum, endpointTerm, rising, Finset.sum_range_succ]
    ring1
  | more n ih₀ ih₁ =>
    have hn : (n+2 : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [endpointSum_recurrence, ih₀, ih₁, rising_factorial_recurrence]

/-- The finite Gegenbauer sum has the literal endpoint value printed before
`(eq:ent-zonal)`, in every degree. -/
theorem gegenbauer_at_one (N ell : ℕ) :
    gegenbauer N ell 1 = rising (2*alpha N) ell / (ell.factorial : ℝ) := by
  have hs : (∑ j ∈ Finset.range (ell/2+1), endpointTerm (alpha N) ell j) =
      endpointSum (alpha N) ell := by
    unfold endpointSum
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    simp [endpointTerm, show ¬2*j ≤ ell by omega]
  rw [← endpointSum_eq, ← hs]
  unfold gegenbauer
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  simp only [endpointTerm, ite_eq_left (show 2*j ≤ ell by omega), mul_one]

/-- General normalization of the literal zonal polynomial in `(eq:ent-zonal)`. -/
theorem zonal_at_one {N : ℕ} (hN : 3 ≤ N) (ell : ℕ) :
    zonal N ell 1 = 1 := by
  have hR := (rising_pos (by linarith [alpha_pos hN] : 0 < 2*alpha N) ell).ne'
  have hf : (ell.factorial : ℝ) ≠ 0 := by positivity
  rw [zonal, gegenbauer_at_one]
  field_simp

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic
open scoped BigOperators

private theorem expansion_sum_triangle (m : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range (m+1), ∑ k ∈ Finset.range (m-j+1), f j k) =
      ∑ s ∈ Finset.range (m+1), ∑ j ∈ Finset.range (s+1), f j (s-j) := by
  calc
    _ = ∑ j ∈ Finset.Ico 0 (m+1), ∑ s ∈ Finset.Ico j (m+1), f j (s-j) := by
      rw [Nat.Ico_zero_eq_range]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ m := by have := Finset.mem_range.mp hj; omega
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show m+1-j = m-j+1 by omega]
      simp only [Nat.add_sub_cancel_left]
    _ = _ := by
      rw [Finset.sum_Ico_Ico_comm]
      simp only [Nat.Ico_zero_eq_range]

/-- The arbitrary-degree reconstruction identity `(eq:ent-harmonic)`, with
finite-product coefficients and every real argument. -/
theorem power_expansion_weight {N : ℕ} (hN : 3 ≤ N) (p : ℕ) (r : ℝ) :
    r^p = ∑ j ∈ Finset.range (p/2+1), weight N p j * zonal N (p-2*j) r := by
  symm
  calc
    _ = ∑ j ∈ Finset.range (p/2+1),
        ∑ k ∈ Finset.range (p/2-j+1),
          weight N p j * zonalCoefficient N (p-2*j) k * r^(p-2*j-2*k) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ p/2 := by have := Finset.mem_range.mp hj; omega
      rw [zonal_eq_sum, Finset.mul_sum]
      rw [show (p-2*j)/2 = p/2-j by omega]
      apply Finset.sum_congr rfl
      intro k _
      ring1
    _ = ∑ s ∈ Finset.range (p/2+1),
        ∑ j ∈ Finset.range (s+1),
          weight N p j * zonalCoefficient N (p-2*j) (s-j) *
            r^(p-2*j-2*(s-j)) := expansion_sum_triangle _ _
    _ = ∑ s ∈ Finset.range (p/2+1),
        (∑ j ∈ Finset.range (s+1),
          weight N p j * zonalCoefficient N (p-2*j) (s-j)) * r^(p-2*s) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : 2*s ≤ p := by have := Finset.mem_range.mp hs; omega
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ s := by have := Finset.mem_range.mp hj; omega
      rw [show p-2*j-2*(s-j) = p-2*s by omega]
    _ = ∑ s ∈ Finset.range (p/2+1), (if s = 0 then 1 else 0) * r^(p-2*s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [weight_zonalCoefficient_convolution hN (by
        have := Finset.mem_range.mp hs
        omega)]
    _ = r^p := by simp

/-- The literal Gamma-coefficient power expansion in manuscript
`(eq:ent-harmonic)`, with no restriction on the real argument. -/
theorem power_expansion {N : ℕ} (hN : 3 ≤ N) (p : ℕ) (r : ℝ) :
    r^p = ∑ j ∈ Finset.range (p/2+1),
      gammaWeight N p j * zonal N (p-2*j) r := by
  simp_rw [gammaWeight_eq_weight hN]
  exact power_expansion_weight hN p r

/-- The finite-product harmonic weights sum to one in every degree. -/
theorem weight_sum_one {N : ℕ} (hN : 3 ≤ N) (p : ℕ) :
    (∑ j ∈ Finset.range (p/2+1), weight N p j) = 1 := by
  simpa only [one_pow, zonal_at_one hN, mul_one] using
    (power_expansion_weight hN p 1).symm

/-- Sum-to-one for the literal Gamma formula in `lem:ent-harmonic`(1). -/
theorem gammaWeight_sum_one {N : ℕ} (hN : 3 ≤ N) (p : ℕ) :
    (∑ j ∈ Finset.range (p/2+1), gammaWeight N p j) = 1 := by
  simp_rw [gammaWeight_eq_weight hN]
  exact weight_sum_one hN p

/-- Each actual harmonic weight is a probability weight. -/
theorem gammaWeight_le_one {N p j : ℕ} (hN : 3 ≤ N) (hj : 2*j ≤ p) :
    gammaWeight N p j ≤ 1 := by
  rw [← gammaWeight_sum_one hN p]
  exact Finset.single_le_sum (fun k _ => (gammaWeight_pos hN p k).le)
    (Finset.mem_range.mpr (by omega))

/-- Literal scalar clause (1) of `lem:ent-harmonic`, in arbitrary degree,
with the printed Gamma coefficients and no additional hypothesis. -/
theorem harmonic_coefficients_scalar {N : ℕ} (hN : 3 ≤ N) (p : ℕ) :
    (∀ r : ℝ, r^p = ∑ j ∈ Finset.range (p/2+1),
      gammaWeight N p j * zonal N (p-2*j) r) ∧
    (∀ j : ℕ, 2*j ≤ p → 0 < gammaWeight N p j) ∧
    (∑ j ∈ Finset.range (p/2+1), gammaWeight N p j) = 1 := by
  exact ⟨power_expansion hN p, fun j _ => gammaWeight_pos hN p j,
    gammaWeight_sum_one hN p⟩

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic
open scoped BigOperators
set_option autoImplicit false

private theorem bottom_rising_scale (N k : ℕ) :
    (2 : ℝ)^k * rising (alpha N+1) k =
      ∏ i ∈ Finset.range k, ((N+2*i : ℕ) : ℝ) := by
  induction k with
  | zero => simp [rising]
  | succ k ih =>
    rw [pow_succ, rising_succ, Finset.prod_range_succ]
    push_cast at ih ⊢
    rw [← ih]
    unfold alpha
    ring1

private theorem bottom_factorial (k : ℕ) :
    ((2*k).factorial : ℝ) =
      2^k * (k.factorial : ℝ) *
        ∏ i ∈ Finset.range k, ((2*i+1 : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega,
      Nat.factorial_succ (2*k+1), Nat.factorial_succ (2*k),
      Nat.factorial_succ k, Finset.prod_range_succ, pow_succ]
    push_cast at ih ⊢
    rw [ih]
    ring1

/-- The degree-zero sector of an even power has the literal spherical
moment coefficient, as a finite product over all pair contractions. -/
theorem gammaWeight_even_bottom {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    gammaWeight N (2*k) k =
      ∏ i ∈ Finset.range k, ((2*i+1 : ℕ) : ℝ) / ((N+2*i : ℕ) : ℝ) := by
  have ha := (alpha_pos hN).ne'
  have hr := (rising_pos (by linarith [alpha_pos hN] : 0 < alpha N+1) k).ne'
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have hp : 2*k-k = k := by omega
  have hz : rising (2*alpha N) 0 = 1 := by simp [rising]
  have hpow : (2 : ℝ)^(2*k) = (2^k)^2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [gammaWeight_eq_weight hN]
  simp only [weight, hp, Nat.sub_self, Nat.cast_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, hz, mul_one]
  rw [expansion_rising_succ_left, Finset.prod_div_distrib,
    ← bottom_rising_scale, bottom_factorial, hpow]
  field_simp [ha, hr, hf]

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open MeasureTheory ProbabilityTheory SphericalModel
open SourceEntranceHarmonic
open SphericalAging.FiniteModel hiding Vector
open SphericalAging.OrthogonalGaussianDisclosure
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false

section ConstantSector

/-- Actual coefficient feature of the degree-`p` field of amplitude `c`. -/
def pureCoefficientFeature (N p : ℕ) (c : ℝ) (x : Vector N) :
    EuclideanSpace ℝ (TensorIndex N p) :=
  Real.sqrt c • (normalization N p •
    PureTensorJetFeatures.tensorFeature (fun _ : Fin p => x))

private theorem pureCoefficientFeature_continuous (N p : ℕ) (c : ℝ) :
    Continuous (pureCoefficientFeature N p c) := by
  unfold pureCoefficientFeature
  exact (((PureTensorJetFeatures.tensorFeature_continuous N p).comp
    (show Continuous (fun x : Vector N => fun _ : Fin p => x) by fun_prop)).const_smul
      (normalization N p)).const_smul (Real.sqrt c)

private theorem pureCoefficientFeature_integrable {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (c : ℝ) :
    Integrable (pureCoefficientFeature N p c) (sphereLaw N) :=
  SphericalForm.integrable_sphereSupported_continuous (sphereLaw N)
    (sphereLaw_support hN) (pureCoefficientFeature_continuous N p c)

/-- The coefficient feature evaluates the original ordered-tensor Hamiltonian. -/
theorem pureCoefficientFeature_field {N p : ℕ} (c : ℝ)
    (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) :
    inner ℝ (pureCoefficientFeature N p c x) (WithLp.toLp 2 J) =
      Real.sqrt c * Hamiltonian N p J x := by
  rw [SphericalAging.TensorHamiltonianRotation.Hamiltonian_eq_tensor_inner]
  unfold pureCoefficientFeature
  rw [real_inner_smul_left, real_inner_smul_left, real_inner_comm]
  rfl

private theorem pureCoefficientFeature_inner {N p : ℕ} (hN : 1 ≤ N)
    (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c) (x y : Vector N) :
    inner ℝ (pureCoefficientFeature N p c x) (pureCoefficientFeature N p c y) =
      (N : ℝ)*c*(overlap x y)^p := by
  simp only [pureCoefficientFeature, real_inner_smul_left, real_inner_smul_right,
    PureTensorJetFeatures.tensorFeature_inner, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  calc
    _ = (Real.sqrt c)^2 * (normalization N p)^2 * (inner ℝ x y)^p := by ring1
    _ = c*((N : ℝ)*((inner ℝ x y)/(N : ℝ))^p) := by
      rw [Real.sq_sqrt hc, normalization_sq N p (by omega)]
      rw [mul_assoc, dimension_covariance_scale N p (by omega) hp]
    _ = (N : ℝ)*c*(overlap x y)^p := by unfold overlap; ring1

/-- The actual coefficient vector of the constant spherical harmonic. -/
def constantSectorFeature (N p : ℕ) (c : ℝ) :
    EuclideanSpace ℝ (TensorIndex N p) :=
  ∫ x, pureCoefficientFeature N p c x ∂sphereLaw N

/-- The degree-zero sector is defined by the literal uniform spherical mean. -/
def constantSector (N p : ℕ) (c : ℝ)
    (J : SphericalAging.FiniteModel.Disorder N p) : ℝ :=
  ∫ x, Real.sqrt c * Hamiltonian N p J x ∂sphereLaw N

/-- The spherical mean is an actual linear Gaussian coefficient observation. -/
theorem constantSector_eq_inner {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (c : ℝ)
    (J : SphericalAging.FiniteModel.Disorder N p) :
    constantSector N p c J =
      inner ℝ (constantSectorFeature N p c) (WithLp.toLp 2 J) := by
  unfold constantSector constantSectorFeature
  calc
    _ = ∫ x, inner ℝ (WithLp.toLp 2 J) (pureCoefficientFeature N p c x)
        ∂sphereLaw N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← pureCoefficientFeature_field]
        exact real_inner_comm _ _
    _ = _ := by
      rw [integral_inner (pureCoefficientFeature_integrable hN p c), real_inner_comm]

private theorem pureCoefficientFeature_constant_inner {N k : ℕ}
    (hN : 3 ≤ N) (hk : 1 ≤ k) {c : ℝ} (hc : 0 ≤ c)
    (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    inner ℝ (pureCoefficientFeature N (2*k) c x) (constantSectorFeature N (2*k) c) =
      (N : ℝ)*c*gammaWeight N (2*k) k := by
  unfold constantSectorFeature
  rw [← integral_inner (pureCoefficientFeature_integrable (by omega) (2*k) c)]
  simp_rw [pureCoefficientFeature_inner (by omega : 1 ≤ N) (by omega : 1 ≤ 2*k) hc]
  rw [integral_const_mul,
    SourceSphericalSharpMoments.sphere_axis_even_moment N (by omega) k x hx,
    ← gammaWeight_even_bottom hN k]

private theorem constantSectorFeature_inner_self {N k : ℕ}
    (hN : 3 ≤ N) (hk : 1 ≤ k) {c : ℝ} (hc : 0 ≤ c) :
    inner ℝ (constantSectorFeature N (2*k) c) (constantSectorFeature N (2*k) c) =
      (N : ℝ)*c*gammaWeight N (2*k) k := by
  calc
    _ = ∫ x, inner ℝ (constantSectorFeature N (2*k) c)
        (pureCoefficientFeature N (2*k) c x) ∂sphereLaw N := by
      exact (integral_inner (pureCoefficientFeature_integrable (by omega) (2*k) c)
        (constantSectorFeature N (2*k) c)).symm
    _ = ∫ _x : Vector N, (N : ℝ)*c*gammaWeight N (2*k) k ∂sphereLaw N := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_support (by omega : 1 ≤ N)] with x hx
      rw [real_inner_comm]
      exact pureCoefficientFeature_constant_inner hN hk hc x hx
    _ = _ := by simp

private theorem constantSectorFeature_projection {N k : ℕ}
    (hN : 3 ≤ N) (hk : 1 ≤ k) {c : ℝ} (hc : 0 ≤ c)
    (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    (ℝ ∙ constantSectorFeature N (2*k) c).starProjection
      (pureCoefficientFeature N (2*k) c x) = constantSectorFeature N (2*k) c := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.mem_span_singleton_self _)
  intro w hw
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [real_inner_smul_right, inner_sub_left,
    pureCoefficientFeature_constant_inner hN hk hc x hx,
    constantSectorFeature_inner_self hN hk hc, sub_self, mul_zero]

/-- The constant sector and every finite family of remainder evaluations are
jointly Gaussian under the original product disorder law. -/
theorem constantSector_jointGaussian {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (c : ℝ)
    {ι : Type*} [Fintype ι] (x : ι → Vector N) :
    HasGaussianLaw (fun J : SphericalAging.FiniteModel.Disorder N p =>
      (constantSector N p c J,
        fun i => Real.sqrt c * Hamiltonian N p J (x i) - constantSector N p c J))
      (SphericalAging.FiniteModel.disorderLaw N p) := by
  have h := (ordered_tensor_hasLaw N p).hasGaussianLaw.map_fun
    ((innerSL ℝ (constantSectorFeature N p c)).prod
      (ContinuousLinearMap.pi (fun i =>
        innerSL ℝ (pureCoefficientFeature N p c (x i) - constantSectorFeature N p c))))
  change HasGaussianLaw (fun J : SphericalAging.FiniteModel.Disorder N p =>
    (inner ℝ (constantSectorFeature N p c) (WithLp.toLp 2 J),
      fun i => inner ℝ (pureCoefficientFeature N p c (x i) - constantSectorFeature N p c)
        (WithLp.toLp 2 J))) (SphericalAging.FiniteModel.disorderLaw N p) at h
  simpa only [inner_sub_left, ← constantSector_eq_inner hN,
    pureCoefficientFeature_field] using h

/-- The genuine degree-zero harmonic sector is centered. -/
theorem constantSector_mean {N : ℕ} (hN : 1 ≤ N) (p : ℕ) (c : ℝ) :
    (∫ J, constantSector N p c J ∂SphericalAging.FiniteModel.disorderLaw N p) = 0 := by
  simp_rw [constantSector_eq_inner hN]
  have h := (ordered_tensor_hasLaw N p).integral_comp
    (show AEStronglyMeasurable (innerSL ℝ (constantSectorFeature N p c))
      (stdGaussian (EuclideanSpace ℝ (TensorIndex N p))) by fun_prop)
  exact h.trans (integral_strongDual_stdGaussian _)

/-- Exact degree-zero covariance in `lem:ent-harmonic`(4), for every even
supported degree and every nonnegative amplitude, including amplitude zero. -/
theorem constantSector_covariance {N k : ℕ} (hN : 3 ≤ N) (hk : 1 ≤ k)
    {c : ℝ} (hc : 0 ≤ c) :
    cov[constantSector N (2*k) c, constantSector N (2*k) c;
      SphericalAging.FiniteModel.disorderLaw N (2*k)] =
        (N : ℝ)*c*gammaWeight N (2*k) k := by
  change cov[(fun J => constantSector N (2*k) c J),
    (fun J => constantSector N (2*k) c J);
    SphericalAging.FiniteModel.disorderLaw N (2*k)] = _
  simp_rw [constantSector_eq_inner (by omega : 1 ≤ N)]
  rw [tensor_inner_covariance, constantSectorFeature_inner_self hN hk hc]

/-- The literal second moment in `(eq:ent-sector-cov)` for the actual
constant spherical harmonic; its zonal factor is exactly `Z_0=1`. -/
theorem constantSector_secondMoment {N k : ℕ} (hN : 3 ≤ N) (hk : 1 ≤ k)
    {c : ℝ} (hc : 0 ≤ c) (x y : Vector N) :
    (∫ J, constantSector N (2*k) c J * constantSector N (2*k) c J
      ∂SphericalAging.FiniteModel.disorderLaw N (2*k)) =
        (N : ℝ)*c*gammaWeight N (2*k) k*zonal N 0 (overlap x y) := by
  have hG := (constantSector_jointGaussian (by omega : 1 ≤ N) (2*k) c
    (fun _ : Fin 0 => (0 : Vector N))).fst
  have h := constantSector_covariance hN hk hc
  rw [covariance_eq_sub hG.memLp_two hG.memLp_two,
    constantSector_mean (by omega : 1 ≤ N), zero_mul, sub_zero] at h
  simpa only [Pi.mul_apply, zonal_zero, mul_one] using h

/-- Subtracting the actual constant sector leaves exactly zero spherical
mean, pointwise for every tensor sample. -/
theorem constantSector_remainder_sphereMean {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (c : ℝ) (J : SphericalAging.FiniteModel.Disorder N p) :
    (∫ x, (Real.sqrt c * Hamiltonian N p J x - constantSector N p c J)
      ∂sphereLaw N) = 0 := by
  have hi : Integrable (fun x => Real.sqrt c * Hamiltonian N p J x) (sphereLaw N) := by
    simpa only [pureCoefficientFeature_field] using
      (pureCoefficientFeature_integrable hN p c).inner_const (𝕜 := ℝ) (WithLp.toLp 2 J)
  rw [integral_sub hi (integrable_const _)]
  simp [constantSector]

/-- The actual constant harmonic is independent of the entire remaining
sphere field under the original tensor disorder law. -/
theorem constantSector_remainder_independent {N k : ℕ}
    (hN : 3 ≤ N) (hk : 1 ≤ k) {c : ℝ} (hc : 0 ≤ c) :
    IndepFun (constantSector N (2*k) c)
      (fun J : SphericalAging.FiniteModel.Disorder N (2*k) =>
        fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
          Real.sqrt c * Hamiltonian N (2*k) J x.val - constantSector N (2*k) c J)
      (SphericalAging.FiniteModel.disorderLaw N (2*k)) := by
  let b := constantSectorFeature N (2*k) c
  let T : Submodule ℝ (EuclideanSpace ℝ (TensorIndex N (2*k))) := ℝ ∙ b
  have hb : T.starProjection b = b :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self b)
  have h := (tensor_projections_independent T).comp
    (show Measurable (fun z => inner ℝ b z) by fun_prop)
    (show Measurable (fun z => fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
      inner ℝ (pureCoefficientFeature N (2*k) c x.val) z) from
      Measurable.of_eval (fun _ => by fun_prop))
  apply h.congr
  · exact Filter.Eventually.of_forall fun J => by
      dsimp only [Function.comp_def]
      rw [← T.inner_starProjection_left_eq_right, hb]
      exact (constantSector_eq_inner (by omega) (2*k) c J).symm
  · exact Filter.Eventually.of_forall fun J => by
      funext x
      dsimp only [Function.comp_def]
      rw [← Tᗮ.inner_starProjection_left_eq_right,
        Submodule.starProjection_orthogonal_val]
      have hx : T.starProjection (pureCoefficientFeature N (2*k) c x.val) = b :=
        constantSectorFeature_projection hN hk hc x.val x.property
      rw [hx, inner_sub_left, pureCoefficientFeature_field]
      rw [constantSector_eq_inner (by omega)]

/-- Constant sectors belonging to distinct original mixture degrees are
independent under the actual product disorder law. -/
theorem constantSectors_independent_degrees {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) :
    iIndepFun (fun p (J : SphericalModel.Disorder N P) =>
      constantSector N p.val.val (c p) (J p)) (SphericalModel.disorderLaw N P) := by
  apply (SphericalModel.independent_degree_blocks N P).comp
    (fun p => constantSector N p.val.val (c p))
  intro p
  have heq : constantSector N p.val.val (c p) =
      (fun J => inner ℝ (constantSectorFeature N p.val.val (c p)) (WithLp.toLp 2 J)) :=
    funext (constantSector_eq_inner hN p.val.val (c p))
  rw [heq]
  exact (show Measurable (fun z : EuclideanSpace ℝ (TensorIndex N p.val.val) =>
    inner ℝ (constantSectorFeature N p.val.val (c p)) z) by fun_prop).comp
      (PiLp.continuous_toLp 2 _).measurable

end ConstantSector

end SlowEquilibration.SourceEntranceHarmonicFinal

namespace SlowEquilibration.SourceEntranceHarmonicFinal

open SourceEntranceHarmonic Filter Asymptotics
open scoped BigOperators Topology
set_option autoImplicit false

/-- The relative error in `(eq:ent-harmonic-asymp)` has one constant and one
threshold depending only on the fixed degree, uniformly over all its sectors. -/
theorem gammaWeights_relative_error_uniform (p : ℕ) :
    ∃ (C : ℝ) (N0 : ℕ), 0 < C ∧ 3 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ j : ℕ, 2*j ≤ p →
        |gammaWeight N p j / (leadingWeight p j / (N : ℝ)^j) - 1| ≤ C/(N : ℝ) := by
  have hCs : ∀ j : Fin (p/2+1), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        |gammaWeight N p j / (leadingWeight p j / (N : ℝ)^(j : ℕ)) - 1| ≤
          C/(N : ℝ) := by
    intro j
    have hj : 2*(j : ℕ) ≤ p := by have := j.isLt; omega
    obtain ⟨e, he, heq⟩ := gammaWeight_asymptotic_literal hj
    obtain ⟨C, hC, hb⟩ := isBigO_iff'.mp he
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, eventually_ge_atTop 3] with N hb hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hL : leadingWeight p j / (N : ℝ)^(j : ℕ) ≠ 0 := by
      apply div_ne_zero
      · unfold leadingWeight
        positivity
      · exact (pow_pos hn _).ne'
    rw [heq N hN, mul_div_cancel_left₀ _ hL, add_sub_cancel_left]
    simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), div_eq_mul_inv]
      using hb
  choose C hC hb using hCs
  have hsum : 0 ≤ ∑ j : Fin (p/2+1), C j :=
    Finset.sum_nonneg (fun j _ => (hC j).le)
  have hAll := Filter.eventually_all.mpr hb
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hAll
  refine ⟨(∑ j : Fin (p/2+1), C j)+1, max N0 3, by positivity,
    le_max_right _ _, ?_⟩
  intro N hN j hj
  have hN0' : N0 ≤ N := (le_max_left N0 3).trans hN
  let i : Fin (p/2+1) := ⟨j, by omega⟩
  apply (hN0 N hN0' i).trans
  have hi : C i ≤ ∑ j : Fin (p/2+1), C j :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

end SlowEquilibration.SourceEntranceHarmonicFinal
