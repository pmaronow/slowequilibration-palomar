module

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
public import SphericalAging.FilteredQuadraticVariation
public import StochasticCalculus.ItoFormulaPartition

public section

/-!
# Quadratic covariation of the actual independent coordinate drivers

All independence below comes from the whole coordinate path laws in
`BrownianDriver`. In particular, coefficient processes may observe the full
filtration and the initial background.

The deterministic stopped-partition estimates are adapted from Ezzeri Esa's
`StochasticCalculus.QuadraticVariation` (Apache 2.0).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorQuadraticVariation
open HardSphereDynamics VectorIto
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
lemma coordinate_functionals_independent (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (f g : (ℝ≥0 → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun ω => f (fun t => D.coordinate i t ω))
      (fun ω => g (fun t => D.coordinate j t ω)) P :=
  (D.independent.indepFun hij).comp hf hg

omit [IsProbabilityMeasure P] in
lemma increment_product_memLp (D : BrownianDriver N P 𝓕) (i j : Fin N)
    (a b c d : ℝ≥0) :
    MemLp (fun ω => increment D i a b ω * increment D j c d ω) 2 P := by
  have := holderTriple_four_four_two
  exact MemLp.fun_mul
    ((D.filtered i).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_sub.memLp
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞))
    ((D.filtered j).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_sub.memLp
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞))

@[expose] def incrementProduct (D : BrownianDriver N P 𝓕) (i j : Fin N) (a b c d : ℝ≥0) :
    RandomL2 P := (increment_product_memLp D i j a b c d).toLp _

omit [IsProbabilityMeasure P] in
lemma incrementProduct_coe (D : BrownianDriver N P 𝓕) (i j : Fin N) (a b c d : ℝ≥0) :
    (incrementProduct D i j a b c d : Ω → ℝ) =ᵐ[P]
      fun ω => increment D i a b ω * increment D j c d ω := MemLp.coeFn_toLp _

omit [IsProbabilityMeasure P] in
lemma separate_increments_independent (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (a b c d : ℝ≥0) :
    IndepFun (increment D i a b) (increment D j c d) P :=
  coordinate_functionals_independent D hij (fun f => f b - f a) (fun f => f d - f c)
    ((measurable_pi_apply b).sub (measurable_pi_apply a))
    ((measurable_pi_apply d).sub (measurable_pi_apply c))

omit [IsProbabilityMeasure P] in
lemma norm_sq_incrementProduct (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d) :
    ‖incrementProduct D i j a b c d‖ ^ 2 =
      ((b : ℝ) - a) * ((d : ℝ) - c) := by
  have hsq := (separate_increments_independent D hij a b c d).integral_fun_comp_mul_comp
    (f := fun x : ℝ => x ^ 2) (g := fun x : ℝ => x ^ 2)
    (increment_memLp_two D i a b).aemeasurable
    (increment_memLp_two D j c d).aemeasurable (by fun_prop) (by fun_prop)
  rw [increment_integral_sq D i hab, increment_integral_sq D j hcd] at hsq
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← hsq]
  apply integral_congr_ae
  filter_upwards [incrementProduct_coe D i j a b c d] with ω hω
  rw [hω]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit [IsProbabilityMeasure P] in
lemma inner_incrementProduct_disjoint (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) {a b c d e f g h : ℝ≥0}
    (hab : a ≤ b) (hbe : b ≤ e) (hef : e ≤ f) :
    inner ℝ (incrementProduct D i j a b c d) (incrementProduct D i j e f g h) = 0 := by
  have hInd := coordinate_functionals_independent D hij
    (fun x => (x b - x a) * (x f - x e))
    (fun x => (x d - x c) * (x h - x g)) (by fun_prop) (by fun_prop)
  have hfac := hInd.integral_fun_mul_eq_mul_integral
    (((increment_memLp_two D i a b).aestronglyMeasurable).mul
      (increment_memLp_two D i e f).aestronglyMeasurable)
    (((increment_memLp_two D j c d).aestronglyMeasurable).mul
      (increment_memLp_two D j g h).aestronglyMeasurable)
  have hzero : ∫ ω, increment D i a b ω * increment D i e f ω ∂P = 0 :=
    integral_incr_mul_incr (D.filtered i).toIsPreBrownianReal hab hbe hef
  change (∫ ω, (increment D i a b ω * increment D i e f ω) *
      (increment D j c d ω * increment D j g h ω) ∂P) =
      (∫ ω, increment D i a b ω * increment D i e f ω ∂P) *
      (∫ ω, increment D j c d ω * increment D j g h ω ∂P) at hfac
  rw [hzero, zero_mul] at hfac
  rw [L2.inner_def, ← hfac]
  apply integral_congr_ae
  filter_upwards [incrementProduct_coe D i j a b c d,
    incrementProduct_coe D i j e f g h] with ω h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

@[expose] noncomputable def stoppedUniformPartitionTime
    (t a : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  min (uniformPartitionTime t n i) a

lemma monotone_stoppedUniformPartitionTime (t a : ℝ≥0) (n : ℕ) :
    Monotone (stoppedUniformPartitionTime t a n) := by
  intro i j hij
  unfold stoppedUniformPartitionTime uniformPartitionTime
  exact min_le_min (by gcongr) le_rfl

lemma stoppedUniformPartitionTime_zero (t a : ℝ≥0) (n : ℕ) :
    stoppedUniformPartitionTime t a n 0 = 0 := by
  simp only [stoppedUniformPartitionTime, uniformPartitionTime, Nat.cast_zero,
    mul_zero, zero_div]
  exact min_eq_left bot_le

lemma stoppedUniformPartitionTime_top
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    stoppedUniformPartitionTime t a n n = min t a := by
  unfold stoppedUniformPartitionTime uniformPartitionTime
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [mul_div_cancel_right₀ t hn0]

lemma stoppedUniformPartitionWidth_toReal
    (t a : ℝ≥0) (n i : ℕ) :
    (nndist
      ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
      ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) =
      (stoppedUniformPartitionTime t a n (i + 1) : ℝ) -
        (stoppedUniformPartitionTime t a n i : ℝ) := by
  rw [← dist_nndist, Real.dist_eq, abs_of_nonneg]
  exact sub_nonneg.mpr (by
    exact_mod_cast monotone_stoppedUniformPartitionTime t a n
      (Nat.le_add_right i 1))

lemma sum_stoppedUniformPartitionWidth
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n,
      (nndist
        ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
        ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) =
      (min t a : ℝ≥0) := by
  simp_rw [stoppedUniformPartitionWidth_toReal]
  rw [Finset.sum_range_sub
      (fun i => (stoppedUniformPartitionTime t a n i : ℝ)) n,
    stoppedUniformPartitionTime_top t a hn,
    stoppedUniformPartitionTime_zero]
  simp only [NNReal.coe_zero, sub_zero]

lemma stoppedUniformPartitionWidth_le_mesh
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (nndist
      ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
      ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ≤
      ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
  rw [stoppedUniformPartitionWidth_toReal]
  have hmono :
      (stoppedUniformPartitionTime t a n i : ℝ) ≤
        (stoppedUniformPartitionTime t a n (i + 1) : ℝ) := by
    exact_mod_cast monotone_stoppedUniformPartitionTime t a n
      (Nat.le_add_right i 1)
  have hmin := abs_min_sub_min_le_max
    (uniformPartitionTime t n (i + 1) : ℝ) (a : ℝ)
    (uniformPartitionTime t n i : ℝ) (a : ℝ)
  have hraw :
      |(stoppedUniformPartitionTime t a n (i + 1) : ℝ) -
        (stoppedUniformPartitionTime t a n i : ℝ)| ≤
      |(uniformPartitionTime t n (i + 1) : ℝ) -
        (uniformPartitionTime t n i : ℝ)| := by
    simpa only [stoppedUniformPartitionTime, NNReal.coe_min, sub_self,
      abs_zero, max_eq_left (abs_nonneg
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)))] using hmin
  rw [← abs_of_nonneg (sub_nonneg.mpr hmono)]
  calc
    |(stoppedUniformPartitionTime t a n (i + 1) : ℝ) -
        (stoppedUniformPartitionTime t a n i : ℝ)| ≤
        |(uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)| := hraw
    _ = ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
      simpa only [NNReal.dist_eq] using dist_uniformPartitionTime_succ_eq t hn i

lemma sum_stoppedUniformPartitionWidth_sq_le
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n,
      2 * (nndist
        ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
        ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ^ 2 ≤
      2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) * (min t a : ℝ≥0) := by
  calc
    ∑ i ∈ Finset.range n,
        2 * (nndist
          ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
          ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ^ 2 ≤
        ∑ i ∈ Finset.range n,
          2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) *
            (nndist
              ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
              ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hd0 : 0 ≤ (nndist
          ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
          ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) := NNReal.coe_nonneg _
      have hdle := stoppedUniformPartitionWidth_le_mesh t a hn i
      nlinarith only [hd0, hdle]
    _ = 2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) *
        (∑ i ∈ Finset.range n,
          (nndist
            ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
            ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = 2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) * (min t a : ℝ≥0) := by
      rw [sum_stoppedUniformPartitionWidth t a hn]


omit [IsProbabilityMeasure P] in
lemma norm_sq_incrementProduct_sum (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (a b : ℕ → ℝ≥0) (ha : Monotone a) (hb : Monotone b) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, incrementProduct D i j (a k) (a (k + 1))
      (b k) (b (k + 1))‖ ^ 2 =
      ∑ k ∈ Finset.range n, ((a (k + 1) : ℝ) - a k) * ((b (k + 1) : ℝ) - b k) := by
  let V (k : ℕ) := incrementProduct D i j (a k) (a (k + 1)) (b k) (b (k + 1))
  have horth {k l : ℕ} (hkl : k ≠ l) : inner ℝ (V k) (V l) = 0 := by
    rcases lt_or_gt_of_ne hkl with h | h
    · exact inner_incrementProduct_disjoint D hij
        (ha (Nat.le_succ k)) (ha (Nat.succ_le_of_lt h)) (ha (Nat.le_succ l))
    · rw [real_inner_comm]
      exact inner_incrementProduct_disjoint D hij
        (ha (Nat.le_succ l)) (ha (Nat.succ_le_of_lt h)) (ha (Nat.le_succ k))
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · rw [real_inner_self_eq_norm_sq]
    exact norm_sq_incrementProduct D hij (ha (Nat.le_succ k)) (hb (Nat.le_succ k))
  · intro l _ hl
    exact horth hl.symm
  · exact fun h => (h hk).elim

@[expose] def stoppedCovariationLp (D : BrownianDriver N P 𝓕) (i j : Fin N)
    (a b t : ℝ≥0) (n : ℕ) : RandomL2 P :=
  ∑ k ∈ Finset.range n, incrementProduct D i j
    (stoppedUniformPartitionTime t a n k) (stoppedUniformPartitionTime t a n (k + 1))
    (stoppedUniformPartitionTime t b n k) (stoppedUniformPartitionTime t b n (k + 1))

omit [IsProbabilityMeasure P] in
lemma stoppedCovariationLp_coe (D : BrownianDriver N P 𝓕) (i j : Fin N)
    (a b t : ℝ≥0) (n : ℕ) :
    (stoppedCovariationLp D i j a b t n : Ω → ℝ) =ᵐ[P]
      quadraticCovariationApprox (fun s ω => D.coordinate i (min s a) ω)
        (fun s ω => D.coordinate j (min s b) ω) t n := by
  have hterm : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range n,
      (incrementProduct D i j (stoppedUniformPartitionTime t a n k)
          (stoppedUniformPartitionTime t a n (k + 1))
          (stoppedUniformPartitionTime t b n k)
          (stoppedUniformPartitionTime t b n (k + 1)) : Ω → ℝ) ω =
      increment D i (stoppedUniformPartitionTime t a n k)
        (stoppedUniformPartitionTime t a n (k + 1)) ω *
      increment D j (stoppedUniformPartitionTime t b n k)
        (stoppedUniformPartitionTime t b n (k + 1)) ω :=
    (Finset.range n).eventually_all.mpr (fun k _ => incrementProduct_coe D i j _ _ _ _)
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n) (fun k =>
    incrementProduct D i j (stoppedUniformPartitionTime t a n k)
      (stoppedUniformPartitionTime t a n (k + 1))
      (stoppedUniformPartitionTime t b n k)
      (stoppedUniformPartitionTime t b n (k + 1))), hterm] with ω hsum ht
  simp only [Finset.sum_apply] at hsum
  change ((∑ k ∈ Finset.range n, incrementProduct D i j
    (stoppedUniformPartitionTime t a n k) (stoppedUniformPartitionTime t a n (k + 1))
    (stoppedUniformPartitionTime t b n k) (stoppedUniformPartitionTime t b n (k + 1)) :
      RandomL2 P) : Ω → ℝ) ω = _
  rw [hsum]
  exact Finset.sum_congr rfl (fun k hk => ht k hk)

omit [IsProbabilityMeasure P] in
lemma norm_sq_stoppedCovariationLp_le (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (a b t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ‖stoppedCovariationLp D i j a b t n‖ ^ 2 ≤ (t : ℝ) ^ 2 / n := by
  rw [stoppedCovariationLp, norm_sq_incrementProduct_sum D hij _ _
    (monotone_stoppedUniformPartitionTime t a n)
    (monotone_stoppedUniformPartitionTime t b n)]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) *
        (nndist ((stoppedUniformPartitionTime t b n (k + 1) : ℝ))
          ((stoppedUniformPartitionTime t b n k : ℝ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [← stoppedUniformPartitionWidth_toReal, ← stoppedUniformPartitionWidth_toReal]
      exact mul_le_mul_of_nonneg_right (stoppedUniformPartitionWidth_le_mesh t a hn k)
        (NNReal.coe_nonneg _)
    _ = ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) * (min t b : ℝ≥0) := by
      rw [← Finset.mul_sum, sum_stoppedUniformPartitionWidth t b hn]
    _ ≤ ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) * t := by
      gcongr
      exact min_le_left _ _
    _ = (t : ℝ) ^ 2 / n := by
      rw [NNReal.coe_div]
      push_cast
      ring

omit [IsProbabilityMeasure P] in
lemma stopped_coordinate_covariation_zero (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (a b t : ℝ≥0) :
    TendstoInMeasure P (fun n => quadraticCovariationApprox
      (fun s ω => D.coordinate i (min s a) ω)
      (fun s ω => D.coordinate j (min s b) ω) t (n + 1)) atTop (fun _ => 0) := by
  let L (n : ℕ) := stoppedCovariationLp D i j a b t (n + 1)
  have hbound (n : ℕ) : ‖L n‖ ≤ Real.sqrt ((t : ℝ) ^ 2 / ((n : ℝ) + 1)) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
    simpa only [L, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      norm_sq_stoppedCovariationLp_le D hij a b t (Nat.zero_lt_succ n)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((t : ℝ) ^ 2 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => (t : ℝ) ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((t : ℝ) ^ 2)
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hdiv
  have hnorm : Tendsto (fun n => ‖L n‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound hsqrt
  have hL : Tendsto L atTop (𝓝 (0 : RandomL2 P)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero] using hnorm
  have hmeas := tendstoInMeasure_of_tendsto_Lp hL
  apply hmeas.congr
  · intro n
    exact stoppedCovariationLp_coe D i j a b t (n + 1)
  · exact Lp.coeFn_zero ℝ 2 P

lemma interval_coordinate_covariation_zero (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (a b c d t : ℝ≥0) :
    TendstoInMeasure P (fun n => quadraticCovariationApprox
      (fun s ω => D.coordinate i (min s b) ω - D.coordinate i (min s a) ω)
      (fun s ω => D.coordinate j (min s d) ω - D.coordinate j (min s c) ω)
      t (n + 1)) atTop (fun _ => 0) := by
  have hi (u s : ℝ≥0) : AEStronglyMeasurable (D.coordinate i (min s u)) P :=
    (D.coordinateStronglyMeasurable i _).aestronglyMeasurable
  have hj (u s : ℝ≥0) : AEStronglyMeasurable (D.coordinate j (min s u)) P :=
    (D.coordinateStronglyMeasurable j _).aestronglyMeasurable
  have hB := tendstoInMeasure_quadraticCovariationApprox_linearCombination_right
    (stopped_coordinate_covariation_zero D hij b d t)
    (stopped_coordinate_covariation_zero D hij b c t) (hi b) (hj d) (hj c) 1 (-1)
  have hA := tendstoInMeasure_quadraticCovariationApprox_linearCombination_right
    (stopped_coordinate_covariation_zero D hij a d t)
    (stopped_coordinate_covariation_zero D hij a c t) (hi a) (hj d) (hj c) 1 (-1)
  have hDC (s : ℝ≥0) : AEStronglyMeasurable
      (fun ω => 1 * D.coordinate j (min s d) ω + (-1) * D.coordinate j (min s c) ω) P :=
    (aestronglyMeasurable_const.mul (hj d s)).add
      (aestronglyMeasurable_const.mul (hj c s))
  have h := tendstoInMeasure_quadraticCovariationApprox_linearCombination_left
    hB hA (hi b) (hi a) hDC 1 (-1)
  apply h.congr
  · intro n
    exact Eventually.of_forall (fun ω => by
      unfold quadraticCovariationApprox
      apply Finset.sum_congr rfl
      intro k _
      ring)
  · exact Eventually.of_forall (fun _ => by ring)

lemma weighted_interval_coordinate_covariation_zero (D : BrownianDriver N P 𝓕)
    {i j : Fin N} (hij : i ≠ j) (a b c d t : ℝ≥0) (r q : Ω → ℝ)
    (hr : AEStronglyMeasurable r P) (hq : AEStronglyMeasurable q P) :
    TendstoInMeasure P (fun n => quadraticCovariationApprox
      (fun s ω => r ω * (D.coordinate i (min s b) ω - D.coordinate i (min s a) ω))
      (fun s ω => q ω * (D.coordinate j (min s d) ω - D.coordinate j (min s c) ω))
      t (n + 1)) atTop (fun _ => 0) := by
  have hi (s : ℝ≥0) : AEStronglyMeasurable
      (fun ω => D.coordinate i (min s b) ω - D.coordinate i (min s a) ω) P :=
    (D.coordinateStronglyMeasurable i _).aestronglyMeasurable.sub
      (D.coordinateStronglyMeasurable i _).aestronglyMeasurable
  have hj (s : ℝ≥0) : AEStronglyMeasurable
      (fun ω => D.coordinate j (min s d) ω - D.coordinate j (min s c) ω) P :=
    (D.coordinateStronglyMeasurable j _).aestronglyMeasurable.sub
      (D.coordinateStronglyMeasurable j _).aestronglyMeasurable
  simpa only [mul_zero] using tendstoInMeasure_quadraticCovariationApprox_timeConstant_mul
    (interval_coordinate_covariation_zero D hij a b c d t) hi hj r q hr hq

omit [IsProbabilityMeasure P] in
lemma covariation_congr_ae {X X' Y Y' : ℝ≥0 → Ω → ℝ}
    (hX : ∀ s, X s =ᵐ[P] X' s) (hY : ∀ s, Y s =ᵐ[P] Y' s) (t : ℝ≥0) (n : ℕ) :
    quadraticCovariationApprox X Y t n =ᵐ[P] quadraticCovariationApprox X' Y' t n := by
  have hall : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range n,
      X (uniformPartitionTime t n (k + 1)) ω = X' (uniformPartitionTime t n (k + 1)) ω ∧
      X (uniformPartitionTime t n k) ω = X' (uniformPartitionTime t n k) ω ∧
      Y (uniformPartitionTime t n (k + 1)) ω = Y' (uniformPartitionTime t n (k + 1)) ω ∧
      Y (uniformPartitionTime t n k) ω = Y' (uniformPartitionTime t n k) ω :=
    (Finset.range n).eventually_all.mpr (fun k _ =>
      (hX _).and ((hX _).and ((hY _).and (hY _))))
  filter_upwards [hall] with ω hω
  unfold quadraticCovariationApprox
  exact Finset.sum_congr rfl (fun k hk => by
    obtain ⟨h1, h2, h3, h4⟩ := hω k hk
    rw [h1, h2, h3, h4])

lemma covariation_finset_sum_zero {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ) (X : ι → ℝ≥0 → Ω → ℝ)
    (Y : κ → ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (hX : ∀ i ∈ S, ∀ s, AEStronglyMeasurable (X i s) P)
    (hY : ∀ j ∈ T, ∀ s, AEStronglyMeasurable (Y j s) P)
    (hCov : ∀ i ∈ S, ∀ j ∈ T, TendstoInMeasure P
      (fun n => quadraticCovariationApprox (X i) (Y j) t (n + 1)) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n => quadraticCovariationApprox
      (fun s ω => ∑ i ∈ S, X i s ω) (fun s ω => ∑ j ∈ T, Y j s ω) t (n + 1))
      atTop (fun _ => 0) := by
  have hSumY (s : ℝ≥0) : AEStronglyMeasurable (fun ω => ∑ j ∈ T, Y j s ω) P := by
    convert Finset.aestronglyMeasurable_sum T (fun j hj => hY j hj s) using 1
    funext ω
    rw [Finset.sum_apply]
  have hi (i : ι) (hi : i ∈ S) : TendstoInMeasure P (fun n =>
      quadraticCovariationApprox (fun s ω => ∑ j ∈ T, Y j s ω) (X i) t (n + 1))
      atTop (fun _ => 0) := by
    have hr := tendstoInMeasure_quadraticCovariationApprox_finset_sum T (X i) Y
      (fun _ => 1) (fun _ _ => 0) t (hX i hi) hY (hCov i hi)
    apply hr.congr
    · intro n
      exact Eventually.of_forall (fun ω => by
        simpa only [one_mul] using quadraticCovariationApprox_comm _ _ t (n + 1) ω)
    · exact Eventually.of_forall (fun _ => by simp)
  have hraw := tendstoInMeasure_quadraticCovariationApprox_finset_sum S
    (fun s ω => ∑ j ∈ T, Y j s ω) X (fun _ => 1) (fun _ _ => 0) t hSumY hX hi
  apply hraw.congr
  · intro n
    exact Eventually.of_forall (fun ω => by
      simpa only [one_mul] using quadraticCovariationApprox_comm _ _ t (n + 1) ω)
  · exact Eventually.of_forall (fun _ => by simp)

lemma elementary_coordinate_integral_covariation_zero (D : BrownianDriver N P 𝓕)
    {i j : Fin N} (hij : i ≠ j)
    (v w : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P →₀ ℝ)
    (t : ℝ≥0) : TendstoInMeasure P (fun n => quadraticCovariationApprox
      (coordinateProcess D i (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P v))
      (coordinateProcess D j (FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P w))
      t (n + 1)) atTop (fun _ => 0) := by
  classical
  let X (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P)
      (s : ℝ≥0) (ω : Ω) := v x * (x.2.2 : Ω → ℝ) ω *
        (D.coordinate i (min s x.2.1.1) ω - D.coordinate i (min s x.1) ω)
  let Y (y : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P)
      (s : ℝ≥0) (ω : Ω) := w y * (y.2.2 : Ω → ℝ) ω *
        (D.coordinate j (min s y.2.1.1) ω - D.coordinate j (min s y.1) ω)
  have hcm (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex 𝓕 P) :
      AEStronglyMeasurable (x.2.2 : Ω → ℝ) P :=
    (lpMeas.aestronglyMeasurable x.2.2).mono (𝓕.le x.1)
  have hx (x) (_ : x ∈ v.support) (s : ℝ≥0) : AEStronglyMeasurable (X x s) P :=
    (aestronglyMeasurable_const.mul (hcm x)).mul
      ((D.coordinateStronglyMeasurable i _).aestronglyMeasurable.sub
        (D.coordinateStronglyMeasurable i _).aestronglyMeasurable)
  have hy (y) (_ : y ∈ w.support) (s : ℝ≥0) : AEStronglyMeasurable (Y y s) P :=
    (aestronglyMeasurable_const.mul (hcm y)).mul
      ((D.coordinateStronglyMeasurable j _).aestronglyMeasurable.sub
        (D.coordinateStronglyMeasurable j _).aestronglyMeasurable)
  have hcov (x) (_ : x ∈ v.support) (y) (_ : y ∈ w.support) :
      TendstoInMeasure P (fun n => quadraticCovariationApprox (X x) (Y y) t (n + 1))
        atTop (fun _ => 0) := weighted_interval_coordinate_covariation_zero D hij
    x.1 x.2.1.1 y.1 y.2.1.1 t
    (fun ω => v x * (x.2.2 : Ω → ℝ) ω) (fun ω => w y * (y.2.2 : Ω → ℝ) ω)
    (aestronglyMeasurable_const.mul (hcm x)) (aestronglyMeasurable_const.mul (hcm y))
  have hraw := covariation_finset_sum_zero v.support w.support X Y t hx hy hcov
  apply hraw.congr
  · intro n
    exact covariation_congr_ae
      (fun s => (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
        (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) v s).symm)
      (fun s => (FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
        (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) w s).symm) t (n + 1)
  · exact EventuallyEq.rfl

omit [IsProbabilityMeasure P] in
lemma integral_abs_covariationApprox_le {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ s, MemLp (X s) 2 P) (hY : ∀ s, MemLp (Y s) 2 P)
    (t : ℝ≥0) (n : ℕ) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hQX : ∫ ω, quadraticVariationApprox X t n ω ∂P ≤ K ^ 2)
    (hQY : ∫ ω, quadraticVariationApprox Y t n ω ∂P ≤ L ^ 2) :
    ∫ ω, |quadraticCovariationApprox X Y t n ω| ∂P ≤ K * L := by
  let QX := quadraticVariationApprox X t n
  let QY := quadraticVariationApprox Y t n
  have hiX : Integrable QX P := integrable_finsetSum (Finset.range n)
    (fun k _ => ((hX _).sub (hX _)).integrable_sq)
  have hiY : Integrable QY P := integrable_finsetSum (Finset.range n)
    (fun k _ => ((hY _).sub (hY _)).integrable_sq)
  have hmX : AEStronglyMeasurable (fun ω => Real.sqrt (QX ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hiX.aestronglyMeasurable
  have hmY : AEStronglyMeasurable (fun ω => Real.sqrt (QY ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hiY.aestronglyMeasurable
  have hlX : MemLp (fun ω => Real.sqrt (QX ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hmX).2
    exact hiX.congr (Eventually.of_forall (fun ω => by
      exact (Real.sq_sqrt (quadraticVariationApprox_nonneg X t n ω)).symm))
  have hlY : MemLp (fun ω => Real.sqrt (QY ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hmY).2
    exact hiY.congr (Eventually.of_forall (fun ω => by
      exact (Real.sq_sqrt (quadraticVariationApprox_nonneg Y t n ω)).symm))
  have hleft : Integrable (fun ω => |quadraticCovariationApprox X Y t n ω|) P := by
    apply Integrable.abs
    exact integrable_finsetSum (Finset.range n) (fun k _ =>
      ((hX _).sub (hX _)).integrable_mul ((hY _).sub (hY _)))
  have hright : Integrable (fun ω => Real.sqrt (QX ω) * Real.sqrt (QY ω)) P :=
    hlX.integrable_mul hlY
  have hpoint (ω : Ω) : |quadraticCovariationApprox X Y t n ω| ≤
      Real.sqrt (QX ω) * Real.sqrt (QY ω) := by
    calc
      _ ≤ Real.sqrt (QX ω * QY ω) :=
        Real.abs_le_sqrt (quadraticCovariationApprox_sq_le _ _ t n ω)
      _ = _ := Real.sqrt_mul (quadraticVariationApprox_nonneg X t n ω) _
  calc
    _ ≤ ∫ ω, Real.sqrt (QX ω) * Real.sqrt (QY ω) ∂P :=
      integral_mono_ae hleft hright (Eventually.of_forall hpoint)
    _ ≤ (∫ ω, (Real.sqrt (QX ω)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫ ω, (Real.sqrt (QY ω)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
      apply integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
        (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
      · simpa only [ENNReal.ofReal_ofNat] using hlX
      · simpa only [ENNReal.ofReal_ofNat] using hlY
    _ = Real.sqrt (∫ ω, QX ω ∂P) * Real.sqrt (∫ ω, QY ω ∂P) := by
      rw [show (∫ ω, (Real.sqrt (QX ω)) ^ (2 : ℝ) ∂P) = ∫ ω, QX ω ∂P by
          apply integral_congr_ae
          exact Eventually.of_forall (fun ω => by
            change (Real.sqrt (QX ω)) ^ (2 : ℝ) = QX ω
            rw [Real.rpow_two]
            exact Real.sq_sqrt (quadraticVariationApprox_nonneg X t n ω)),
        show (∫ ω, (Real.sqrt (QY ω)) ^ (2 : ℝ) ∂P) = ∫ ω, QY ω ∂P by
          apply integral_congr_ae
          exact Eventually.of_forall (fun ω => by
            change (Real.sqrt (QY ω)) ^ (2 : ℝ) = QY ω
            rw [Real.rpow_two]
            exact Real.sq_sqrt (quadraticVariationApprox_nonneg Y t n ω))]
      norm_num [← Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (K ^ 2) * Real.sqrt (L ^ 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hQX) (Real.sqrt_le_sqrt hQY)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = K * L := by rw [Real.sqrt_sq hK, Real.sqrt_sq hL]

lemma coordinateProcess_memLp (D : BrownianDriver N P 𝓕) (i : Fin N)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) : MemLp (coordinateProcess D i U t) 2 P :=
  MemLp.ae_eq (FourPapersCommon.FilteredBrownian.naturalItoProcess_ae_eq_representative
    (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U t)
    (Lp.memLp _)

lemma integral_abs_coordinate_covariation_le (D : BrownianDriver N P 𝓕) (i j : Fin N)
    (U V : PredictableProcessL2 𝓕 P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, |quadraticCovariationApprox (coordinateProcess D i U)
      (coordinateProcess D j V) t n ω| ∂P ≤ ‖U‖ * ‖V‖ := by
  apply integral_abs_covariationApprox_le (coordinateProcess_memLp D i U)
    (coordinateProcess_memLp D j V) t n (norm_nonneg _) (norm_nonneg _)
  · unfold coordinateProcess
    rw [FilteredQuadraticVariation.integral_quadraticVariationApprox_naturalItoProcessRepresentative
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U t hn]
    exact pow_le_pow_left₀ (norm_nonneg _) (FourPapersCommon.FilteredBrownian.norm_naturalItoProcess_le
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U t) 2
  · unfold coordinateProcess
    rw [FilteredQuadraticVariation.integral_quadraticVariationApprox_naturalItoProcessRepresentative
      (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) V t hn]
    exact pow_le_pow_left₀ (norm_nonneg _) (FourPapersCommon.FilteredBrownian.norm_naturalItoProcess_le
      (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) V t) 2

lemma coordinate_covariation_integrable (D : BrownianDriver N P 𝓕) (i j : Fin N)
    (U V : PredictableProcessL2 𝓕 P) (t : ℝ≥0) (n : ℕ) :
    Integrable (quadraticCovariationApprox (coordinateProcess D i U)
      (coordinateProcess D j V) t n) P :=
  integrable_finsetSum (Finset.range n) (fun _k _ =>
    ((coordinateProcess_memLp D i U _).sub (coordinateProcess_memLp D i U _)).integrable_mul
      ((coordinateProcess_memLp D j V _).sub (coordinateProcess_memLp D j V _)))

omit [IsProbabilityMeasure P] [MeasurableSpace Ω] in
lemma covariation_difference (X X' Y Y' : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    quadraticCovariationApprox X Y t n ω - quadraticCovariationApprox X' Y' t n ω =
      quadraticCovariationApprox (fun s ω => X s ω - X' s ω) Y t n ω +
      quadraticCovariationApprox X' (fun s ω => Y s ω - Y' s ω) t n ω := by
  unfold quadraticCovariationApprox
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma integral_abs_coordinate_covariation_sub_le (D : BrownianDriver N P 𝓕) (i j : Fin N)
    (U U' V V' : PredictableProcessL2 𝓕 P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, |quadraticCovariationApprox (coordinateProcess D i U) (coordinateProcess D j V) t n ω -
      quadraticCovariationApprox (coordinateProcess D i U') (coordinateProcess D j V') t n ω| ∂P ≤
      ‖U - U'‖ * ‖V‖ + ‖U'‖ * ‖V - V'‖ := by
  let A := quadraticCovariationApprox (coordinateProcess D i (U - U')) (coordinateProcess D j V) t n
  let C := quadraticCovariationApprox (coordinateProcess D i U') (coordinateProcess D j (V - V')) t n
  have hA := covariation_congr_ae (Y := coordinateProcess D j V)
    (fun s => FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_sub_ae
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) U U' s)
    (fun _ => EventuallyEq.rfl) t n
  have hC := covariation_congr_ae (X := coordinateProcess D i U') (fun _ => EventuallyEq.rfl)
    (fun s => FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_sub_ae
      (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) V V' s) t n
  have hd : (fun ω => quadraticCovariationApprox (coordinateProcess D i U)
      (coordinateProcess D j V) t n ω - quadraticCovariationApprox (coordinateProcess D i U')
      (coordinateProcess D j V') t n ω) =ᵐ[P] fun ω => A ω + C ω := by
    filter_upwards [hA, hC] with ω ha hc
    rw [covariation_difference]
    exact congrArg₂ (· + ·) ha hc
  have hiA : Integrable A P := coordinate_covariation_integrable D i j (U - U') V t n
  have hiC : Integrable C P := coordinate_covariation_integrable D i j U' (V - V') t n
  calc
    _ = ∫ ω, |A ω + C ω| ∂P := integral_congr_ae (hd.fun_comp abs)
    _ ≤ ∫ ω, |A ω| + |C ω| ∂P :=
      integral_mono_ae (hiA.add hiC).abs (hiA.abs.add hiC.abs)
        (Eventually.of_forall (fun ω => abs_add_le _ _))
    _ = (∫ ω, |A ω| ∂P) + ∫ ω, |C ω| ∂P := integral_add hiA.abs hiC.abs
    _ ≤ _ := add_le_add
      (integral_abs_coordinate_covariation_le D i j (U - U') V t hn)
      (integral_abs_coordinate_covariation_le D i j U' (V - V') t hn)

lemma coordinate_integral_covariation_zero (D : BrownianDriver N P 𝓕) {i j : Fin N}
    (hij : i ≠ j) (U V : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    TendstoInMeasure P (fun n => quadraticCovariationApprox (coordinateProcess D i U)
      (coordinateProcess D j V) t (n + 1)) atTop (fun _ => 0) := by
  let e := FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable 𝓕 P
  have hd := FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable (P := P) 𝓕
  obtain ⟨Uk, hUkRange, hUk⟩ := mem_closure_iff_seq_limit.mp (hd U)
  obtain ⟨Vk, hVkRange, hVk⟩ := mem_closure_iff_seq_limit.mp (hd V)
  choose u hu using hUkRange
  choose v hv using hVkRange
  let f : ℕ → Ω → ℝ := fun n => quadraticCovariationApprox (coordinateProcess D i U)
    (coordinateProcess D j V) t (n + 1)
  let F : ℕ → ℕ → Ω → ℝ := fun k n => quadraticCovariationApprox (coordinateProcess D i (Uk k))
    (coordinateProcess D j (Vk k)) t (n + 1)
  let a : ℕ → ℝ := fun k => ‖U - Uk k‖ * ‖V‖ + ‖Uk k‖ * ‖V - Vk k‖
  have ha : Tendsto a atTop (𝓝 0) := by
    have hUconst : Tendsto (fun _ : ℕ => U) atTop (𝓝 U) := tendsto_const_nhds
    have hVconst : Tendsto (fun _ : ℕ => V) atTop (𝓝 V) := tendsto_const_nhds
    have h1 := (hUconst.sub hUk).norm.mul_const ‖V‖
    have h2 := hUk.norm.mul (hVconst.sub hVk).norm
    simpa only [a, sub_self, norm_zero, zero_mul, mul_zero, add_zero] using h1.add h2
  apply tendstoInMeasure_of_uniform_integral_approx f (fun _ => (0 : ℝ)) F
    (fun _ _ => (0 : ℝ)) a ha
  · intro k
    exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro k
    have h := elementary_coordinate_integral_covariation_zero D hij (u k) (v k) t
    rw [hu k, hv k] at h
    exact h
  · intro k n
    exact ((coordinate_covariation_integrable D i j U V t (n + 1)).sub
      (coordinate_covariation_integrable D i j (Uk k) (Vk k) t (n + 1))).norm
  · intro k n
    simpa only [Real.norm_eq_abs] using
      integral_abs_coordinate_covariation_sub_le D i j U (Uk k) V (Vk k) t (Nat.zero_lt_succ n)
  · intro k
    simp
  · intro k
    simp only [sub_zero, norm_zero, integral_zero]
    exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma vectorProcess_quadraticVariation (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt (vectorProcess D U) P t
      (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
  classical
  have hmeas (i : Fin N) (s : ℝ≥0) : AEStronglyMeasurable (coordinateProcess D i (U i) s) P :=
    (coordinateProcess_memLp D i (U i) s).aestronglyMeasurable
  have hQV (i : Fin N) : HasQuadraticVariationInProbabilityAt (coordinateProcess D i (U i)) P t
      (FilteredQuadraticVariation.predictableQuadraticVariation (U i) t) :=
    FilteredQuadraticVariation.quadraticVariation_naturalItoProcessRepresentative
      (D.brownian i) (D.coordinateStronglyMeasurable i) (D.filtered i) (U i) t
  have hsum (S : Finset (Fin N)) : HasQuadraticVariationInProbabilityAt
      (fun s ω => ∑ i ∈ S, coordinateProcess D i (U i) s ω) P t
      (fun ω => ∑ i ∈ S, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change TendstoInMeasure P (fun n => quadraticVariationApprox (fun _ _ => 0) t (n + 1))
        atTop (fun _ => 0)
      have heq : (fun n => quadraticVariationApprox (fun _ (_ : Ω) => (0 : ℝ)) t (n + 1)) =
          (fun _ (_ : Ω) => (0 : ℝ)) := by
        funext n ω
        simp [quadraticVariationApprox]
      rw [heq]
      apply tendstoInMeasure_of_tendsto_ae
      · intro n
        exact aestronglyMeasurable_const
      · exact Eventually.of_forall (fun _ => tendsto_const_nhds)
    | @insert i S hi ih =>
      have hSmeas (s : ℝ≥0) : AEStronglyMeasurable
          (fun ω => ∑ j ∈ S, coordinateProcess D j (U j) s ω) P := by
        convert Finset.aestronglyMeasurable_sum S (fun j _ => hmeas j s) using 1
        funext ω
        rw [Finset.sum_apply]
      have hc (j : Fin N) (hj : j ∈ S) : TendstoInMeasure P
          (fun n => quadraticCovariationApprox (coordinateProcess D i (U i))
            (coordinateProcess D j (U j)) t (n + 1)) atTop (fun _ => 0) := by
        apply coordinate_integral_covariation_zero D _ (U i) (U j) t
        exact fun hij => hi (hij ▸ hj)
      have hCov := tendstoInMeasure_quadraticCovariationApprox_finset_sum S
        (coordinateProcess D i (U i)) (fun j => coordinateProcess D j (U j))
        (fun _ => 1) (fun _ _ => 0) t (hmeas i) (fun j _ => hmeas j) hc
      have hCov' : TendstoInMeasure P (fun n => quadraticCovariationApprox
          (coordinateProcess D i (U i)) (fun s ω => ∑ j ∈ S, coordinateProcess D j (U j) s ω)
          t (n + 1)) atTop (fun _ => 0) := by
        simpa only [one_mul, mul_zero, Finset.sum_const_zero] using hCov
      simpa only [Finset.sum_insert hi, one_pow, one_mul, mul_zero, add_zero] using
        (hQV i).linearCombination ih hCov' (hmeas i) hSmeas 1 1
  exact hsum Finset.univ

lemma vectorProcess_timeRestrict_ae (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (a s : ℝ≥0) :
    vectorProcess D (fun i => FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a (U i)) s
      =ᵐ[P] vectorProcess D U (min s a) := by
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin N,
      coordinateProcess D i (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a (U i)) s ω =
      coordinateProcess D i (U i) (min s a) ω :=
    ae_all_iff.mpr (fun i => FourPapersCommon.FilteredBrownian.naturalItoProcessRepresentative_predictableTimeRestrict_ae
      (D.filtered i).toIsPreBrownianReal (D.coordinateStronglyMeasurable i) (D.filtered i) (U i) s a)
  filter_upwards [hall] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

lemma vectorProcess_stopped_quadraticVariation (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (a t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt (fun s => vectorProcess D U (min s a)) P t
      (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) (min t a) ω) := by
  have hQV := vectorProcess_quadraticVariation D
    (fun i => FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a (U i)) t
  apply hQV.congr (fun s => vectorProcess_timeRestrict_ae D U a s)
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin N,
      FilteredQuadraticVariation.predictableQuadraticVariation
        (FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 a (U i)) t ω =
      FilteredQuadraticVariation.predictableQuadraticVariation (U i) (min t a) ω :=
    ae_all_iff.mpr (fun i => FilteredQuadraticVariation.predictableQuadraticVariation_timeRestrict_ae
      (U i) a t)
  filter_upwards [hall] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

lemma vectorProcess_beforeStop_quadraticVariation (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t a : ℝ≥0) (ha : a ≤ t) :
    TendstoInMeasure P (fun n => quadraticVariationBeforeStopApprox (vectorProcess D U) t (n + 1) a)
      atTop (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) (min t a) ω) := by
  obtain ⟨Y, hmod⟩ := exists_continuousModification_vectorProcess D U
  exact hmod.quadraticVariationBeforeStopApprox_tendstoInMeasure
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable) t a ⟨bot_le, ha⟩
    _ (vectorProcess_stopped_quadraticVariation D U a t)

omit [IsProbabilityMeasure P] [MeasurableSpace Ω] in
lemma beforeStop_min_horizon (X : ℝ≥0 → Ω → ℝ) (t a : ℝ≥0) (n : ℕ) (ω : Ω) :
    quadraticVariationBeforeStopApprox X t n a ω =
      quadraticVariationBeforeStopApprox X t n (min t a) ω := by
  unfold quadraticVariationBeforeStopApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hn : 0 < n := (Nat.zero_lt_succ i).trans_le hi1
  have hend : uniformPartitionTime t n (i + 1) ≤ t :=
    (uniformPartitionTime_mem_Icc_of_le t hn hi1).2
  have heq : (uniformPartitionTime t n (i + 1) ≤ a) =
      (uniformPartitionTime t n (i + 1) ≤ min t a) :=
    propext ⟨fun h => le_min hend h, fun h => h.trans (min_le_right _ _)⟩
  simp only [← heq]

lemma vectorProcess_beforeStop_all (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (t a : ℝ≥0) :
    TendstoInMeasure P (fun n => quadraticVariationBeforeStopApprox (vectorProcess D U) t (n + 1) a)
      atTop (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) (min t a) ω) := by
  have h := vectorProcess_beforeStop_quadraticVariation D U t (min t a) (min_le_left _ _)
  apply h.congr
  · intro n
    exact Eventually.of_forall (fun ω => (beforeStop_min_horizon _ t a (n + 1) ω).symm)
  · simp only [← min_assoc, min_self]
    exact EventuallyEq.rfl

end SphericalAging.VectorQuadraticVariation
