-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet
public import SlowEquilibration.GaussianNormMean

@[expose] public section

namespace SlowEquilibration.PureTensorJetFeatures

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual coefficient tensor of an ordered multilinear evaluation. -/
def tensorFeature {N p : ℕ} (v : Fin p → Vector N) :
    EuclideanSpace ℝ (TensorIndex N p) :=
  WithLp.toLp 2 (fun I => ∏ k : Fin p, v k (I k))

@[simp] theorem tensorFeature_apply {N p : ℕ} (v : Fin p → Vector N)
    (I : TensorIndex N p) : tensorFeature v I = ∏ k : Fin p, v k (I k) := rfl

theorem tensorFeature_inner {N p : ℕ} (v w : Fin p → Vector N) :
    inner ℝ (tensorFeature v) (tensorFeature w) =
      ∏ k : Fin p, inner ℝ (v k) (w k) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, tensorFeature_apply,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k i => w k i * v k i)).symm

theorem tensorFeature_continuous (N p : ℕ) :
    Continuous (tensorFeature (N := N) (p := p)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro I
  exact continuous_finsetProd _ (fun k _ =>
    by fun_prop)

theorem one_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, |a i| ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ha' : ∀ k ∈ s, |a k| ≤ 1 := fun k hk => ha k (Finset.mem_insert_of_mem hk)
    have hi' : a i ≤ 1 := (le_abs_self _).trans (ha i (Finset.mem_insert_self _ _))
    have hp : (∏ k ∈ s, a k) ≤ 1 := by
      apply (le_abs_self _).trans
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun k _ => abs_nonneg _) ha'
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hmul := mul_nonneg (sub_nonneg.mpr hi') (sub_nonneg.mpr hp)
    have h := ih ha'
    nlinarith

theorem tensorFeature_norm_sq_of_unit {N p : ℕ} (v : Fin p → Vector N)
    (hv : ∀ k, ‖v k‖ = 1) : ‖tensorFeature v‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, tensorFeature_inner]
  simp [real_inner_self_eq_norm_sq, hv]

/-- The product tensor has the square-root increment metric on unit factors. -/
theorem tensorFeature_increment_sq_le {N p : ℕ} (v w : Fin p → Vector N)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ k, ‖w k‖ = 1) :
    ‖tensorFeature v - tensorFeature w‖ ^ 2 ≤ ∑ k : Fin p, ‖v k - w k‖ ^ 2 := by
  have hinner (k : Fin p) : |inner ℝ (v k) (w k)| ≤ 1 := by
    simpa [hv, hw] using abs_real_inner_le_norm (v k) (w k)
  have h := one_sub_prod_le_sum Finset.univ (fun k => inner ℝ (v k) (w k))
    (fun k _ => hinner k)
  rw [norm_sub_sq_real, tensorFeature_norm_sq_of_unit v hv,
    tensorFeature_norm_sq_of_unit w hw, tensorFeature_inner]
  have he : (∑ k : Fin p, ‖v k - w k‖ ^ 2) =
      2 * ∑ k : Fin p, (1 - inner ℝ (v k) (w k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [norm_sub_sq_real, hv, hw]
    ring
  rw [he]
  linarith

/-- Flatten the finitely many Euclidean direction blocks without changing their
Hilbert direct-sum norm. -/
def blockFeature {N q : ℕ} (v : Fin q → Vector N) :
    EuclideanSpace ℝ (Fin q × Fin N) :=
  WithLp.toLp 2 (fun ki => v ki.1 ki.2)

@[simp] theorem blockFeature_apply {N q : ℕ} (v : Fin q → Vector N)
    (ki : Fin q × Fin N) : blockFeature v ki = v ki.1 ki.2 := rfl

theorem blockFeature_norm_sq {N q : ℕ} (v : Fin q → Vector N) :
    ‖blockFeature v‖ ^ 2 = ∑ k : Fin q, ‖v k‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, blockFeature_apply]

theorem blockFeature_sub {N q : ℕ} (v w : Fin q → Vector N) :
    blockFeature v - blockFeature w = blockFeature (v - w) := rfl

theorem blockFeature_continuous (N q : ℕ) :
    Continuous (blockFeature (N := N) (q := q)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ki
  fun_prop

/-- A repeated-factor coefficient tensor only pays the square root of its degree,
independently of the number of tensor coordinates. -/
theorem repeated_tensorFeature_increment_le {N p q : ℕ} (t : Fin p → Fin q)
    (v w : Fin q → Vector N) (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ k, ‖w k‖ = 1) :
    ‖tensorFeature (v ∘ t) - tensorFeature (w ∘ t)‖ ≤
      Real.sqrt p * ‖blockFeature v - blockFeature w‖ := by
  have h := tensorFeature_increment_sq_le (v ∘ t) (w ∘ t)
    (fun k => hv (t k)) (fun k => hw (t k))
  have hsum : (∑ k : Fin p, ‖v (t k) - w (t k)‖ ^ 2) ≤
      (p : ℝ) * ∑ k : Fin q, ‖v k - w k‖ ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin p, ∑ k : Fin q, ‖v k - w k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        exact Finset.single_le_sum (fun i _ => sq_nonneg (‖v i - w i‖)) (Finset.mem_univ (t k))
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p), blockFeature_sub, blockFeature_norm_sq]
  exact h.trans hsum

/-- The slot occupied by each derivative direction in an ordered insertion. -/
def insertionSlot {p j : ℕ} (e : Fin j ↪ Fin p) (k : Fin p) : Fin (j + 1) :=
  if h : k ∈ Set.range e then (e.toEquivRange.symm ⟨k, h⟩).succ else 0

/-- The exact unnormalized derivative coefficient, summed over all ordered
injections of the derivative directions into the original tensor slots. -/
def insertionFeature {N p j : ℕ} (v : Fin (j + 1) → Vector N) :
    EuclideanSpace ℝ (TensorIndex N p) :=
  ∑ e : Fin j ↪ Fin p, tensorFeature (v ∘ insertionSlot e)

theorem insertionFeature_continuous (N p j : ℕ) :
    Continuous (insertionFeature (N := N) (p := p) (j := j)) := by
  apply continuous_finsetSum
  intro e _
  apply (tensorFeature_continuous N p).comp
  exact continuous_pi (fun k => continuous_apply (insertionSlot e k))

theorem insertionFeature_increment_le {N p j : ℕ} (v w : Fin (j + 1) → Vector N)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ k, ‖w k‖ = 1) :
    ‖insertionFeature (p := p) v - insertionFeature (p := p) w‖ ≤
      (p : ℝ) ^ j * Real.sqrt p * ‖blockFeature v - blockFeature w‖ := by
  classical
  unfold insertionFeature
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e : Fin j ↪ Fin p,
        ‖tensorFeature (v ∘ insertionSlot e) - tensorFeature (w ∘ insertionSlot e)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _e : Fin j ↪ Fin p, Real.sqrt p * ‖blockFeature v - blockFeature w‖ := by
      exact Finset.sum_le_sum (fun e _ => repeated_tensorFeature_increment_le _ v w hv hw)
    _ = (Nat.descFactorial p j : ℝ) * Real.sqrt p * ‖blockFeature v - blockFeature w‖ := by
      simp [mul_assoc]
    _ ≤ _ := by
      gcongr
      exact_mod_cast Nat.descFactorial_le_pow p j

theorem insertionFeature_norm_le {N p j : ℕ} (v : Fin (j + 1) → Vector N)
    (hv : ∀ k, ‖v k‖ = 1) : ‖insertionFeature (p := p) v‖ ≤ (p : ℝ) ^ j := by
  classical
  unfold insertionFeature
  calc
    _ ≤ ∑ e : Fin j ↪ Fin p, ‖tensorFeature (v ∘ insertionSlot e)‖ := norm_sum_le _ _
    _ = (Nat.descFactorial p j : ℝ) := by
      have he (e : Fin j ↪ Fin p) : ‖tensorFeature (v ∘ insertionSlot e)‖ = 1 := by
        have h := tensorFeature_norm_sq_of_unit (v ∘ insertionSlot e) (fun k => hv _)
        nlinarith [norm_nonneg (tensorFeature (v ∘ insertionSlot e))]
      simp [he]
    _ ≤ _ := by exact_mod_cast Nat.descFactorial_le_pow p j

theorem diagonal_iteratedFDeriv_eq_sum {N p j : ℕ}
    (f : SphericalAging.GaussianLandscape.TensorForm N p) (x : Vector N)
    (a : Fin j → Vector N) :
    iteratedFDeriv ℝ j (fun y => f (fun _ => y)) x a =
      ∑ e : Fin j ↪ Fin p, f (Fin.cons x a ∘ insertionSlot e) := by
  classical
  let D := SphericalAging.LandscapeDerivatives.diagonalL N p
  have he : (fun y : Vector N => f (fun _ => y)) = f ∘ D := rfl
  rw [he, D.iteratedFDeriv_comp_right (f.contDiff (n := ⊤)) x (by simp),
    f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  funext k
  by_cases hk : k ∈ Set.range e
  · simp only [Function.comp_def, insertionSlot, dif_pos hk, Fin.cons_succ, D,
      SphericalAging.LandscapeDerivatives.diagonalL, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.id_apply]
    obtain ⟨i, rfl⟩ := hk
    simp
  · simp [Function.comp_def, insertionSlot, hk, D,
      SphericalAging.LandscapeDerivatives.diagonalL]

/-- Literal equality with the iterated Fréchet derivative of the original
Hamiltonian; no auxiliary Gaussian field is substituted. -/
theorem Hamiltonian_iteratedFDeriv_eq_inner {N p j : ℕ} (J : Disorder N p)
    (x : Vector N) (a : Fin j → Vector N) :
    iteratedFDeriv ℝ j (Hamiltonian N p J) x a = normalization N p *
      inner ℝ (insertionFeature (Fin.cons x a)) (WithLp.toLp 2 J) := by
  classical
  have hc : ContDiff ℝ j (fun y : Vector N =>
      SphericalAging.GaussianLandscape.tensorForm N p J (fun _ => y)) :=
    (SphericalAging.GaussianLandscape.tensorForm N p J).contDiff.comp
      (SphericalAging.LandscapeDerivatives.diagonalL N p).contDiff
  have he : Hamiltonian N p J = fun y : Vector N => normalization N p •
      SphericalAging.GaussianLandscape.tensorForm N p J (fun _ => y) := by
    funext y
    exact SphericalAging.LandscapeDerivatives.Hamiltonian_eq_diagonal J y
  rw [he, iteratedFDeriv_const_smul_apply' hc.contDiffAt,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, diagonal_iteratedFDeriv_eq_sum]
  unfold insertionFeature
  rw [sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [SphericalAging.GaussianLandscape.tensorForm_apply]
  simp [PiLp.inner_apply, RCLike.inner_apply, tensorFeature_apply]

theorem tensorFeature_insertion_cons_smul {N p j : ℕ} (e : Fin j ↪ Fin p)
    (r : ℝ) (x : Vector N) (a : Fin j → Vector N) :
    tensorFeature (Fin.cons (r • x) a ∘ insertionSlot e) =
      r ^ (p - j) • tensorFeature (Fin.cons x a ∘ insertionSlot e) := by
  classical
  ext I
  simp only [tensorFeature_apply, PiLp.smul_apply, smul_eq_mul]
  have hfactor (k : Fin p) : ((Fin.cons (r • x) a : Fin (j + 1) → Vector N) (insertionSlot e k)) (I k) =
      (if k ∈ Set.range e then 1 else r) * ((Fin.cons x a : Fin (j + 1) → Vector N) (insertionSlot e k)) (I k) := by
    by_cases hk : k ∈ Set.range e <;> simp [insertionSlot, hk]
  simp_rw [Function.comp_apply, hfactor]
  rw [Finset.prod_mul_distrib]
  congr 1
  have hcRange : Fintype.card {k : Fin p // k ∈ Set.range e} = j :=
    (Fintype.card_congr e.toEquivRange.symm).trans (Fintype.card_fin j)
  have hc : Fintype.card {k : Fin p // k ∉ Set.range e} = p - j := by
    rw [Fintype.card_subtype_compl, hcRange, Fintype.card_fin]
  rw [← hc]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k : Fin p => k ∈ Set.range e)
    (fun k : Fin p => if k ∈ Set.range e then (1 : ℝ) else r)]
  conv_lhs =>
    arg 1
    arg 2
    ext k
    rw [if_pos k.property]
  conv_lhs =>
    arg 2
    arg 2
    ext k
    rw [if_neg k.property]
  simp

theorem insertionFeature_cons_smul {N p j : ℕ} (r : ℝ) (x : Vector N)
    (a : Fin j → Vector N) :
    insertionFeature (p := p) (Fin.cons (r • x) a) =
      r ^ (p - j) • insertionFeature (p := p) (Fin.cons x a) := by
  classical
  simp only [insertionFeature, tensorFeature_insertion_cons_smul, Finset.smul_sum]

end
end SlowEquilibration.PureTensorJetFeatures
