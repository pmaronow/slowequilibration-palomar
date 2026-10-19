-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianHermiteDerivative
public import Lemmas.SpinGlass.gaussian_concentration

/-! Coordinate integration by parts for the normalized product Hermites.
The exponential envelopes below are hypotheses about genuine smooth
functions, rather than hypotheses asserting the desired coefficient identity. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianHermiteDerivative

open MeasureTheory ProbabilityTheory Polynomial OAI.MinUncut.GaussianHermite
open scoped BigOperators NNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinatePartial (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

lemma coordinatePartial_mul (f g : (ι → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : ι) (x : ι → ℝ) :
    coordinatePartial (fun y => f y * g y) i x =
      coordinatePartial f i x * g x + f x * coordinatePartial g i x := by
  unfold coordinatePartial
  have hh := ((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv
  simp only [Pi.mul_def] at hh
  rw [hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma coordinatePartial_add (f g : (ι → ℝ) → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : ι) (x : ι → ℝ) :
    coordinatePartial (fun y => f y + g y) i x =
      coordinatePartial f i x + coordinatePartial g i x := by
  unfold coordinatePartial
  have hh := ((hf x).hasFDerivAt.add (hg x).hasFDerivAt).fderiv
  simp only [Pi.add_def] at hh
  rw [hh]
  rfl

/-- A concrete growth condition, preserved by polynomial tests. -/
structure ExponentialFirstJet (f : (ι → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ 1 f
  bound : ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧
    (∀ x, |f x| ≤ C * Real.exp (c * ∑ j, |x j|)) ∧
    (∀ x i, |coordinatePartial f i x| ≤ C * Real.exp (c * ∑ j, |x j|))

lemma sum_abs_nonneg (x : ι → ℝ) : 0 ≤ ∑ j, |x j| :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem ExponentialFirstJet.const (r : ℝ) :
    ExponentialFirstJet (fun _ : ι → ℝ => r) := by
  refine ⟨contDiff_const, |r|, 0, abs_nonneg r, le_rfl, ?_, ?_⟩
  · intro x
    simp
  · intro x i
    simp [coordinatePartial]

theorem ExponentialFirstJet.apply (i : ι) :
    ExponentialFirstJet (fun x : ι → ℝ => x i) := by
  refine ⟨contDiff_apply ℝ ℝ i, 1, 1, by norm_num, by norm_num, ?_, ?_⟩
  · intro x
    have hx : |x i| ≤ ∑ j, |x j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    simp only [one_mul]
    linarith [Real.add_one_le_exp (∑ j, |x j|)]
  · intro x j
    have he : 1 ≤ Real.exp (∑ k, |x k|) := Real.one_le_exp (sum_abs_nonneg x)
    rw [coordinatePartial, (hasFDerivAt_apply i x).fderiv]
    simp only [ContinuousLinearMap.proj_apply, one_mul]
    by_cases h : i = j
    · subst j
      simpa using he
    · simp [Pi.single_eq_of_ne h, Real.exp_nonneg]

theorem ExponentialFirstJet.add {f g : (ι → ℝ) → ℝ}
    (hf : ExponentialFirstJet f) (hg : ExponentialFirstJet g) :
    ExponentialFirstJet (fun x => f x + g x) := by
  obtain ⟨C, c, hC, hc, hfb, hfdb⟩ := hf.bound
  obtain ⟨D, d, hD, hd, hgb, hgdb⟩ := hg.bound
  have hec (x : ι → ℝ) : Real.exp (c * ∑ j, |x j|) ≤
      Real.exp ((c + d) * ∑ j, |x j|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sum_abs_nonneg x]
  have hed (x : ι → ℝ) : Real.exp (d * ∑ j, |x j|) ≤
      Real.exp ((c + d) * ∑ j, |x j|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sum_abs_nonneg x]
  refine ⟨hf.smooth.add hg.smooth, C + D, c + d, by positivity, by positivity, ?_, ?_⟩
  · intro x
    exact (abs_add_le _ _).trans (by
      nlinarith [hfb x, hgb x, mul_le_mul_of_nonneg_left (hec x) hC,
        mul_le_mul_of_nonneg_left (hed x) hD])
  · intro x i
    rw [coordinatePartial_add f g (hf.smooth.differentiable (by norm_num))
      (hg.smooth.differentiable (by norm_num))]
    exact (abs_add_le _ _).trans (by
      nlinarith [hfdb x i, hgdb x i, mul_le_mul_of_nonneg_left (hec x) hC,
        mul_le_mul_of_nonneg_left (hed x) hD])

theorem ExponentialFirstJet.mul {f g : (ι → ℝ) → ℝ}
    (hf : ExponentialFirstJet f) (hg : ExponentialFirstJet g) :
    ExponentialFirstJet (fun x => f x * g x) := by
  obtain ⟨C, c, hC, hc, hfb, hfdb⟩ := hf.bound
  obtain ⟨D, d, hD, hd, hgb, hgdb⟩ := hg.bound
  have he (x : ι → ℝ) :
      (C * Real.exp (c * ∑ j, |x j|)) * (D * Real.exp (d * ∑ j, |x j|)) =
        (C * D) * Real.exp ((c + d) * ∑ j, |x j|) := by
    rw [add_mul, Real.exp_add]
    ring
  refine ⟨hf.smooth.mul hg.smooth, 2 * (C * D), c + d,
    by positivity, by positivity, ?_, ?_⟩
  · intro x
    rw [abs_mul]
    have hb := mul_le_mul (hfb x) (hgb x) (abs_nonneg _) (by positivity)
    rw [he] at hb
    nlinarith [show 0 ≤ C * D * Real.exp ((c + d) * ∑ j, |x j|) by positivity]
  · intro x i
    rw [coordinatePartial_mul f g (hf.smooth.differentiable (by norm_num))
      (hg.smooth.differentiable (by norm_num))]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    have hb := mul_le_mul (hfdb x i) (hgb x) (abs_nonneg _) (by positivity)
    have hb' := mul_le_mul (hfb x) (hgdb x i) (abs_nonneg _) (by positivity)
    rw [he] at hb hb'
    linarith

theorem ExponentialFirstJet.pow {f : (ι → ℝ) → ℝ}
    (hf : ExponentialFirstJet f) (n : ℕ) :
    ExponentialFirstJet (fun x => (f x) ^ n) := by
  induction n with
  | zero => simpa using ExponentialFirstJet.const (ι := ι) 1
  | succ n hn => simpa only [pow_succ] using hn.mul hf

theorem ExponentialFirstJet.polynomial_eval (p : ℝ[X]) (i : ι) :
    ExponentialFirstJet (fun x : ι → ℝ => p.eval (x i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n r =>
    simpa only [Polynomial.eval_monomial] using
      (ExponentialFirstJet.const r).mul ((ExponentialFirstJet.apply i).pow n)

theorem ExponentialFirstJet.finset_prod {κ : Type*} (s : Finset κ)
    (f : κ → (ι → ℝ) → ℝ) (hf : ∀ k ∈ s, ExponentialFirstJet (f k)) :
    ExponentialFirstJet (fun x => ∏ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ExponentialFirstJet.const (ι := ι) 1
  | @insert k s hks ih =>
    have hk := hf k (Finset.mem_insert_self k s)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hks] using hk.mul hs

theorem ExponentialFirstJet.psi (a : ι → ℕ) : ExponentialFirstJet (psi a) := by
  apply ExponentialFirstJet.finset_prod
  intro i _
  have hp := ExponentialFirstJet.polynomial_eval (hePoly (a i)) i
  have hc := ExponentialFirstJet.const (ι := ι) (Real.sqrt ((a i).factorial : ℝ))⁻¹
  simpa only [hePoly_eval, H, div_eq_mul_inv] using hp.mul hc

/-- Linear value growth and bounded coordinate derivatives suffice for all
the Hermite integration-by-parts tests. -/
theorem ExponentialFirstJet.of_linear_bounds
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ C * (1 + ∑ j, |x j|))
    (hdb : ∀ x i, |coordinatePartial f i x| ≤ C) :
    ExponentialFirstJet f := by
  refine ⟨hf, C, 1, hC, by norm_num, ?_, ?_⟩
  · intro x
    simp only [one_mul]
    exact (hb x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using Real.add_one_le_exp (∑ j, |x j|)) hC)
  · intro x i
    simp only [one_mul]
    exact (hdb x i).trans (le_mul_of_one_le_right hC
      (Real.one_le_exp (sum_abs_nonneg x)))

theorem ExponentialFirstJet.of_lipschitz
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hlip : LipschitzWith L f) : ExponentialFirstJet f := by
  let C : ℝ := (L : ℝ) + |f 0|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ExponentialFirstJet.of_linear_bounds f hf C hC
  · intro x
    have hnorm : ‖x‖ ≤ ∑ j, |x j| := by
      apply (pi_norm_le_iff_of_nonneg (sum_abs_nonneg x)).mpr
      intro j
      simpa only [Real.norm_eq_abs] using
        (Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ j))
    have hl := hlip.norm_sub_le x 0
    rw [sub_zero, Real.norm_eq_abs] at hl
    have ht : |f x| ≤ |f x - f 0| + |f 0| := by
      simpa only [sub_add_cancel] using abs_add_le (f x - f 0) (f 0)
    have hs := sum_abs_nonneg x
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hnorm L.coe_nonneg, abs_nonneg (f 0)]
  · intro x i
    have hd : |coordinatePartial f i x| ≤ (L : ℝ) := by
      calc
        _ = ‖fderiv ℝ f x (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ f x‖ * ‖(Pi.single i 1 : ι → ℝ)‖ :=
          (fderiv ℝ f x).le_opNorm _
        _ = ‖fderiv ℝ f x‖ := by simp only [Pi.norm_single, norm_one, mul_one]
        _ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hlip
    exact hd.trans (le_add_of_nonneg_right (abs_nonneg (f 0)))

lemma H_contDiff (n : ℕ) : ContDiff ℝ 1 (H n) := by
  convert (Polynomial.contDiff_aeval (hermite n) 1).div_const
    (Real.sqrt (n.factorial : ℝ)) using 1
  rfl

lemma H_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (H n)
      ((hePoly n).derivative.eval x / Real.sqrt (n.factorial : ℝ)) x := by
  convert ((hePoly n).hasDerivAt x).div_const (Real.sqrt (n.factorial : ℝ)) using 1
  funext y
  simp only [H, hePoly_eval]

lemma H_derivative_adjoint (n : ℕ) (x : ℝ) :
    (hePoly n).derivative.eval x / Real.sqrt (n.factorial : ℝ) =
      x * H n x - Real.sqrt (n + 1 : ℝ) * H (n + 1) x := by
  have hh : he (n + 1) x = x * he n x - (hePoly n).derivative.eval x := by
    rw [← hePoly_eval, hePoly_succ]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, hePoly_eval]
  rw [H, H, sqrt_factorial_succ]
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
  have ht : Real.sqrt (n.factorial : ℝ) ≠ 0 := ne_of_gt (sqrt_factorial_pos n)
  field_simp
  nlinarith

lemma psi_contDiff (a : ι → ℕ) : ContDiff ℝ 1 (psi a) := by
  apply contDiff_prod
  intro i _
  exact (H_contDiff (a i)).comp (contDiff_apply ℝ ℝ i)

lemma coordinatePartial_psi (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    coordinatePartial (psi a) i x =
      x i * psi a x - Real.sqrt (a i + 1 : ℝ) * psi (bump i a) x := by
  have hd (j : ι) :
      HasFDerivAt (𝕜 := ℝ) (fun y : ι → ℝ => H (a j) (y j))
        (((hePoly (a j)).derivative.eval (x j) / Real.sqrt ((a j).factorial : ℝ)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x :=
    by
      have hp : HasFDerivAt (𝕜 := ℝ) (fun y : ι → ℝ => y j)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x :=
        hasFDerivAt_apply (𝕜 := ℝ) j x
      simpa only [Function.comp_def] using
        (H_hasDerivAt (a j) (x j)).comp_hasFDerivAt x hp
  have hh := (HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd j)).fderiv
  change (fderiv ℝ (fun y : ι → ℝ => ∏ j, H (a j) (y j)) x) (Pi.single i 1) = _
  rw [hh]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hsum : (∑ j : ι,
      (∏ k ∈ Finset.univ.erase j, H (a k) (x k)) *
        (((hePoly (a j)).derivative.eval (x j) / Real.sqrt ((a j).factorial : ℝ)) *
          (Pi.single i 1 : ι → ℝ) j)) =
      (∏ k ∈ Finset.univ.erase i, H (a k) (x k)) *
        ((hePoly (a i)).derivative.eval (x i) / Real.sqrt ((a i).factorial : ℝ)) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  rw [hsum, H_derivative_adjoint]
  have hpsi : psi a x = H (a i) (x i) * ∏ j ∈ Finset.univ.erase i, H (a j) (x j) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hbump : psi (bump i a) x =
      H (a i + 1) (x i) * ∏ j ∈ Finset.univ.erase i, H (a j) (x j) := by
    rw [psi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [bump, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [bump, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hpsi, hbump]
  ring

/-- Smooth Gaussian integration by parts gives the raising identity. The
envelopes are for the Hermite test times the function; polynomial growth
of the Hermite factors makes them applicable to functions with bounded
first derivatives. -/
theorem coeff_coordinatePartial_of_exponential_bounds
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : MemLp f 2 (γpi ι)) (i : ι)
    (hdf2 : MemLp (coordinatePartial f i) 2 (γpi ι)) (a : ι → ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hb : ∀ x, |psi a x * f x| ≤ C * Real.exp (c * ∑ j, |x j|))
    (hdb : ∀ x j, |coordinatePartial (fun y => psi a y * f y) j x| ≤
      C * Real.exp (c * ∑ k, |x k|)) :
    coeff (coordinatePartial f i) a =
      Real.sqrt (a i + 1 : ℝ) * coeff f (bump i a) := by
  have hh : ContDiff ℝ 1 (fun x => psi a x * f x) := (psi_contDiff a).mul hf
  have hstein := SYK.pi_gaussian_stein_coord (fun x => psi a x * f x) i
    hh C c hc hC hb hdb
  change (∫ x : ι → ℝ, x i * (psi a x * f x) ∂γpi ι) =
    ∫ x, coordinatePartial (fun y => psi a y * f y) i x ∂γpi ι at hstein
  have hd (x : ι → ℝ) :
      coordinatePartial (fun y => psi a y * f y) i x =
        (x i * psi a x - Real.sqrt (a i + 1 : ℝ) * psi (bump i a) x) * f x +
          psi a x * coordinatePartial f i x := by
    rw [coordinatePartial_mul _ _ ((psi_contDiff a).differentiable (by norm_num))
      (hf.differentiable (by norm_num)), coordinatePartial_psi]
  have hX : Integrable (fun x : ι → ℝ => x i * psi a x * f x) (γpi ι) := by
    apply Integrable.mono'
      ((SYK.integrable_abs_coord_mul_exp_c_sum_abs_pi c i).const_mul C)
    · exact (((continuous_apply i).mul (psi_contDiff a).continuous).mul
        hf.continuous).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, show x i * psi a x * f x = x i * (psi a x * f x) by ring,
        abs_mul]
      nlinarith [hb x, abs_nonneg (x i)]
  have hB : Integrable (fun x => psi (bump i a) x * f x) (γpi ι) :=
    (memLp_psi (bump i a)).integrable_mul hf2
  have hD : Integrable (fun x => psi a x * coordinatePartial f i x) (γpi ι) :=
    (memLp_psi a).integrable_mul hdf2
  have heq : (fun x : ι → ℝ => coordinatePartial (fun y => psi a y * f y) i x) =
      fun x => (x i * psi a x * f x -
        Real.sqrt (a i + 1 : ℝ) * (psi (bump i a) x * f x)) +
          psi a x * coordinatePartial f i x := by
    funext x
    change coordinatePartial (fun y => psi a y * f y) i x = _
    rw [hd]
    ring
  have hiAdd := integral_add (hX.sub (hB.const_mul (Real.sqrt (a i + 1 : ℝ)))) hD
  simp only [Pi.sub_apply] at hiAdd
  rw [heq, hiAdd, integral_sub hX (hB.const_mul _), integral_const_mul] at hstein
  have hleft : (∫ x : ι → ℝ, x i * (psi a x * f x) ∂γpi ι) =
      ∫ x, x i * psi a x * f x ∂γpi ι := by
    congr 1
    funext x
    ring
  change (∫ x : ι → ℝ, x i * (psi a x * f x) ∂γpi ι) = _ at hstein
  rw [hleft] at hstein
  unfold OAI.MinUncut.GaussianHermite.coeff
  linarith

/-- Integration by parts against every normalized Hermite polynomial, with
the test-function envelopes discharged by polynomial closure. -/
theorem coeff_coordinatePartial (f : (ι → ℝ) → ℝ)
    (hf : ExponentialFirstJet f) (hf2 : MemLp f 2 (γpi ι))
    (i : ι) (hdf2 : MemLp (coordinatePartial f i) 2 (γpi ι)) (a : ι → ℕ) :
    coeff (coordinatePartial f i) a =
      Real.sqrt (a i + 1 : ℝ) * coeff f (bump i a) := by
  obtain ⟨C, c, hC, hc, hb, hdb⟩ := ((ExponentialFirstJet.psi a).mul hf).bound
  exact coeff_coordinatePartial_of_exponential_bounds f hf.smooth hf2 i hdf2 a
    C c hC hc hb hdb

/-- The actual squared coordinate derivatives control every finite
weighted Hermite sum. No Hermite coefficient identity is an extra premise. -/
theorem finite_weighted_energy_le (f : (ι → ℝ) → ℝ)
    (hf : ExponentialFirstJet f) (hf2 : MemLp f 2 (γpi ι))
    (hdf2 : ∀ i, MemLp (coordinatePartial f i) 2 (γpi ι))
    (s : Finset (ι → ℕ)) :
    ∑ a ∈ s, (degree a : ℝ) * (coeff f a) ^ 2 ≤
      ∑ i, ∫ x, (coordinatePartial f i x) ^ 2 ∂γpi ι := by
  exact finite_weighted_energy_le_of_coeff_identity f (coordinatePartial f) hdf2
    (fun i a => coeff_coordinatePartial f hf hf2 i (hdf2 i) a) s

end SlowEquilibration.GaussianHermiteDerivative
