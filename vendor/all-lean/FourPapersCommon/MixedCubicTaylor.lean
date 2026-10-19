module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedFirstVariationRegularity

@[expose] public section

/-! Uniform cubic Taylor control of the genuine mixed first variation.
The scalar covariance jets have compact analytic bounds, and every RSB depth
uses the same normalized Hessian-square Lipschitz constant. The elementary
Taylor proof is adapted from Apache-2.0 Targets.Section4CubicTaylor. -/
noncomputable section
open Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 1000000

private theorem mixed_abs_product_sub_le {a b c d M N L J δ : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (ha : |a| ≤ M) (hd : |d| ≤ N)
    (hac : |a - c| ≤ L * δ) (hbd : |b - d| ≤ J * δ) :
    |a * b - c * d| ≤ (M * J + N * L) * δ := by
  calc
    _ = |a * (b - d) + d * (a - c)| := by congr 1; ring
    _ ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]
    _ ≤ M * (J * δ) + N * (L * δ) := add_le_add
      (mul_le_mul ha hbd (abs_nonneg _) hM) (mul_le_mul hd hac (abs_nonneg _) hN)
    _ = _ := by ring

def mixedCurvatureLipschitz (ξ : AdmissibleEvenMixture) : ℝ :=
  (535 * ξ.jetBound ^ 3 + 3 * ξ.jetBound ^ 2 + 3 * ξ.jetBound) / 2

theorem mixedCurvatureLipschitz_nonneg (ξ : AdmissibleEvenMixture) :
    0 ≤ mixedCurvatureLipschitz ξ := by
  have hK : 0 ≤ ξ.jetBound := zero_le_one.trans ξ.jetBound_spec.1
  dsimp [mixedCurvatureLipschitz]
  positivity

theorem mixedSection4FirstVariationD2_lipschitz (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    {u w : ℝ} (hu : u ∈ Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Icc (s.q (r - 1)) (s.q r)) :
    |mixedSection4FirstVariationD2 ξ s h r u - mixedSection4FirstVariationD2 ξ s h r w| ≤
      mixedCurvatureLipschitz ξ * |u - w| := by
  let K := ξ.jetBound
  let δ := |u - w|
  let Q := mixedSection4Q ξ s h r
  let R := mixedSection4R ξ s h r
  let T := deriv ξ.second
  let S := ξ.second
  have hK : 0 ≤ K := zero_le_one.trans ξ.jetBound_spec.1
  have hu0 : u ∈ Icc (0 : ℝ) 1 := ⟨(s.q_nonneg (by omega)).trans hu.1, hu.2.trans (s.q_le_one (by omega))⟩
  have hw0 : w ∈ Icc (0 : ℝ) 1 := ⟨(s.q_nonneg (by omega)).trans hw.1, hw.2.trans (s.q_le_one (by omega))⟩
  have hSu : |S u| ≤ K := (ξ.abs_second_le_at_one (abs_le.mpr ⟨by linarith [hu0.1], hu0.2⟩)).trans ξ.jetBound_spec.2.1
  have hSw : |S w| ≤ K := (ξ.abs_second_le_at_one (abs_le.mpr ⟨by linarith [hw0.1], hw0.2⟩)).trans ξ.jetBound_spec.2.1
  have hTu : |T u| ≤ K := ξ.jetBound_spec.2.2.1 u hu0
  have hEu : |u - Q u| ≤ 1 := abs_le.mpr ⟨by linarith [(mixedSection4Q_mem ξ s h hr u).2, hu0.1], by linarith [(mixedSection4Q_mem ξ s h hr u).1, hu0.2]⟩
  have hEw : |w - Q w| ≤ 1 := abs_le.mpr ⟨by linarith [(mixedSection4Q_mem ξ s h hr w).2, hw0.1], by linarith [(mixedSection4Q_mem ξ s h hr w).1, hw0.2]⟩
  have hRw : |R w| ≤ 1 := by rw [abs_of_nonneg (mixedSection4R_mem ξ s h hr w).1]; exact (mixedSection4R_mem ξ s h hr w).2
  have hSl : |S u - S w| ≤ K * δ := ξ.second_lipschitz_unit hu0 hw0
  have hTl : |T u - T w| ≤ K * δ := ξ.third_lipschitz_unit hu0 hw0
  have hRl : |R u - R w| ≤ (535 * K) * δ := mixedSection4R_lipschitz ξ s h hr0 hr hu hw
  have hQl : |Q u - Q w| ≤ K * δ := mixedSection4Q_lipschitz ξ s h hr0 hr hu hw
  have hEl : |(u - Q u) - (w - Q w)| ≤ (1 + K) * δ := by
    calc
      _ = |(u - w) - (Q u - Q w)| := by congr 1; ring
      _ ≤ |u - w| + |Q u - Q w| := abs_sub _ _
      _ ≤ δ + K * δ := add_le_add le_rfl hQl
      _ = _ := by ring
  have hA := mixed_abs_product_sub_le hK (by norm_num : (0 : ℝ) ≤ 1) hTu hEw hTl hEl
  have hSS := mixed_abs_product_sub_le hK hK hSu hSw hSl hSl
  have hSSu : |S u * S u| ≤ K ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hSu hSu (abs_nonneg _) hK).trans_eq (by ring)
  have hB := mixed_abs_product_sub_le (sq_nonneg K) (by norm_num : (0 : ℝ) ≤ 1)
    hSSu hRw hSS hRl
  have he : mixedSection4FirstVariationD2 ξ s h r u - mixedSection4FirstVariationD2 ξ s h r w =
      ((T u * (u - Q u) - T w * (w - Q w)) + (S u - S w) -
        (S u * S u * R u - S w * S w * R w)) / 2 := by
    dsimp [mixedSection4FirstVariationD2, T, S, Q, R]
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have H : |(T u * (u - Q u) - T w * (w - Q w)) + (S u - S w) -
      (S u * S u * R u - S w * S w * R w)| ≤
      |T u * (u - Q u) - T w * (w - Q w)| + |S u - S w| +
      |S u * S u * R u - S w * S w * R w| := by
    exact (abs_sub _ _).trans
      (add_le_add (abs_add_le (T u * (u - Q u) - T w * (w - Q w)) (S u - S w)) le_rfl)
  change _ ≤ _ at hA hB
  dsimp [mixedCurvatureLipschitz]
  change _ ≤ (535 * K ^ 3 + 3 * K ^ 2 + 3 * K) / 2 * δ
  nlinarith only [H, hA, hB, hSl]

theorem mixed_cubic_remainder_of_second_lipschitz
    {f d d2 : ℝ → ℝ} {l r K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ x ∈ Set.Icc l r, HasDerivWithinAt f (d x) (Set.Icc l r) x)
    (hd : ∀ x ∈ Set.Icc l r, HasDerivWithinAt d (d2 x) (Set.Icc l r) x)
    (hLip : ∀ x ∈ Set.Icc l r, ∀ y ∈ Set.Icc l r, |d2 x - d2 y| ≤ K * |x - y|)
    {a b : ℝ} (ha : a ∈ Set.Icc l r) (hb : b ∈ Set.Icc l r) :
    |f a - f b - d b * (a - b) - d2 b / 2 * (a - b) ^ 2| ≤ K * |a - b| ^ 3 := by
  have hsub : Set.uIcc b a ⊆ Set.Icc l r := Set.uIcc_subset_Icc hb ha
  let E1 := fun x => d x - d b - d2 b * (x - b)
  have hE1 (x : ℝ) (hx : x ∈ Set.uIcc b a) :
      HasDerivWithinAt E1 (d2 x - d2 b) (Set.uIcc b a) x := by
    simpa only [E1, mul_one, Pi.sub_def, id_eq] using! ((hd x (hsub hx)).sub_const (d b)).sub
      ((((hasDerivAt_id x).sub_const b).const_mul (d2 b)).hasDerivWithinAt) |>.mono hsub
  have hD (x : ℝ) (hx : x ∈ Set.uIcc b a) : |d2 x - d2 b| ≤ K * |a - b| :=
    (hLip x (hsub hx) b hb).trans
      (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx) hK)
  have hE1bound (x : ℝ) (hx : x ∈ Set.uIcc b a) : |E1 x| ≤ K * |a - b| ^ 2 := by
    have H := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le hE1
      (fun y hy => by simpa only [Real.norm_eq_abs] using hD y hy)
      Set.left_mem_uIcc hx
    have H' : |E1 x| ≤ (K * |a - b|) * |x - b| := by
      simpa only [E1, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] using H
    calc
      |E1 x| ≤ (K * |a - b|) * |x - b| := H'
      _ ≤ (K * |a - b|) * |a - b| :=
        mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hx)
          (mul_nonneg hK (abs_nonneg _))
      _ = K * |a - b| ^ 2 := by ring
  let E0 := fun x => f x - f b - d b * (x - b) - d2 b / 2 * (x - b) ^ 2
  have hE0 (x : ℝ) (hx : x ∈ Set.uIcc b a) :
      HasDerivWithinAt E0 (E1 x) (Set.uIcc b a) x := by
    have H := (((hf x (hsub hx)).sub_const (f b)).sub
      ((((hasDerivAt_id x).sub_const b).const_mul (d b)).hasDerivWithinAt)).sub
      (((((hasDerivAt_id x).sub_const b).pow 2).const_mul (d2 b / 2)).hasDerivWithinAt)
    convert! H.mono hsub using 1
    simp only [E1, id_eq]
    ring
  have H := (convex_uIcc b a).norm_image_sub_le_of_norm_hasDerivWithin_le hE0
    (fun x hx => by simpa only [Real.norm_eq_abs] using hE1bound x hx)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa only [E0, sub_self, mul_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    Real.norm_eq_abs, pow_succ, mul_assoc] using H


theorem mixedSection4FirstVariation_cubic_taylor (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1)
    (hm : s.m (r - 1) < 1) {u w : ℝ}
    (hu : u ∈ Icc (s.q (r - 1)) (s.q r)) (hw : w ∈ Icc (s.q (r - 1)) (s.q r)) :
    |mixedSection4FirstVariation ξ s h r u - mixedSection4FirstVariation ξ s h r w -
      mixedSection4FirstVariationD ξ s h r w * (u - w) -
      mixedSection4FirstVariationD2 ξ s h r w / 2 * (u - w) ^ 2| ≤
      mixedCurvatureLipschitz ξ * |u - w| ^ 3 :=
  mixed_cubic_remainder_of_second_lipschitz (mixedCurvatureLipschitz_nonneg ξ)
    (fun _x hx => hasDerivWithinAt_mixedSection4FirstVariation ξ s h hr0 hr hm hx)
    (fun _x hx => hasDerivWithinAt_mixedSection4FirstVariationD ξ s h hr0 hr hx)
    (fun _x hx _y hy => mixedSection4FirstVariationD2_lipschitz ξ s h hr0 hr hx hy) hu hw

end FourPapersCommon
