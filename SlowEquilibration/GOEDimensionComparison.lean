-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalPrefactors

/-! # Genuine bounded changes of physical GOE dimension

The finite-dimensional logarithmic exponent has a true uniformly bounded
dimension derivative at fixed codimension. Actual determinant means therefore
remain comparable under the fixed dimension changes used by spherical Kac--Rice.
-/

@[expose] public section

namespace SlowEquilibration.GOEDimensionComparison

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open GOEScaling GOERawMoments GOEPrefactors GOEPhysicalPotential GOEPhysicalPrefactors
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def scaledProfile (b k q : ℝ) : ℝ :=
  q * (Real.log (Real.sqrt (b * q)) + SemicirclePotential.potential (k / Real.sqrt (b * q)))

def dimensionSlope (b k q : ℝ) : ℝ :=
  Real.log (Real.sqrt (b * q)) + SemicirclePotential.potential (k / Real.sqrt (b * q)) +
    (1 - (k / Real.sqrt (b * q)) * SemicirclePotential.resolvent (k / Real.sqrt (b * q))) / 2

lemma scaledProfile_hasDerivAt {b k q : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hz : 2 < k / Real.sqrt (b * q)) :
    HasDerivAt (scaledProfile b k) (dimensionSlope b k q) q := by
  let a := Real.sqrt (b * q)
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hb hq)
  have hsquare : a ^ 2 = b * q := Real.sq_sqrt (mul_pos hb hq).le
  have hsqrt : HasDerivAt (fun v => Real.sqrt (b * v)) (b / (2 * a)) q := by
    simpa only [id_eq, mul_one, a] using ((hasDerivAt_id q).const_mul b).sqrt (mul_pos hb hq).ne'
  have hlog : HasDerivAt (fun v => Real.log (Real.sqrt (b * v))) (1 / (2 * q)) q := by
    convert hsqrt.log ha.ne' using 1
    change 1 / (2 * q) = b / (2 * a) / a
    field_simp
    nlinarith only [hsquare]
  have hshift : HasDerivAt (fun v => k / Real.sqrt (b * v)) (-(k / a) / (2 * q)) q := by
    convert (hasDerivAt_const q k).div hsqrt ha.ne' using 1
    change -(k / a) / (2 * q) = (0 * a - k * (b / (2 * a))) / a ^ 2
    rw [hsquare]
    field_simp
    ring
  have hpot := (SemicirclePotential.potential_hasDerivAt hz).comp q hshift
  have h := (hasDerivAt_id q).mul (hlog.add hpot)
  convert h using 1
  · rfl
  · dsimp only [dimensionSlope, a]
    simp only [Pi.add_apply, Function.comp_apply, id_eq, one_mul]
    field_simp
    ring

lemma normalized_shift_gap {J : ℕ} {b g k q : ℝ} (hb : 0 < b) (hg : 0 < g)
    (hq : q ∈ Icc (1 / (J + 1 : ℝ)) 1) (hk : 2 * Real.sqrt b + g ≤ k) :
    2 + g / Real.sqrt b ≤ k / Real.sqrt (b * q) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq.1
  have ha := Real.sqrt_pos.mpr (mul_pos hb hqpos)
  have hle : Real.sqrt (b * q) ≤ Real.sqrt b :=
    Real.sqrt_le_sqrt (by nlinarith only [hq.2, hb])
  have hs := Real.sqrt_pos.mpr hb
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ (2 + g / Real.sqrt b) * Real.sqrt b :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * Real.sqrt b + g := by field_simp
    _ ≤ k := hk

/-- The actual dimension derivative is bounded on the genuine compact
fixed-codimension/shift parameter domain, independently of ambient N. -/
theorem dimensionSlope_uniform_bound (J : ℕ) {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Icc (1 / (J + 1 : ℝ)) 1,
      ∀ k ∈ Icc (2 * Real.sqrt b + g) Z, ‖dimensionSlope b k q‖ ≤ M := by
  let s : Set (ℝ × ℝ) := (Icc (1 / (J + 1 : ℝ)) 1).prod (Icc (2 * Real.sqrt b + g) Z)
  have hc : ContinuousOn (fun p : ℝ × ℝ => dimensionSlope b p.2 p.1) s := by
    intro p hp
    have hqpos : 0 < p.1 := lt_of_lt_of_le (by positivity) hp.1.1
    have ha := Real.sqrt_pos.mpr (mul_pos hb hqpos)
    have hz : 2 < p.2 / Real.sqrt (b * p.1) := by
      have h := normalized_shift_gap hb hg hp.1 hp.2.1
      have hs := Real.sqrt_pos.mpr hb
      linarith [div_pos hg hs]
    have hroot : ContinuousAt (fun p : ℝ × ℝ => Real.sqrt (b * p.1)) p := by fun_prop
    have hshift : ContinuousAt (fun p : ℝ × ℝ => p.2 / Real.sqrt (b * p.1)) p :=
      continuous_snd.continuousAt.div hroot ha.ne'
    have hlog := hroot.log ha.ne'
    have hpot := (SemicirclePotential.potential_hasDerivAt hz).continuousAt.comp (f := fun v : ℝ × ℝ => v.2 / Real.sqrt (b * v.1)) hshift
    have hres := (SemicirclePotential.resolvent_hasDerivAt hz).continuousAt.comp (f := fun v : ℝ × ℝ => v.2 / Real.sqrt (b * v.1)) hshift
    exact ((hlog.add hpot).add ((continuousAt_const.sub (hshift.mul hres)).div_const 2)).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro q hq k hk
  exact (hM (q,k) ⟨hq,hk⟩).trans (le_max_left _ _)

/-- The source dimension exponent as an ordinary differentiable function
of the actual real matrix dimension. -/
def dimensionRate (N : ℕ) (b k t : ℝ) : ℝ :=
  (N : ℝ) * scaledProfile b k (t / N)

lemma dimensionRate_hasDerivAt {N : ℕ} (hN : 0 < N) {b k t : ℝ}
    (hb : 0 < b) (ht : 0 < t) (hz : 2 < k / Real.sqrt (b * (t / N))) :
    HasDerivAt (dimensionRate N b k) (dimensionSlope b k (t / N)) t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := ((scaledProfile_hasDerivAt hb (div_pos ht hNpos) hz).comp t
    ((hasDerivAt_id t).div_const (N : ℝ))).const_mul (N : ℝ)
  convert h using 1
  · rfl
  · field_simp

lemma dimensionRate_eq (n j : ℕ) (b k : ℝ) :
    dimensionRate (n + 1 + j) b k (n + 1 : ℝ) = physicalRate n j b k := by
  have hN : (n + 1 + j : ℕ) ≠ 0 := by omega
  have hroot : Real.sqrt (b * ((n + 1 : ℝ) / (n + 1 + j : ℕ))) =
      scaleFactor n (n + 1 + j) b := by
    unfold scaleFactor
    rw [mul_div_assoc]
  unfold dimensionRate scaledProfile physicalRate
  rw [hroot]
  have hcancel : (n + 1 + j : ℕ) * ((n + 1 : ℝ) / (n + 1 + j : ℕ)) = (n + 1 : ℝ) := by
    field_simp
  rw [← mul_assoc, hcancel]

/-- True mean-value estimate for the exponent, uniform in ambient dimension. -/
theorem dimensionRate_uniform_lipschitz (J : ℕ) {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 0 < N → ∀ k ∈ Icc (2 * Real.sqrt b + g) Z,
      ∀ t₁ ∈ Icc ((N : ℝ) / (J + 1 : ℝ)) N,
      ∀ t₂ ∈ Icc ((N : ℝ) / (J + 1 : ℝ)) N,
      ‖dimensionRate N b k t₁ - dimensionRate N b k t₂‖ ≤ M * ‖t₁ - t₂‖ := by
  obtain ⟨M, hM, hbound⟩ := dimensionSlope_uniform_bound J (Z := Z) hb hg
  refine ⟨M, hM, ?_⟩
  intro N hN k hk t₁ ht₁ t₂ ht₂
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hJpos : (0 : ℝ) < J + 1 := by positivity
  have hnormalized (t : ℝ) (ht : t ∈ Icc ((N : ℝ) / (J + 1 : ℝ)) N) :
      t / N ∈ Icc (1 / (J + 1 : ℝ)) 1 := by
    constructor
    · have he : ((N : ℝ) / (J + 1 : ℝ)) / N = 1 / (J + 1 : ℝ) := by field_simp
      rw [← he]
      exact div_le_div_of_nonneg_right ht.1 hNpos.le
    · exact (div_le_one hNpos).mpr ht.2
  have hd (t : ℝ) (ht : t ∈ Icc ((N : ℝ) / (J + 1 : ℝ)) N) :
      HasDerivWithinAt (dimensionRate N b k) (dimensionSlope b k (t / N))
        (Icc ((N : ℝ) / (J + 1 : ℝ)) N) t := by
    have hq := hnormalized t ht
    have htpos : 0 < t := (div_pos hNpos hJpos).trans_le ht.1
    have hgap := normalized_shift_gap hb hg hq hk.1
    have hz : 2 < k / Real.sqrt (b * (t / N)) := by
      have hsmall : 0 < g / Real.sqrt b := div_pos hg (Real.sqrt_pos.mpr hb)
      linarith
    exact (dimensionRate_hasDerivAt hN hb htpos hz).hasDerivWithinAt
  exact (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun t ht => hbound (t / N) (hnormalized t ht) k hk) ht₂ ht₁

lemma actual_dimension_in_interval (J n j : ℕ) (hj : j ≤ J) :
    (n + 1 : ℝ) ∈ Icc ((n + 1 + j : ℕ) / (J + 1 : ℝ)) (n + 1 + j : ℕ) := by
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < J + 1)).mpr
    have hj' : (j : ℝ) ≤ J := by exact_mod_cast hj
    have hn : (0 : ℝ) ≤ n := by positivity
    have hJ : (0 : ℝ) ≤ J := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg hn hJ]
  · simp only [Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_right (Nat.cast_nonneg j)

/-- The actual Λ_(m,N) values for bounded codimension changes differ by a
uniform finite amount, with no asymptotic hypothesis supplied. -/
theorem physicalRate_fixed_codimension_bound (J : ℕ) {b g Z : ℝ}
    (hb : 0 < b) (hg : 0 < g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n₁ n₂ j₁ j₂ : ℕ, j₁ ≤ J → j₂ ≤ J →
      n₁ + 1 + j₁ = n₂ + 1 + j₂ → ∀ k ∈ Icc (2 * Real.sqrt b + g) Z,
      ‖physicalRate n₁ j₁ b k - physicalRate n₂ j₂ b k‖ ≤ B := by
  obtain ⟨M, hM, h⟩ := dimensionRate_uniform_lipschitz J (Z := Z) hb hg
  refine ⟨M * J, mul_nonneg hM (Nat.cast_nonneg _), ?_⟩
  intro n₁ n₂ j₁ j₂ hj₁ hj₂ hN k hk
  have h₁ := actual_dimension_in_interval J n₁ j₁ hj₁
  have h₂ := actual_dimension_in_interval J n₂ j₂ hj₂
  rw [← hN] at h₂
  have hh := h (n₁ + 1 + j₁) (by omega) k hk (n₁ + 1 : ℝ) h₁ (n₂ + 1 : ℝ) h₂
  rw [dimensionRate_eq, hN, dimensionRate_eq] at hh
  have hd : ‖(n₁ + 1 : ℝ) - (n₂ + 1 : ℝ)‖ ≤ (J : ℝ) := by
    rw [Real.norm_eq_abs, abs_le]
    have hj₁' : (j₁ : ℝ) ≤ J := by exact_mod_cast hj₁
    have hj₂' : (j₂ : ℝ) ≤ J := by exact_mod_cast hj₂
    have hN' : (n₁ : ℝ) + 1 + j₁ = (n₂ : ℝ) + 1 + j₂ := by exact_mod_cast hN
    have hz₁ : (0 : ℝ) ≤ j₁ := by positivity
    have hz₂ : (0 : ℝ) ≤ j₂ := by positivity
    constructor <;> linarith
  exact hh.trans (mul_le_mul_of_nonneg_left hd hM)

/-- Genuine ordinary expected determinants at dimensions differing by a fixed
bounded integer are uniformly comparable, throughout the fixed gap interval. -/
theorem physicalMean_fixed_codimension_comparable (J : ℕ) {b g Z : ℝ}
    (hb : 0 < b) (hg : 0 < g) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₁ n₂ j₁ j₂ : ℕ, j₁ ≤ J → j₂ ≤ J →
      n₁ + 1 + j₁ = n₂ + 1 + j₂ → ∀ k ∈ Icc (2 * Real.sqrt b + g) Z,
      physicalMean n₁ (n₁ + 1 + j₁) b k ≤ C * physicalMean n₂ (n₂ + 1 + j₂) b k := by
  classical
  choose C hC hpref using (fun j : ℕ => physical_first_prefactors j (Z := Z) hb hg)
  let Cmax : ℝ := ∑ j ∈ Finset.range (J + 1), C j
  have hCmax : 0 < Cmax := by
    apply Finset.sum_pos
    · intro j hj
      exact hC j
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨B, hB, hbound⟩ := physicalRate_fixed_codimension_bound J (Z := Z) hb hg
  refine ⟨Cmax * Real.exp B, mul_pos hCmax (Real.exp_pos _), ?_⟩
  intro n₁ n₂ j₁ j₂ hj₁ hj₂ hN k hk
  have hp₁ := hpref j₁ n₁ k hk.1 hk.2
  have hp₂ := hpref j₂ n₂ k hk.1 hk.2
  have hC₁ : C j₁ ≤ Cmax := Finset.single_le_sum (fun j hj => (hC j).le)
    (Finset.mem_range.mpr (by omega))
  have hd := hbound n₁ n₂ j₁ j₂ hj₁ hj₂ hN k hk
  have hrate : physicalRate n₁ j₁ b k ≤ B + physicalRate n₂ j₂ b k := by
    have hle := (le_abs_self (physicalRate n₁ j₁ b k - physicalRate n₂ j₂ b k)).trans
      (by simpa only [Real.norm_eq_abs] using hd)
    linarith
  calc
    _ ≤ C j₁ * Real.exp (physicalRate n₁ j₁ b k) := hp₁.2
    _ ≤ Cmax * Real.exp (physicalRate n₁ j₁ b k) := mul_le_mul_of_nonneg_right hC₁ (Real.exp_pos _).le
    _ ≤ Cmax * Real.exp (B + physicalRate n₂ j₂ b k) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) hCmax.le
    _ = (Cmax * Real.exp B) * Real.exp (physicalRate n₂ j₂ b k) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp₂.1 (mul_pos hCmax (Real.exp_pos _)).le

end
end SlowEquilibration.GOEDimensionComparison
