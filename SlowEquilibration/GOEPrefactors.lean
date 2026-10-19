-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEExpectedDeterminant

@[expose] public section

/-! # Actual canonical GOE determinant prefactors

The actual signed expectation is the proved scaled-Hermite polynomial. Its
actual Jacobi comparison and the genuine signed/absolute rare-event estimate
supply bounded prefactors for ordinary absolute determinants.
-/

namespace SlowEquilibration.GOEPrefactors

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open OAI.CriticalSK GOEExpectedDeterminant GOEClippedDeterminants GOESignedAbsoluteTransfer
open scoped ENNReal NNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev MatrixSpace (n : ℕ) := GOEAsymptotics.GaussianMatrix (n + 1)

def meanAbsolute (n : ℕ) (k : ℝ) : ℝ := ∫ A, absoluteDet n k A ∂stdGaussian (MatrixSpace n)

def firstPrefactor (d : ℝ) : ℝ := 2 * Real.exp (1 / (2 * d ^ 2))

def momentPrefactor (d r : ℝ) : ℝ :=
  (2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / d ^ 2) * (firstPrefactor d) ^ r

lemma signed_integrable (n : ℕ) (k : ℝ) : Integrable (signedDet n k) (stdGaussian (MatrixSpace n)) := by
  have hmp : MeasurePreserving (symmetrizeGaussianMatrix (goeScale n))
      (stdGaussian (GaussianMatrix (Fin (n + 1)))) (goeLaw (Fin (n + 1)) (goeScale n)) :=
    ⟨(symmetrizeGaussianMatrix_continuous _).measurable, rfl⟩
  exact hmp.integrable_comp_of_integrable (shifted_det_integrable _ _ _)

lemma absolute_integrable (n : ℕ) (k : ℝ) : Integrable (absoluteDet n k) (stdGaussian (MatrixSpace n)) :=
  (signed_integrable n k).abs

/-- The exact lower prefactor is one, in every positive dimension. -/
theorem meanAbsolute_lower (n : ℕ) {k : ℝ} (hk : 2 < k) :
    Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential k) ≤ meanAbsolute n k := by
  calc
    _ ≤ JacobiPrefactors.hermiteValue n k := (JacobiPrefactors.hermiteValue_prefactors n hk).1
    _ = ∫ A, signedDet n k A ∂stdGaussian (MatrixSpace n) := (standard_signed_mean_eq_hermiteValue n k).symm
    _ ≤ _ := integral_mono (signed_integrable n k) (absolute_integrable n k) (fun A => le_abs_self _)

lemma meanAbsolute_pos (n : ℕ) {k : ℝ} (hk : 2 < k) : 0 < meanAbsolute n k :=
  (Real.exp_pos _).trans_le (meanAbsolute_lower n hk)

/-- Uniform canonical bounded first prefactors above a fixed positive gap. -/
theorem meanAbsolute_upper_eventually {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + d ≤ k →
      meanAbsolute n k ≤ firstPrefactor d * Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential k) := by
  filter_upwards [signed_absolute_expectations_eventually hd] with n hn
  intro k hk
  have h := (hn k hk).2.2.2
  rw [standard_signed_mean_eq_hermiteValue] at h
  exact h.trans (by
    have hb := (JacobiPrefactors.hermiteValue_prefactors_uniform n hd hk).2
    have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [firstPrefactor, mul_assoc] using hh)

lemma integral_rpow_eq_normalized (n : ℕ) {k r : ℝ} (hk : 2 < k) :
    (fun A : MatrixSpace n => absoluteDet n k A ^ r) =
      fun A => meanAbsolute n k ^ r * (absoluteDet n k A / meanAbsolute n k) ^ r := by
  funext A
  have hm := meanAbsolute_pos n hk
  rw [← Real.mul_rpow hm.le (div_nonneg (absoluteDet_nonneg _ _ _) hm.le)]
  congr 1
  field_simp

lemma exponential_rpow_eq_normalized (n : ℕ) {k rho r : ℝ} (hk : 2 < k) :
    (fun A : MatrixSpace n => Real.exp (r * clippedTrace n k rho A)) =
      fun A => meanAbsolute n k ^ r * (Real.exp (clippedTrace n k rho A) / meanAbsolute n k) ^ r := by
  funext A
  have hm := meanAbsolute_pos n hk
  rw [← Real.mul_rpow hm.le (div_nonneg (Real.exp_pos _).le hm.le)]
  rw [mul_div_cancel₀ _ hm.ne', ← Real.exp_mul]
  congr 1
  ring

/-- Actual ordinary higher moments and actual clipped exponentials have
bounded spectral-potential prefactors, with no determinant expectation input. -/
theorem moments_prefactors_eventually {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + d ≤ k → ∀ r : ℝ, 0 ≤ r →
      Integrable (fun A : MatrixSpace n => absoluteDet n k A ^ r) (stdGaussian (MatrixSpace n)) ∧
      Integrable (fun A : MatrixSpace n => Real.exp (r * clippedTrace n k (d / 2) A)) (stdGaussian (MatrixSpace n)) ∧
      (∫ A : MatrixSpace n, absoluteDet n k A ^ r ∂stdGaussian (MatrixSpace n)) ≤
        momentPrefactor d r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) ∧
      (∫ A : MatrixSpace n, Real.exp (r * clippedTrace n k (d / 2) A) ∂stdGaussian (MatrixSpace n)) ≤
        momentPrefactor d r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
  filter_upwards [meanAbsolute_upper_eventually hd,
    GOESharpMoments.raw_absoluteDet_normalized_eventually hd,
    GOESharpMoments.clipped_over_raw_normalized_eventually hd] with n hu hraw hclip
  intro k hk r hr
  have hk2 : 2 < k := by linarith
  have hR := hraw k hk |>.2.2 r hr
  have hC := hclip k hk r hr
  have hbound : meanAbsolute n k ^ r * ((2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / d ^ 2)) ≤
      momentPrefactor d r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
    have hm := meanAbsolute_pos n hk2
    have he := Real.rpow_le_rpow hm.le (hu k hk) hr
    have hf : 0 ≤ firstPrefactor d := by unfold firstPrefactor; positivity
    have hpow : (firstPrefactor d * Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential k)) ^ r =
        firstPrefactor d ^ r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
      rw [Real.mul_rpow hf (Real.exp_pos _).le, ← Real.exp_mul]
      congr 1
      ring
    rw [hpow] at he
    have h := mul_le_mul_of_nonneg_right he
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r) (Real.exp_pos (4 * r ^ 2 / d ^ 2)).le)
    exact h.trans_eq (by unfold momentPrefactor; ring)
  have hRI : Integrable (fun A : MatrixSpace n => absoluteDet n k A ^ r) (stdGaussian (MatrixSpace n)) := by
    rw [integral_rpow_eq_normalized n hk2]
    exact hR.1.const_mul _
  have hCI : Integrable (fun A : MatrixSpace n => Real.exp (r * clippedTrace n k (d / 2) A))
      (stdGaussian (MatrixSpace n)) := by
    rw [exponential_rpow_eq_normalized n hk2]
    exact hC.1.const_mul _
  refine ⟨hRI, hCI, ?_, ?_⟩
  · rw [integral_rpow_eq_normalized n hk2, integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hR.2 (Real.rpow_nonneg (meanAbsolute_pos n hk2).le _)).trans hbound
  · rw [exponential_rpow_eq_normalized n hk2, integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hC.2 (Real.rpow_nonneg (meanAbsolute_pos n hk2).le _)).trans hbound

lemma clipped_exponential_integrable (n : ℕ) (k r : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (fun A : MatrixSpace n => Real.exp (r * clippedTrace n k rho A))
      (stdGaussian (MatrixSpace n)) := by
  let m := ∫ A, clippedTrace n k rho A ∂stdGaussian (MatrixSpace n)
  have hG := GOESharpMoments.clippedTrace_centered_sharpGaussian n k hrho
  apply ((hG.integrable_exp_mul r).const_mul (Real.exp (r * m))).congr
  exact ae_of_all _ (fun A => by
    change Real.exp (r * m) * Real.exp (r * (clippedTrace n k rho A - m)) =
      Real.exp (r * clippedTrace n k rho A)
    rw [← Real.exp_add]
    congr 1
    ring)

lemma clippedLog_shift_bound {rho : ℝ} (hrho : 0 < rho) (k x : ℝ) :
    SpectralTraceLipschitz.clippedLog k rho x ≤
      SpectralTraceLipschitz.clippedLog 0 rho x + |k| / rho := by
  have h := (SpectralTraceLipschitz.clippedLog_lipschitz 0 hrho).dist_le_mul (x - k) x
  change |SpectralTraceLipschitz.clippedLog 0 rho (x - k) -
    SpectralTraceLipschitz.clippedLog 0 rho x| ≤ (1 / rho) * |x - k - x| at h
  have heq : SpectralTraceLipschitz.clippedLog 0 rho (x - k) =
      SpectralTraceLipschitz.clippedLog k rho x := by
    unfold SpectralTraceLipschitz.clippedLog
    rw [show 0 - (x - k) = k - x by ring]
  rw [heq, show x - k - x = -k by ring, abs_neg] at h
  have hh := (le_abs_self _).trans h
  calc
    _ ≤ SpectralTraceLipschitz.clippedLog 0 rho x + (1 / rho) * |k| := by linarith
    _ = _ := by ring

lemma clippedTrace_shift_upper (n : ℕ) {rho : ℝ} (hrho : 0 < rho) (k : ℝ) (A : MatrixSpace n) :
    clippedTrace n k rho A ≤ clippedTrace n 0 rho A + (n + 1 : ℝ) * |k| / rho := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    clippedLog_shift_bound hrho k (GOEEdgeConcentration.realizedEigenvalues n A i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  exact h.trans_eq (by unfold clippedTrace; ring)

lemma potential_ge_log_gap {d k : ℝ} (hd : 0 < d) (hk : 2 + d ≤ k) :
    Real.log d ≤ SemicirclePotential.potential k := by
  have hk2 : 2 < k := by linarith
  have hI : IntervalIntegrable (fun t => SemicirclePotential.density t * Real.log (k - t))
      volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr
      (SemicirclePotential.potential_integrable hk2)
  have hIc : IntervalIntegrable (fun t => SemicirclePotential.density t * Real.log d)
      volume (-2 : ℝ) 2 := SemicirclePotential.density_continuous.intervalIntegrable _ _ |>.mul_const _
  calc
    _ = ∫ t in (-2 : ℝ)..2, SemicirclePotential.density t * Real.log d := by
      rw [intervalIntegral.integral_mul_const, SemicirclePotential.density_integral_interval, one_mul]
    _ ≤ ∫ t in (-2 : ℝ)..2, SemicirclePotential.density t * Real.log (k - t) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2) hIc hI
      intro t ht
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hd (by linarith [ht.2]))
        (SemicirclePotential.density_nonneg _)
    _ = _ := (SemicirclePotential.potential_eq_interval k).symm

/-- A genuine finite-dimensional constant to absorb the finitely many small
matrices. It is an integrable actual clipped exponential expectation. -/
def finiteMomentPrefactor (n : ℕ) (d Z r : ℝ) : ℝ :=
  Real.exp (r * (n + 1 : ℝ) * (|Z| / (d / 2) - Real.log d)) *
    ∫ A : MatrixSpace n, Real.exp (r * clippedTrace n 0 (d / 2) A) ∂stdGaussian (MatrixSpace n)

lemma finiteMomentPrefactor_nonneg (n : ℕ) (d Z r : ℝ) : 0 ≤ finiteMomentPrefactor n d Z r :=
  mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le))

/-- Actual moment bounds for every fixed dimension, uniformly on the source
compact shift interval. No continuity or integrability premise is supplied. -/
lemma fixed_dimension_moment_bound (n : ℕ) {d Z k r : ℝ}
    (hd : 0 < d) (hk : 2 + d ≤ k) (hkZ : k ≤ Z) (hr : 0 ≤ r) :
    Integrable (fun A : MatrixSpace n => absoluteDet n k A ^ r) (stdGaussian (MatrixSpace n)) ∧
      (∫ A : MatrixSpace n, absoluteDet n k A ^ r ∂stdGaussian (MatrixSpace n)) ≤
        finiteMomentPrefactor n d Z r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) ∧
      (∫ A : MatrixSpace n, Real.exp (r * clippedTrace n k (d / 2) A) ∂stdGaussian (MatrixSpace n)) ≤
        finiteMomentPrefactor n d Z r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
  have hrho : 0 < d / 2 := by positivity
  have hexp := clipped_exponential_integrable n k r hrho
  have hpoint (A : MatrixSpace n) : absoluteDet n k A ^ r ≤ Real.exp (r * clippedTrace n k (d / 2) A) := by
    calc
      _ ≤ (Real.exp (clippedTrace n k (d / 2) A)) ^ r :=
        Real.rpow_le_rpow (absoluteDet_nonneg _ _ _) (absoluteDet_le_exp_clippedTrace _ _ hrho A) hr
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  have hInt : Integrable (fun A : MatrixSpace n => absoluteDet n k A ^ r) (stdGaussian (MatrixSpace n)) := by
    apply hexp.mono' ((absoluteDet_measurable n k).pow_const r).aestronglyMeasurable
    exact ae_of_all _ (fun A => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (absoluteDet_nonneg _ _ _) r)]
      exact hpoint A)
  have hkabs : |k| ≤ |Z| := by rw [abs_of_pos (by linarith : 0 < k)]; exact hkZ.trans (le_abs_self _)
  have hclip : (∫ A : MatrixSpace n, Real.exp (r * clippedTrace n k (d / 2) A) ∂stdGaussian (MatrixSpace n)) ≤
      finiteMomentPrefactor n d Z r * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
    have h0 := clipped_exponential_integrable n 0 r hrho
    have hdom (A : MatrixSpace n) : Real.exp (r * clippedTrace n k (d / 2) A) ≤
        Real.exp (r * (n + 1 : ℝ) * |Z| / (d / 2)) * Real.exp (r * clippedTrace n 0 (d / 2) A) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hs := clippedTrace_shift_upper n hrho k A
      have hb : (n + 1 : ℝ) * |k| / (d / 2) ≤ (n + 1 : ℝ) * |Z| / (d / 2) := by gcongr
      have hs' : clippedTrace n k (d / 2) A ≤
          clippedTrace n 0 (d / 2) A + (n + 1 : ℝ) * |Z| / (d / 2) := by linarith [hs, hb]
      calc
        _ ≤ r * (clippedTrace n 0 (d / 2) A + (n + 1 : ℝ) * |Z| / (d / 2)) :=
          mul_le_mul_of_nonneg_left hs' hr
        _ = _ := by ring
    calc
      _ ≤ ∫ A : MatrixSpace n, Real.exp (r * (n + 1 : ℝ) * |Z| / (d / 2)) *
          Real.exp (r * clippedTrace n 0 (d / 2) A) ∂stdGaussian (MatrixSpace n) :=
        integral_mono hexp (h0.const_mul _) hdom
      _ = Real.exp (r * (n + 1 : ℝ) * |Z| / (d / 2)) *
          ∫ A : MatrixSpace n, Real.exp (r * clippedTrace n 0 (d / 2) A) ∂stdGaussian (MatrixSpace n) :=
        integral_const_mul _ _
      _ ≤ _ := by
        have hp := potential_ge_log_gap hd hk
        have hE : Real.exp (r * (n + 1 : ℝ) * |Z| / (d / 2)) ≤
            Real.exp (r * (n + 1 : ℝ) * (|Z| / (d / 2) - Real.log d)) *
              Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hr (by positivity : 0 ≤ (n + 1 : ℝ)))
          calc
            _ = r * (n + 1 : ℝ) * (|Z| / (d / 2) - Real.log d) +
                r * (n + 1 : ℝ) * Real.log d := by ring
            _ ≤ _ := by linarith only [hh]
        have hmean0 : 0 ≤ ∫ A : MatrixSpace n, Real.exp (r * clippedTrace n 0 (d / 2) A)
            ∂stdGaussian (MatrixSpace n) := integral_nonneg (fun _ => (Real.exp_pos _).le)
        calc
          _ ≤ (Real.exp (r * (n + 1 : ℝ) * (|Z| / (d / 2) - Real.log d)) *
              Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k)) *
              ∫ A : MatrixSpace n, Real.exp (r * clippedTrace n 0 (d / 2) A)
                ∂stdGaussian (MatrixSpace n) := mul_le_mul_of_nonneg_right hE hmean0
          _ = _ := by unfold finiteMomentPrefactor; ring
  exact ⟨hInt, (integral_mono hInt hexp hpoint).trans hclip, hclip⟩

/-- The full canonical moment-prefactor conclusion for every positive matrix
dimension and every shift in the manuscript's compact outside-edge interval.
The finitely many small dimensions are absorbed using proved actual moments. -/
theorem canonical_moments_prefactors {d Z r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ k : ℝ, 2 + d ≤ k → k ≤ Z →
      Integrable (fun A : MatrixSpace n => absoluteDet n k A ^ r) (stdGaussian (MatrixSpace n)) ∧
      Integrable (fun A : MatrixSpace n => Real.exp (r * clippedTrace n k (d / 2) A)) (stdGaussian (MatrixSpace n)) ∧
      (∫ A : MatrixSpace n, absoluteDet n k A ^ r ∂stdGaussian (MatrixSpace n)) ≤
        C * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) ∧
      (∫ A : MatrixSpace n, Real.exp (r * clippedTrace n k (d / 2) A) ∂stdGaussian (MatrixSpace n)) ≤
        C * Real.exp (r * (n + 1 : ℝ) * SemicirclePotential.potential k) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (moments_prefactors_eventually hd)
  let C := momentPrefactor d r + (∑ n ∈ Finset.range M, finiteMomentPrefactor n d Z r) + 1
  have hs : 0 ≤ ∑ n ∈ Finset.range M, finiteMomentPrefactor n d Z r :=
    Finset.sum_nonneg (fun n _ => finiteMomentPrefactor_nonneg _ _ _ _)
  have hm : 0 ≤ momentPrefactor d r := by
    unfold momentPrefactor
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r)
      (Real.exp_pos _).le) (Real.rpow_nonneg (by unfold firstPrefactor; positivity) r)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro n k hk hkZ
  have hIexp := clipped_exponential_integrable n k r (by positivity : 0 < d / 2)
  by_cases hn : M ≤ n
  · have h := hM n hn k hk r hr
    have hle : momentPrefactor d r ≤ C := by dsimp [C]; linarith
    have hb := mul_le_mul_of_nonneg_right hle
      (Real.exp_pos (r * (n + 1 : ℝ) * SemicirclePotential.potential k)).le
    exact ⟨h.1, h.2.1, h.2.2.1.trans hb, h.2.2.2.trans hb⟩
  · have h := fixed_dimension_moment_bound n hd hk hkZ hr
    have hnM : n < M := lt_of_not_ge hn
    have hleSum : finiteMomentPrefactor n d Z r ≤
        ∑ j ∈ Finset.range M, finiteMomentPrefactor j d Z r :=
      Finset.single_le_sum (fun j _ => finiteMomentPrefactor_nonneg j d Z r) (Finset.mem_range.mpr hnM)
    have hle : finiteMomentPrefactor n d Z r ≤ C := by dsimp [C]; linarith
    have hb := mul_le_mul_of_nonneg_right hle
      (Real.exp_pos (r * (n + 1 : ℝ) * SemicirclePotential.potential k)).le
    exact ⟨h.1, hIexp, h.2.1.trans hb, h.2.2.trans hb⟩

/-- Exact canonical first prefactors, including the source lower constant
one, every positive dimension and the whole compact outside-edge interval. -/
theorem canonical_first_prefactors {d Z : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ k : ℝ, 2 + d ≤ k → k ≤ Z →
      Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential k) ≤ meanAbsolute n k ∧
        meanAbsolute n k ≤ C * Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential k) := by
  obtain ⟨C, hC, h⟩ := canonical_moments_prefactors (Z := Z) hd (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨C, hC, ?_⟩
  intro n k hk hkZ
  refine ⟨meanAbsolute_lower n (by linarith), ?_⟩
  simpa only [meanAbsolute, Real.rpow_one, one_mul] using (h n k hk hkZ).2.2.1

end
end SlowEquilibration.GOEPrefactors
