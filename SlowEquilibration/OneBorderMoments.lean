-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.BorderMomentTransfer
public import SlowEquilibration.GaussianMatrixMomentLaw

/-! Actual one-border determinant moments. The bulk and its border live on
the same probability space; the proof imposes no independence. -/

@[expose] public section

namespace SlowEquilibration.OneBorderMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Function Matrix
open GOEAsymptotics OAI.CriticalSK GaussianMatrixMomentLaw
open SpectralTraceLipschitz SymmetricGaussianCovariance
open scoped BigOperators ENNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- The actual matrix spectral trace is independent of the arbitrary
reindexing of its orthonormal eigenbasis. -/
lemma eigenvalue_trace_eq {m : ℕ} (A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j, A i j = A j i) (hM : (gaussianToMatrix A).IsHermitian)
    (f : ℝ → ℝ) :
    (∑ i, f (hM.eigenvalues i)) = ∑ i, f (matrixOrderedEigenvalues A i) := by
  let hs := gaussianMatrixCLM_symmetric A hA
  have hc : (gaussianMatrixCLM A).toLinearMap.charpoly = (gaussianToMatrix A).charpoly :=
    Matrix.charpoly_toLin _ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have hroots := hM.roots_charpoly_eq_eigenvalues
  rw [← hc, hs.roots_charpoly_eq_eigenvalues (n := m) (by simp)] at hroots
  have ht := congrArg (fun s : Multiset ℝ => (s.map f).sum) hroots
  simpa only [matrixOrderedEigenvalues_eq A hA, Multiset.map_map,
    RCLike.ofReal_real_eq_id, id_eq, Function.comp_def, ← Finset.sum_eq_multiset_sum] using ht.symm

lemma one_border_bound_ordered {n : ℕ} (A : GOEAsymptotics.GaussianMatrix (n+1))
    (hA : ∀ i j, A i j = A j i) (k : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (a : ℝ) (u : Fin (n+1) → ℝ) :
    |(GOEBorderedDeterminant.border a u u (k • 1 - gaussianToMatrix A)).det| ≤
      Real.exp (∑ i, SpectralTraceLipschitz.clippedLog k rho (matrixOrderedEigenvalues A i)) *
        (|a| + (∑ i, u i ^ 2) / rho) := by
  have hM : (gaussianToMatrix A).IsHermitian := by
    ext i j
    exact hA j i
  have h := OneBorderDeterminant.shifted_one_border_bound (gaussianToMatrix A) hM k hrho a u
  rw [eigenvalue_trace_eq A hA hM (fun z => Real.log (max |k-z| rho))] at h
  exact h

/-- Genuine Cauchy--Schwarz moment transfer from an almost everywhere product
bound, with all ordinary integrability obligations proved. -/
lemma moment_of_product_domination {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D E B : Ω → ℝ) (hD : Measurable D) (hE : Measurable E) (hB : Measurable B)
    (hD0 : ∀ x, 0 ≤ D x) (hE0 : ∀ x, 0 ≤ E x) (hB0 : ∀ x, 0 ≤ B x)
    (hdom : ∀ᵐ x ∂μ, D x ≤ E x * B x) {r : ℝ} (hr : 0 ≤ r)
    (hEm : Integrable (fun x => E x ^ (2*r)) μ)
    (hBm : Integrable (fun x => B x ^ (2*r)) μ) :
    Integrable (fun x => D x ^ r) μ ∧
      (∫ x, D x ^ r ∂μ) ≤ Real.sqrt (∫ x, E x ^ (2*r) ∂μ) *
        Real.sqrt (∫ x, B x ^ (2*r) ∂μ) := by
  have hepow (x) : (E x ^ r) ^ (2 : ℕ) = E x ^ (2*r) := by
    simpa only [Real.rpow_two, mul_comm] using (Real.rpow_mul (hE0 x) r 2).symm
  have hbpow (x) : (B x ^ r) ^ (2 : ℕ) = B x ^ (2*r) := by
    simpa only [Real.rpow_two, mul_comm] using (Real.rpow_mul (hB0 x) r 2).symm
  have he : MemLp (fun x => E x ^ r) 2 μ :=
    (memLp_two_iff_integrable_sq (hE.pow_const r).aestronglyMeasurable).mpr
      (by simpa only [hepow] using hEm)
  have hb : MemLp (fun x => B x ^ r) 2 μ :=
    (memLp_two_iff_integrable_sq (hB.pow_const r).aestronglyMeasurable).mpr
      (by simpa only [hbpow] using hBm)
  have hprod : Integrable (fun x => E x ^ r * B x ^ r) μ :=
    memLp_one_iff_integrable.mp (he.mul hb)
  have hp : ∀ᵐ x ∂μ, D x ^ r ≤ E x ^ r * B x ^ r := by
    filter_upwards [hdom] with x hx
    simpa only [Real.mul_rpow (hE0 x) (hB0 x)] using Real.rpow_le_rpow (hD0 x) hx hr
  have hdi : Integrable (fun x => D x ^ r) μ := hprod.mono' (hD.pow_const r).aestronglyMeasurable (by
    filter_upwards [hp] with x hx
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (hD0 x) r)] using hx)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all μ fun x => Real.rpow_nonneg (hE0 x) r)
    (ae_of_all μ fun x => Real.rpow_nonneg (hB0 x) r) (by simpa using he) (by simpa using hb)
  have her (x) : (E x ^ r) ^ (2 : ℝ) = E x ^ (2*r) := by
    rw [← Real.rpow_mul (hE0 x)]
    congr 1
    ring
  have hbr (x) : (B x ^ r) ^ (2 : ℝ) = B x ^ (2*r) := by
    rw [← Real.rpow_mul (hB0 x)]
    congr 1
    ring
  simp only [her, hbr, ← Real.sqrt_eq_rpow] at hCS
  exact ⟨hdi, (integral_mono_ae hdi hprod hp).trans hCS⟩

/-- The actual absolute determinant of the literal one-border matrix. -/
def borderDet {n : ℕ} (C : GOEAsymptotics.GaussianMatrix (n+1)) (k : ℝ)
    (a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ)
    (u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ :=
  |(GOEBorderedDeterminant.border (a A) (u A) (u A)
    (k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - gaussianToMatrix (C+A))).det|

def borderFactor {n : ℕ} (rho : ℝ)
    (a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ)
    (u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ)
    (A : GOEAsymptotics.GaussianMatrix (n+1)) : ℝ := |a A| + (∑ i, u A i ^ 2) / rho

lemma borderDet_measurable {n : ℕ} (C : GOEAsymptotics.GaussianMatrix (n+1)) (k : ℝ)
    {a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ}
    {u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ}
    (ha : Measurable a) (hu : Measurable u) : Measurable (borderDet C k a u) := by
  have hm : Measurable (fun A => GOEBorderedDeterminant.border (a A) (u A) (u A)
      (k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - gaussianToMatrix (C+A))) := by
    apply Measurable.of_eval_matrix
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact ha
      | inr j => exact (measurable_pi_apply j).comp hu
    | inr i =>
      cases j with
      | inl j => exact (measurable_pi_apply i).comp hu
      | inr j =>
        change Measurable (fun A : GOEAsymptotics.GaussianMatrix (n+1) =>
          k * (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i j - (C+A) i j)
        fun_prop
  have hd : Measurable (fun M : Matrix (Unit ⊕ Fin (n+1)) (Unit ⊕ Fin (n+1)) ℝ => M.det) :=
    continuous_id.matrix_det.measurable
  exact (hd.comp hm).abs

lemma borderFactor_measurable {n : ℕ} (rho : ℝ)
    {a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ}
    {u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ}
    (ha : Measurable a) (hu : Measurable u) : Measurable (borderFactor rho a u) := by
  exact ha.abs.add ((Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hu).pow_const 2)).div_const rho)

/-- Actual bulk moment estimates imply the literal one-border upper moment
bound on the common space, without imposing independence. -/
theorem normalized_border_moment_of_bulk {n : ℕ}
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1)))
    (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (hC : ∀ i j, C i j = C j i)
    (k : ℝ) {rho : ℝ} (hrho : 0 < rho) (bound : ℝ → ℝ)
    (hbulk : MomentBounds μ C k rho bound)
    (a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ)
    (u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ)
    (ha : Measurable a) (hu : Measurable u) {r : ℝ} (hr : 0 ≤ r)
    (hBm : Integrable (fun A => borderFactor rho a u A ^ (2*r)) μ) :
    Integrable (fun A => (borderDet C k a u A / (∫ B, rawDet C k B ∂μ)) ^ r) μ ∧
      (∫ A, (borderDet C k a u A / (∫ B, rawDet C k B ∂μ)) ^ r ∂μ) ≤
        Real.sqrt (bound (2*r)) * Real.sqrt (∫ A, borderFactor rho a u A ^ (2*r) ∂μ) := by
  let m := ∫ B, rawDet C k B ∂μ
  let E := fun A => Real.exp (logClipped C k rho A) / m
  let D := fun A => borderDet C k a u A / m
  have hm : 0 < m := hbulk.expectation_pos
  have hb0 (A) : 0 ≤ borderFactor rho a u A := by
    unfold borderFactor
    positivity
  have hdom : ∀ᵐ A ∂μ, D A ≤ E A * borderFactor rho a u A := by
    filter_upwards [hSym] with A hA
    have h := one_border_bound_ordered (C+A) (fun i j => by
      change C i j + A i j = C j i + A j i
      rw [hC i j, hA i j]) k hrho (a A) (u A)
    change borderDet C k a u A ≤ Real.exp (logClipped C k rho A) * borderFactor rho a u A at h
    exact (div_le_div_of_nonneg_right h hm.le).trans_eq (by dsimp [D,E]; ring)
  have h := moment_of_product_domination D E (borderFactor rho a u)
    ((borderDet_measurable C k ha hu).div_const _) ((logClipped_measurable C k rho).exp.div_const _)
    (borderFactor_measurable rho ha hu) (fun A => div_nonneg (abs_nonneg _) hm.le)
    (fun A => div_nonneg (Real.exp_pos _).le hm.le) hb0 hdom hr
    (hbulk.clipped_integrable (2*r) (by positivity)) hBm
  refine ⟨h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hbulk.upper (2*r) (by positivity)))
    (Real.sqrt_nonneg _)

/-- Genuine law-level one-border upper moments in every dimension, for the
actual covariance condition of the manuscript. The Gaussian bulk theorem is
proved independently and no border moment conclusion is assumed. -/
theorem normalized_one_border_moments_all_dimensions {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N n : ℕ), n+1 ≤ N →
      ∀ (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsGaussian μ],
      (∫ A, A ∂μ = 0) → (∀ᵐ A ∂μ, ∀ i j, A i j = A j i) →
      (∀ M : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, M i j = M j i) →
        Var[fun A => Matrix.trace (entries A * entries M); μ] ≤
          (2*b/N)*Matrix.trace (entries M * entries M)) →
      ∀ C : GOEAsymptotics.GaussianMatrix (n+1), (∀ i j, C i j = C j i) →
      ‖gaussianMatrixCLM C‖ ≤ g/4 → ∀ k : ℝ, 2*Real.sqrt b+g ≤ k →
      ∀ (a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ)
        (u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ),
      Measurable a → Measurable u → ∀ r : ℝ, 0 ≤ r →
      Integrable (fun A => borderFactor (g/2) a u A ^ (2*r)) μ →
      Integrable (fun A => (borderDet C k a u A / (∫ B, rawDet C k B ∂μ)) ^ r) μ ∧
      (∫ A, (borderDet C k a u A / (∫ B, rawDet C k B ∂μ)) ^ r ∂μ) ≤
        Real.sqrt (K^(2*r)*Real.exp (K*(2*r)^2)) *
          Real.sqrt (∫ A, borderFactor (g/2) a u A ^ (2*r) ∂μ) := by
  obtain ⟨K,hK,hall⟩ := normalized_moments_all_dimensions hb hg
  refine ⟨K,hK,?_⟩
  intro N n hN μ _ hmean hSym hvar C hC hCop k hk a u ha hu r hr hBm
  exact normalized_border_moment_of_bulk μ hSym C hC k (by positivity) _
    (hall N n hN μ hmean hSym hvar C hC hCop k hk) a u ha hu hr hBm

/-- The true one-border determinant factors by the scalar Schur complement
on the ordinary invertibility event. -/
lemma one_border_schur_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : T.det ≠ 0) (a : ℝ) (u : ι → ℝ) :
    (GOEBorderedDeterminant.border a u u T).det =
      T.det * (a - u ⬝ᵥ (T⁻¹ *ᵥ u)) := by
  have hadj : T.adjugate = T.det • T⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hT, one_smul]
  rw [GOEBorderedDeterminant.border_det, hadj, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The source scalar Schur hypothesis yields the genuine pointwise absolute
determinant lower bound on the specified good event. -/
lemma one_border_schur_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : T.det ≠ 0) (a : ℝ) (u : ι → ℝ)
    {s : ℝ} (hs : s ≤ |a - u ⬝ᵥ (T⁻¹ *ᵥ u)|) :
    s * |T.det| ≤ |(GOEBorderedDeterminant.border a u u T).det| := by
  rw [one_border_schur_det T hT a u, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (abs_nonneg T.det)

/-- A genuine second-moment rare-event estimate controls the mass lost off
the good event. The desired lower expectation is derived, not assumed. -/
lemma expectation_lower_from_good_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D T : Ω → ℝ) (hD : Integrable D μ) (hT : Integrable T μ)
    (hD0 : ∀ x, 0 ≤ D x) (hT0 : ∀ x, 0 ≤ T x)
    (hm : 0 < ∫ x, T x ∂μ) (G : Set Ω) (hG : MeasurableSet G)
    (s : ℝ) (hs : 0 ≤ s)
    (hlower : ∀ᵐ x ∂μ, x ∈ G → s*T x ≤ D x)
    (K2 : ℝ) (hsecond : Integrable (fun x => (T x/(∫ y,T y ∂μ))^2) μ)
    (hbound : (∫ x, (T x/(∫ y,T y ∂μ))^2 ∂μ) ≤ K2)
    (hsmall : Real.sqrt K2 * Real.sqrt (μ.real Gᶜ) ≤ 1/2) :
    s * (∫ x, T x ∂μ) / 2 ≤ ∫ x, D x ∂μ := by
  let m := ∫ y,T y ∂μ
  let F := fun x => T x/m
  have hm' : 0 < m := hm
  have hFi : Integrable F μ := hT.div_const m
  have hF0 (x) : 0 ≤ F x := div_nonneg (hT0 x) hm'.le
  have hF2 : MemLp F 2 μ := by
    apply (memLp_two_iff_integrable_sq hFi.aestronglyMeasurable).mpr
    exact hsecond
  have hI2 : MemLp (Gᶜ.indicator (fun _ : Ω => (1:ℝ))) 2 μ :=
    (memLp_const 1).indicator hG.compl
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := F) (g := Gᶜ.indicator (fun _ : Ω => (1:ℝ)))
    (show (2:ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all μ hF0) (ae_of_all μ (fun x => by
      by_cases hx : x ∈ Gᶜ <;> simp [hx])) (by simpa using hF2) (by simpa using hI2)
  have hpow : (fun x : Ω => (Gᶜ.indicator (fun _ => (1:ℝ)) x)^ (2:ℝ)) =
      Gᶜ.indicator (fun _ => (1:ℝ)) := by
    funext x
    by_cases hx : x ∈ Gᶜ <;> simp [hx]
  rw [hpow, integral_indicator_const 1 hG.compl] at hCS
  simp only [smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] at hCS
  have hFpow (x) : F x ^ (2:ℝ) = (T x/m)^ (2:ℕ) := by
    exact Real.rpow_two _
  simp only [hFpow] at hCS
  have hbad : (∫ x in Gᶜ, F x ∂μ) ≤ 1/2 := by
    have he : (fun x => F x * Gᶜ.indicator (fun _ => (1:ℝ)) x) = Gᶜ.indicator F := by
      funext x
      by_cases hx : x ∈ Gᶜ <;> simp [hx]
    rw [he, integral_indicator hG.compl] at hCS
    exact hCS.trans ((mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hbound)
      (Real.sqrt_nonneg _)).trans hsmall)
  have hbadT : (∫ x in Gᶜ, T x ∂μ) ≤ m/2 := by
    have he : (∫ x in Gᶜ, F x ∂μ) = (∫ x in Gᶜ, T x ∂μ)/m := integral_div m T
    rw [he] at hbad
    exact (div_le_iff₀ hm').mp hbad |>.trans_eq (by ring)
  have hgoodT : m/2 ≤ ∫ x in G, T x ∂μ := by
    have he : (∫ x in G, T x ∂μ) + (∫ x in Gᶜ, T x ∂μ) = m :=
      integral_add_compl hG hT
    linarith
  have hgoodD : s*(∫ x in G,T x ∂μ) ≤ ∫ x,D x ∂μ := by
    rw [← integral_const_mul, ← integral_indicator hG]
    apply integral_mono_ae ((hT.const_mul s).indicator hG) hD
    filter_upwards [hlower] with x hx
    by_cases hxG : x ∈ G
    · simpa only [Set.indicator_of_mem hxG] using hx hxG
    · simp only [Set.indicator_of_notMem hxG]
      exact hD0 x
  calc
    _ = s*(m/2) := by dsimp [m]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hgoodT hs).trans hgoodD

/-- The true Schur good-event assumptions of the source give the one-border
first-moment lower bound against the actual bulk expectation. -/
theorem border_expectation_lower_of_schur {n : ℕ}
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsProbabilityMeasure μ]
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (k rho : ℝ) (bound : ℝ → ℝ)
    (hbulk : MomentBounds μ C k rho bound)
    (a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ)
    (u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ)
    (hD : Integrable (borderDet C k a u) μ)
    (G : Set (GOEAsymptotics.GaussianMatrix (n+1))) (hG : MeasurableSet G)
    {s : ℝ} (hs : 0 < s)
    (hschur : ∀ᵐ A ∂μ, A ∈ G →
      (k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - gaussianToMatrix (C+A)).det ≠ 0 ∧
      s ≤ |a A - u A ⬝ᵥ ((k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) -
        gaussianToMatrix (C+A))⁻¹ *ᵥ u A)|)
    (hsmall : Real.sqrt (bound 2) * Real.sqrt (μ.real Gᶜ) ≤ 1/2) :
    s*(∫ A, rawDet C k A ∂μ)/2 ≤ ∫ A, borderDet C k a u A ∂μ := by
  apply expectation_lower_from_good_event μ (borderDet C k a u) (rawDet C k)
    hD hbulk.integrable (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    hbulk.expectation_pos G hG s hs.le ?_ (bound 2) ?_ ?_ hsmall
  · filter_upwards [hschur] with A hA
    intro hAG
    exact one_border_schur_lower _ (hA hAG).1 (a A) (u A) (hA hAG).2
  · simpa only [Real.rpow_two] using hbulk.raw_integrable 2 (by norm_num)
  · simpa only [Real.rpow_two] using
      (hbulk.ordered 2 (by norm_num)).trans (hbulk.upper 2 (by norm_num))

/-- An actual lower mean comparison rescales a normalized moment to the
observable's own ordinary expectation. -/
lemma own_mean_moment_of_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (D : Ω → ℝ) (hD0 : ∀ x, 0 ≤ D x) {m s r U : ℝ}
    (hm : 0 < m) (hs : 0 < s) (hr : 0 ≤ r)
    (hlower : s*m/2 ≤ ∫ x,D x ∂μ)
    (hI : Integrable (fun x => (D x/m)^r) μ)
    (hU : (∫ x,(D x/m)^r ∂μ) ≤ U) :
    0 < ∫ x,D x ∂μ ∧ Integrable (fun x => (D x/(∫ y,D y ∂μ))^r) μ ∧
      (∫ x,(D x/(∫ y,D y ∂μ))^r ∂μ) ≤ (2/s)^r*U := by
  let e := ∫ x,D x ∂μ
  have he : 0 < e := (by positivity : 0 < s*m/2).trans_le hlower
  have hc : m/e ≤ 2/s := by
    apply (div_le_iff₀ he).mpr
    calc
      m ≤ 2*e/s := (le_div_iff₀ hs).mpr (by dsimp [e]; nlinarith [hlower])
      _ = _ := by ring
  have hpoint (x) : (D x/e)^r = (D x/m)^r*(m/e)^r := by
    rw [← Real.mul_rpow (div_nonneg (hD0 x) hm.le) (div_nonneg hm.le he.le)]
    congr 1
    field_simp
  have hi : Integrable (fun x => (D x/e)^r) μ := by
    simpa only [hpoint] using hI.mul_const ((m/e)^r)
  have hn : 0 ≤ ∫ x,(D x/m)^r ∂μ := integral_nonneg fun x => Real.rpow_nonneg (div_nonneg (hD0 x) hm.le) r
  refine ⟨he,hi,?_⟩
  calc
    _ = (∫ x,(D x/m)^r ∂μ)*(m/e)^r := by
      change (∫ x,(D x/e)^r ∂μ) = _
      simp only [hpoint, integral_mul_const]
    _ ≤ (∫ x,(D x/m)^r ∂μ)*(2/s)^r :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hm.le he.le) hc hr) hn
    _ ≤ U*(2/s)^r := mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg (by positivity) r)
    _ = _ := mul_comm _ _

/-- Source one-border normalization under its true Schur event: first moment
lower bound and all nonnegative real moments normalized by the bordered
matrix's own actual expectation. No independence hypothesis is used. -/
theorem own_mean_border_moment_of_schur {n : ℕ}
    (μ : Measure (GOEAsymptotics.GaussianMatrix (n+1))) [IsProbabilityMeasure μ]
    (hSym : ∀ᵐ A ∂μ, ∀ i j, A i j = A j i)
    (C : GOEAsymptotics.GaussianMatrix (n+1)) (hC : ∀ i j, C i j = C j i)
    (k : ℝ) {rho : ℝ} (hrho : 0 < rho) (bound : ℝ → ℝ)
    (hbulk : MomentBounds μ C k rho bound)
    (a : GOEAsymptotics.GaussianMatrix (n+1) → ℝ)
    (u : GOEAsymptotics.GaussianMatrix (n+1) → Fin (n+1) → ℝ)
    (ha : Measurable a) (hu : Measurable u)
    (hB2 : Integrable (fun A => borderFactor rho a u A ^ (2:ℝ)) μ)
    (G : Set (GOEAsymptotics.GaussianMatrix (n+1))) (hG : MeasurableSet G)
    {s : ℝ} (hs : 0 < s)
    (hschur : ∀ᵐ A ∂μ, A ∈ G →
      (k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - gaussianToMatrix (C+A)).det ≠ 0 ∧
      s ≤ |a A - u A ⬝ᵥ ((k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) -
        gaussianToMatrix (C+A))⁻¹ *ᵥ u A)|)
    (hsmall : Real.sqrt (bound 2) * Real.sqrt (μ.real Gᶜ) ≤ 1/2)
    {r : ℝ} (hr : 0 ≤ r)
    (hBm : Integrable (fun A => borderFactor rho a u A ^ (2*r)) μ) :
    Integrable (borderDet C k a u) μ ∧
    s*(∫ A,rawDet C k A ∂μ)/2 ≤ ∫ A,borderDet C k a u A ∂μ ∧
    0 < ∫ A,borderDet C k a u A ∂μ ∧
    Integrable (fun A => (borderDet C k a u A/(∫ B,borderDet C k a u B ∂μ))^r) μ ∧
    (∫ A,(borderDet C k a u A/(∫ B,borderDet C k a u B ∂μ))^r ∂μ) ≤
      (2/s)^r*Real.sqrt (bound (2*r))*Real.sqrt (∫ A,borderFactor rho a u A^(2*r) ∂μ) := by
  have hm := hbulk.expectation_pos
  have hI1 := (normalized_border_moment_of_bulk μ hSym C hC k hrho bound hbulk a u ha hu
    (r := 1) (by norm_num) (by simpa only [mul_one] using hB2)).1
  simp only [Real.rpow_one] at hI1
  have hD : Integrable (borderDet C k a u) μ := by
    convert hI1.mul_const (∫ B,rawDet C k B ∂μ) using 1
    funext A
    exact (div_mul_cancel₀ _ hm.ne').symm
  have hlow := border_expectation_lower_of_schur μ C k rho bound hbulk a u hD G hG hs hschur hsmall
  have hupper := normalized_border_moment_of_bulk μ hSym C hC k hrho bound hbulk a u ha hu hr hBm
  have h := own_mean_moment_of_lower (borderDet C k a u) (fun _ => abs_nonneg _) hm hs hr hlow hupper.1 hupper.2
  refine ⟨hD,hlow,h.1,h.2.1,?_⟩
  exact h.2.2.trans_eq (by ring)

end
end SlowEquilibration.OneBorderMoments
