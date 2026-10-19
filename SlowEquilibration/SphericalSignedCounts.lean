-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountIntegrability
public import SlowEquilibration.SphericalPureMarkedWindows

/-! Literal signed critical-point sums and genuine absolute integrability. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalKacRiceGluing SphericalMorse
open SphericalIntrinsicKacRice SphericalCountIntegrability SphericalForm
open scoped ENNReal Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The actual signed sum, over the literal intrinsic critical points in the score window. -/
def actualSignedScoreWindowCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ) (J : Disorder (n+1) P) : ℝ :=
  ∑' x : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
    surfaceGradient (field c J) x = 0 ∧ actualScore c J x ∈ K}, psi J x

lemma actualScoreWindowCount_le_total {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (M : ℝ≥0∞) (hpsi : ∀ J x, psi J x ≤ M) (J : Disorder (n+1) P) :
    actualScoreWindowCount n c K psi J ≤ M * actualSphereCount n c (fun _ _ => 1) J := by
  rw [actualScoreWindowCount_eq_indicator]
  unfold actualSphereCount
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  dsimp only
  split_ifs
  · simpa only [mul_one] using hpsi J x
  · exact bot_le

lemma actualScoreWindowCount_aemeasurable (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualScoreWindowCount n c K psi) (disorderLaw (n+1) μ.maxDegree) := by
  have he := funext fun J => actualScoreWindowCount_eq_indicator n
    (centerCoefficients (mixtureCoefficients μ) Q) K psi J
  dsimp only
  rw [he]
  exact (actual_sphere_marked_kacRice n hn μ hQ _ (scoreWindowMark_measurable _ K hK psi hpsi)).1

/-- Bounded nonnegative weights have finite expectation, from the genuine
unrestricted expected total count, rather than almost-sure finiteness alone. -/
theorem bounded_scoreWindowCount_lintegral_lt_top (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (M : ℝ≥0∞) (hM : M < ⊤) (hpsi : ∀ J x, psi J x ≤ M) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount n c K psi J ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
  refine (lintegral_mono (actualScoreWindowCount_le_total n _ K psi M hpsi)).trans_lt ?_
  rw [lintegral_const_mul' _ _ hM.ne]
  exact ENNReal.mul_lt_top hM (actual_sphere_total_count_lintegral_lt_top n hn μ hQ)

lemma finite_tsum_real_parts {ι : Type*} [Finite ι] (f : ι → ℝ) :
    (∑' i, f i) = (∑' i, ENNReal.ofReal (f i)).toReal -
      (∑' i, ENNReal.ofReal (-f i)).toReal := by
  letI := Fintype.ofFinite ι
  simp only [tsum_fintype, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),
    ← Finset.sum_sub_distrib, ENNReal.toReal_ofReal']
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ f i
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · have hi : f i ≤ 0 := le_of_not_ge h
    rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
    ring

lemma actualSignedScoreWindowCount_parts {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ) (J : Disorder (n+1) P)
    (hfin : (sphereCriticalSet n c J).Finite) :
    actualSignedScoreWindowCount n c K psi J =
      (actualScoreWindowCount n c K (fun J x => ENNReal.ofReal (psi J x)) J).toReal -
      (actualScoreWindowCount n c K (fun J x => ENNReal.ofReal (-psi J x)) J).toReal := by
  have hf : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
      surfaceGradient (field c J) x = 0 ∧ actualScore c J x ∈ K}.Finite :=
    hfin.subset (fun _ h => ⟨h.1, h.2.1⟩)
  letI := hf.to_subtype
  exact finite_tsum_real_parts _

/-- Every bounded real Borel weight gives a genuinely integrable literal
signed window count and the exact finite positive-minus-negative identity. -/
theorem actualSignedScoreWindowCount_integrable_parts (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2)
    (M : ℝ) (hbound : ∀ J x, |psi J x| ≤ M) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (actualSignedScoreWindowCount n c K psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫ J, actualSignedScoreWindowCount n c K psi J ∂disorderLaw (n+1) μ.maxDegree) =
      (∫⁻ J, actualScoreWindowCount n c K (fun J x => ENNReal.ofReal (psi J x)) J
        ∂disorderLaw (n+1) μ.maxDegree).toReal -
      (∫⁻ J, actualScoreWindowCount n c K (fun J x => ENNReal.ofReal (-psi J x)) J
        ∂disorderLaw (n+1) μ.maxDegree).toReal := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let f := actualScoreWindowCount n c K (fun J x => ENNReal.ofReal (psi J x))
  let g := actualScoreWindowCount n c K (fun J x => ENNReal.ofReal (-psi J x))
  have hf := actualScoreWindowCount_aemeasurable n hn μ hQ K hK (fun J x => ENNReal.ofReal (psi J x)) hpsi.ennreal_ofReal
  have hg := actualScoreWindowCount_aemeasurable n hn μ hQ K hK (fun J x => ENNReal.ofReal (-psi J x)) hpsi.neg.ennreal_ofReal
  have hfi : (∫⁻ J, f J ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K _ (ENNReal.ofReal M) ENNReal.ofReal_lt_top
      (fun J x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hbound J x)))
  have hgi : (∫⁻ J, g J ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K _ (ENNReal.ofReal M) ENNReal.ofReal_lt_top
      (fun J x => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hbound J x)))
  have hIntf := integrable_toReal_of_lintegral_ne_top hf hfi.ne
  have hIntg := integrable_toReal_of_lintegral_ne_top hg hgi.ne
  have he : actualSignedScoreWindowCount n c K psi =ᵐ[disorderLaw (n+1) μ.maxDegree]
      (fun J => (f J).toReal - (g J).toReal) := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hJ
    exact actualSignedScoreWindowCount_parts n c K psi J hJ
  refine ⟨(hIntf.sub hIntg).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_sub hIntf hIntg,
    integral_toReal hf (ae_lt_top' hf hfi.ne), integral_toReal hg (ae_lt_top' hg hgi.ne)]

end
end SlowEquilibration.SphericalMarkedWindows
