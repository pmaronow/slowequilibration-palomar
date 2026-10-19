-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSignedMarkedWindows

/-! The actual pure score-window Kac--Rice formula for bounded signed marks. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalPosteriorMaps SphericalSequentialRegression UnrestrictedConditionedDeterminants
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The literal signed critical-point sum in a scalar value window. -/
def actualSignedValueWindowCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (I : Set ℝ) (psi : Disorder (n+1) P → Vector (n+1) → ℝ)
    (J : Disorder (n+1) P) : ℝ :=
  ∑' x : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
    surfaceGradient (field c J) x = 0 ∧ actualValue c J x ∈ I}, psi J x

lemma actual_pure_signedScoreWindowCount_eq_valueWindowCount (n : ℕ)
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree → Vector (n+1) → ℝ)
    (J : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
    actualSignedScoreWindowCount n c K psi J =
      actualSignedValueWindowCount n c (pureScoreWindow p K) psi J := by
  let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
  have hs : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
      surfaceGradient (field c J) x = 0 ∧ actualScore c J x ∈ K} =
      {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
      surfaceGradient (field c J) x = 0 ∧ actualValue c J x ∈ pureScoreWindow p K} := by
    ext x
    change (_ ∧ _ ∧ actualScore c J x ∈ K) ↔ _
    rw [actualScore_pure p hp alpha halpha Q J x]
    rfl
  exact (Set.equivOfEq hs).tsum_eq (fun x => psi J x)

/-- The source's actual signed posterior integral, with both integrals interpreted
as Bochner integrals and the full original disorder retained in the mark. -/
def valueSignedWindowIntensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (K : Set ℝ)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ) (x : Vector (n+1)) : ℝ :=
  if hx : ‖x‖ ^ 2 = (n+1 : ℕ) then
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∫ b in K, (physicalValuePdf (n+1) μ Q b).toReal *
      ∫ J, |(intrinsicHessian (field c J) x).det| * psi J x
        ∂valueConditionedLaw c x hx b
  else 0

lemma valueSignedWindowIntensity_parts (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (K : Set ℝ)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2)
    (M : ℝ) (hbound : ∀ J x, |psi J x| ≤ M)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (hD : ∀ b, Integrable (fun J =>
      |(intrinsicHessian (field (centerCoefficients (mixtureCoefficients μ) Q) J) x).det|)
      (valueConditionedLaw (n := n) (centerCoefficients (mixtureCoefficients μ) Q) x hx b))
    (hp : valueWindowIntensity n μ Q K (fun J x => ENNReal.ofReal (psi J x)) x < ⊤)
    (hm : valueWindowIntensity n μ Q K (fun J x => ENNReal.ofReal (-psi J x)) x < ⊤) :
    valueSignedWindowIntensity n μ Q K psi x =
      (valueWindowIntensity n μ Q K (fun J x => ENNReal.ofReal (psi J x)) x).toReal -
      (valueWindowIntensity n μ Q K (fun J x => ENNReal.ofReal (-psi J x)) x).toReal := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hmark : Measurable (fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) := by
    simpa only [Function.comp_def] using hpsi.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hparam : Measurable (fun b : ℝ => ((⟨x,hx⟩ : SpherePoint n), b)) :=
    measurable_const.prodMk measurable_id
  have hpp := (value_det_posterior_measurable n μ hQ
    (fun J x => ENNReal.ofReal (psi J x)) hmark.ennreal_ofReal).comp hparam
  have hpm := (value_det_posterior_measurable n μ hQ
    (fun J x => ENNReal.ofReal (-psi J x)) hmark.neg.ennreal_ofReal).comp hparam
  have hpsi_x : Measurable (fun J => psi J x) :=
    hpsi.comp (measurable_id.prodMk (measurable_const (a := x)))
  have hj (b : ℝ) := weighted_posterior_integrable_parts
    (valueConditionedLaw (n := n) c x hx b)
    (fun J => |(intrinsicHessian (field c J) x).det|) (fun J => psi J x)
    (hD b)
    (fun _ => abs_nonneg _) hpsi_x M (fun J => hbound J x)
  simp only [valueWindowIntensity, dite_eq_left hx] at hp hm ⊢
  rw [valueSignedWindowIntensity, dite_eq_left hx]
  exact (weighted_integral_parts (volume.restrict K) _ _ _ _
    ((physicalValuePdf_measurable (n+1) μ Q).mul hpp).aemeasurable
    ((physicalValuePdf_measurable (n+1) μ Q).mul hpm).aemeasurable
    hp hm (fun b => (hj b).2.2.2)).2

/-- The full signed pure marked Kac--Rice formula. Both the literal critical
sum and the actual iterated posterior intensity are integrable. -/
theorem actual_pure_signed_score_window_kacRice (n : ℕ) (hn : 1 ≤ n)
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree → Vector (n+1) → ℝ)
    (hpsi : Measurable fun z : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree ×
      Vector (n+1) => psi z.1 z.2)
    (M : ℝ) (hbound : ∀ J x, |psi J x| ≤ M) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (actualSignedScoreWindowCount n c K psi) (disorderLaw (n+1) μ.maxDegree) ∧
    Integrable (valueSignedWindowIntensity n μ Q (pureScoreWindow p K) psi) (sphereLaw (n+1)) ∧
    (∫ J, actualSignedScoreWindowCount n c K psi J ∂disorderLaw (n+1) μ.maxDegree) =
      (sphereKRPrefactor n μ Q).toReal *
        ∫ x, valueSignedWindowIntensity n μ Q (pureScoreWindow p K) psi x ∂sphereLaw (n+1) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let fp := valueWindowIntensity n μ Q (pureScoreWindow p K) (fun J x => ENNReal.ofReal (psi J x))
  let fm := valueWindowIntensity n μ Q (pureScoreWindow p K) (fun J x => ENNReal.ofReal (-psi J x))
  have hkp := (actual_pure_score_window_kacRice n hn p hp alpha halpha hQ K hK
    (fun J x => ENNReal.ofReal (psi J x)) hpsi.ennreal_ofReal).2
  have hkm := (actual_pure_score_window_kacRice n hn p hp alpha halpha hQ K hK
    (fun J x => ENNReal.ofReal (-psi J x)) hpsi.neg.ennreal_ofReal).2
  have hcp := bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K
    (fun J x => ENNReal.ofReal (psi J x)) (ENNReal.ofReal M) ENNReal.ofReal_lt_top
    (fun J x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hbound J x)))
  have hm := bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K
    (fun J x => ENNReal.ofReal (-psi J x)) (ENNReal.ofReal M) ENNReal.ofReal_lt_top
    (fun J x => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hbound J x)))
  have hfp : Measurable fp := valueWindowIntensity_measurable n μ hQ (pureScoreWindow p K) _ hpsi.ennreal_ofReal
  have hfm : Measurable fm := valueWindowIntensity_measurable n μ hQ (pureScoreWindow p K) _ hpsi.neg.ennreal_ofReal
  have hfpi := lintegral_lt_top_of_prefactor (sphereLaw (n+1)) fp
    (sphereKRPrefactor_ne_zero n μ hQ) hcp hkp
  have hfmi := lintegral_lt_top_of_prefactor (sphereLaw (n+1)) fm
    (sphereKRPrefactor_ne_zero n μ hQ) hm hkm
  have he : valueSignedWindowIntensity n μ Q (pureScoreWindow p K) psi =ᵐ[sphereLaw (n+1)]
      (fun x => (fp x).toReal - (fm x).toReal) := by
    filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega),
      ae_lt_top' hfp.aemeasurable hfpi.ne, ae_lt_top' hfm.aemeasurable hfmi.ne] with x hx hpx hmx
    exact valueSignedWindowIntensity_parts n μ hQ (pureScoreWindow p K) psi hpsi M hbound x hx
      (fun b => pure_intrinsicDet_integrable (n := n) p hp alpha halpha hQ x hx b) hpx hmx
  have hj := integrable_toReal_sub_integral (sphereLaw (n+1)) fp fm
    hfp.aemeasurable hfm.aemeasurable hfpi hfmi
  have hc := actualSignedScoreWindowCount_integrable_parts n hn μ hQ K hK psi hpsi M hbound
  refine ⟨hc.1, hj.1.congr he.symm, ?_⟩
  rw [hc.2, hkp, hkm, integral_congr_ae he, hj.2,
    ENNReal.toReal_mul, ENNReal.toReal_mul, mul_sub]

/-- The pure formula in the manuscript's literal scalar-window notation. -/
theorem actual_pure_signed_value_window_kacRice (n : ℕ) (hn : 1 ≤ n)
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree → Vector (n+1) → ℝ)
    (hpsi : Measurable fun z : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree ×
      Vector (n+1) => psi z.1 z.2)
    (M : ℝ) (hbound : ∀ J x, |psi J x| ≤ M) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Integrable (actualSignedValueWindowCount n c (pureScoreWindow p K) psi)
      (disorderLaw (n+1) μ.maxDegree) ∧
    Integrable (valueSignedWindowIntensity n μ Q (pureScoreWindow p K) psi) (sphereLaw (n+1)) ∧
    (∫ J, actualSignedValueWindowCount n c (pureScoreWindow p K) psi J
      ∂disorderLaw (n+1) μ.maxDegree) =
      (sphereKRPrefactor n μ Q).toReal *
        ∫ x, valueSignedWindowIntensity n μ Q (pureScoreWindow p K) psi x ∂sphereLaw (n+1) := by
  have he := funext fun J =>
    actual_pure_signedScoreWindowCount_eq_valueWindowCount n p hp alpha halpha Q K psi J
  simpa only [he] using
    actual_pure_signed_score_window_kacRice n hn p hp alpha halpha hQ K hK psi hpsi M hbound

end
end SlowEquilibration.SphericalMarkedWindows
