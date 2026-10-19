-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLocalMaxima

/-! Exact Kac--Rice intensities and uniform exterior window bounds for
literal local maxima of the actual field on the actual sphere. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalMorse NegativeDefiniteOperators SphericalSequentialRegression
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal local-maximum count. Criticality and Hessian signs are not
part of its definition. -/
def actualLocalMaxCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' _x : {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧
    IsLocalMaxOn (field c J) {y | ‖y‖^2=(n+1 : ℕ)} x ∧ actualScore c J x ∈ K}, (1 : ℝ≥0∞)

lemma actualLocalMaxCount_eq_negative_of_iff {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (J : Disorder (n+1) P)
    (h : ∀ x : Vector (n+1), ‖x‖^2=(n+1 : ℕ) →
      (IsLocalMaxOn (field c J) {y | ‖y‖^2=(n+1 : ℕ)} x ↔
        surfaceGradient (field c J) x=0 ∧ NegativeDefinite (intrinsicHessian (field c J) x))) :
    actualLocalMaxCount n c K J = actualNegativeCriticalCount n c K J := by
  have he : {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧
      IsLocalMaxOn (field c J) {y | ‖y‖^2=(n+1 : ℕ)} x ∧ actualScore c J x ∈ K} =
      {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧ surfaceGradient (field c J) x=0 ∧
        actualScore c J x ∈ K ∧ NegativeDefinite (intrinsicHessian (field c J) x)} := by
    ext x
    by_cases hx : ‖x‖^2=(n+1 : ℕ)
    · simp only [mem_ofPred_eq,hx,true_and,h x hx]
      tauto
    · simp only [mem_ofPred_eq,hx,false_and]
  unfold actualLocalMaxCount actualNegativeCriticalCount
  rw [he]

theorem actualLocalMaxCount_eq_negative_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (K : Set (EuclideanSpace ℝ (Fin 2))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    actualLocalMaxCount n c K =ᵐ[disorderLaw (n+1) μ.maxDegree] actualNegativeCriticalCount n c K := by
  filter_upwards [actual_sphere_localMax_iff_negative_ae n hn μ hQ] with J hJ
  exact actualLocalMaxCount_eq_negative_of_iff n _ K J hJ

theorem actual_sphere_localMaxSet_finite_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧
        IsLocalMaxOn (field c J) {y | ‖y‖^2=(n+1 : ℕ)} x}.Finite := by
  filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ,
    actual_sphere_localMax_iff_negative_ae n hn μ hQ] with J hfinite hiff
  apply hfinite.subset
  intro x hx
  exact ⟨hx.1,((hiff x hx.1).mp hx.2).1⟩

theorem actual_mixed_localMax_count_intensity (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualLocalMaxCount (n+1) c K) (disorderLaw (n+2) μ.maxDegree) ∧
    (∫⁻ J, actualLocalMaxCount (n+1) c K J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ z in K, mixedNegativeIntensity n μ Q z := by
  have he := actualLocalMaxCount_eq_negative_ae (n+1) (by omega) μ hQ K
  have hn := actual_mixed_negative_count_intensity n μ hQ hnp K hK
  exact ⟨hn.1.congr he.symm,(lintegral_congr_ae he).trans hn.2⟩

theorem actual_pure_localMax_count_intensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualLocalMaxCount (n+1) c K) (disorderLaw (n+2) μ.maxDegree) ∧
    (∫⁻ J, actualLocalMaxCount (n+1) c K J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ h in pureScoreWindow p K, pureNegativeIntensity n p hp alpha halpha Q h := by
  have he := actualLocalMaxCount_eq_negative_ae (n+1) (by omega) (FiniteMixture.pure p hp alpha halpha) hQ K
  have hn := actual_pure_negative_count_intensity n p hp alpha halpha hQ K hK
  exact ⟨hn.1.congr he.symm,(lintegral_congr_ae he).trans hn.2⟩

theorem actual_mixed_localMax_window_prefactors (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ z ∈ K, z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let a := centerCoefficients (mixtureCoefficients μ) Q
      ENNReal.ofReal (c * (n+2 : ℕ)) *
        (∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * markedComplexity μ Q z))) ≤
          (∫⁻ J, actualLocalMaxCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualLocalMaxCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * (n+2 : ℕ)) *
          ∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_mixed_negative_window_prefactors μ hQ hnp (Z := Z) hg
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro K hK hgap
  dsimp only
  rw [lintegral_congr_ae (actualLocalMaxCount_eq_negative_ae (n+1) (by omega) μ hQ K)]
  exact hn K hK hgap

theorem actual_pure_localMax_window_prefactors (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ h ∈ pureScoreWindow p K, (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let a := centerCoefficients (mixtureCoefficients μ) Q
      ENNReal.ofReal (c * Real.sqrt (n+2 : ℕ)) *
        (∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
          (Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h))) ≤
        (∫⁻ J, actualLocalMaxCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualLocalMaxCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * Real.sqrt (n+2 : ℕ)) *
          ∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
            (Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_pure_negative_window_prefactors p hp alpha halpha hQ (Z := Z) hg
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro K hK hgap
  dsimp only
  rw [lintegral_congr_ae (actualLocalMaxCount_eq_negative_ae (n+1) (by omega)
    (FiniteMixture.pure p hp alpha halpha) hQ K)]
  exact hn K hK hgap

end
end SlowEquilibration.SphericalMarkedWindows
