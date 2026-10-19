-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalNormalizedMoments
public import SlowEquilibration.PureConditionedHessian
public import SlowEquilibration.SphericalSequentialRegression

/-! # Actual conditioned intrinsic determinant expectations and moments

The complete intrinsic Hessian under the actual whole-field posterior has the
proved shifted GOE law. Its literal own ordinary determinant expectation equals
μ_(N−1,N)(k), is positive, and normalizes the genuine all-dimension moments.
Both nonpure score conditioning and proper pure value conditioning are retained.
-/

@[expose] public section

namespace SlowEquilibration.ConditionedDeterminantMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian WholeFieldRegression
open IntrinsicHessianLaw ConditionedIntrinsicHessian PureConditionedHessian
open SphericalSequentialRegression GOERawMoments GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Literal absolute determinant of the actual intrinsic Hessian operator. -/
def intrinsicDet {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (x : Vector N)
    (J : Disorder N μ.maxDegree) : ℝ :=
  |(intrinsicHessian (field (centerCoefficients (mixtureCoefficients μ) Q) J) x).det|

/-- The actual canonical posterior at normalized nonpure value/radial marks. -/
def mixedLaw {n : ℕ} (μ : FiniteMixture) (Q : ℝ) (x : Vector (n + 2))
    (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    Measure (Disorder (n + 2) μ.maxDegree) :=
  coefficientKernel (jointCLM (centerCoefficients (mixtureCoefficients μ) Q) x (tangentFrame x hx))
    (jointScoreTarget (n + 1) (((n + 2 : ℕ) : ℝ) • z))

/-- The actual proper pure posterior, with redundant radial score omitted. -/
def pureLaw {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (h : ℝ) :
    Measure (Disorder (n + 2) (FiniteMixture.pure p hp alpha halpha).maxDegree) :=
  coefficientKernel (ValueTangentConditioning.valueTangentCLM
    (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q)
      x (tangentFrame x hx)) (valueTarget (n + 1) h)

lemma intrinsicMatrix_abs_det {n : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (J : Disorder (n + 2) μ.maxDegree) :
    |(intrinsicMatrix (centerCoefficients (mixtureCoefficients μ) Q) x hx J).det| = intrinsicDet μ Q x J := by
  rw [intrinsicMatrix, LinearMap.det_toMatrix]
  rfl

lemma shifted_abs_det (n : ℕ) (k : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    |(W - k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).det| = matrixAbsoluteDet n k W := by
  have he : W - k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = -(k • 1 - W) := by abel
  rw [he, Matrix.det_neg, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  rfl

lemma shifted_absdet_law {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω} (n : ℕ)
    (H : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (D : Ω → ℝ)
    (b k : ℝ)
    (hH : HasLaw H ((goeLaw (n + 1) (n + 2) b).map
      (fun W => W - k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))) η)
    (hD : ∀ ω, |(H ω).det| = D ω) :
    HasLaw D ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) η := by
  have hf : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => |W.det|) :=
    continuous_id.matrix_det.abs.measurable
  have hs : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => W - k • 1) := by fun_prop
  have h := (hasLaw_map hf.aemeasurable).fun_comp hH
  rw [Measure.map_map hf hs] at h
  simpa only [Function.comp_def, shifted_abs_det, hD] using h

/-- The posterior determinant itself has the literal canonical ordinary GOE
absolute determinant law at every specified nonpure null mark. -/
theorem mixed_intrinsicDet_hasLaw {n : ℕ} (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    HasLaw (intrinsicDet μ Q x)
      ((goeLaw (n + 1) (n + 2) (Q ^ 2 * μ.xi2 Q)).map (matrixAbsoluteDet n (z 1)))
      (mixedLaw μ Q x hx z) := by
  have hk : jointScoreTarget (n + 1) (((n + 2 : ℕ) : ℝ) • z) (Sum.inl 1) / (n + 2 : ℕ) = z 1 := by
    change (((n + 2 : ℕ) : ℝ) * z 1) / (n + 2 : ℕ) = _
    field_simp
  have h := conditioned_intrinsicMatrix_hasLaw μ hQ hnp x hx
    (jointScoreTarget (n + 1) (((n + 2 : ℕ) : ℝ) • z))
  simp only [hk] at h
  exact shifted_absdet_law n _ _ _ _ h (intrinsicMatrix_abs_det μ Q x hx)

/-- Proper pure conditioning yields the literal determinant law at k=ph. -/
theorem pure_intrinsicDet_hasLaw {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    HasLaw (intrinsicDet μ Q x)
      ((goeLaw (n + 1) (n + 2) (Q ^ 2 * μ.xi2 Q)).map (matrixAbsoluteDet n ((p : ℝ) * h)))
      (pureLaw p hp alpha halpha Q x hx h) := by
  dsimp only
  have hH := pure_hessian_at_normalized_value p hp alpha halpha hQ x hx h
  exact shifted_absdet_law n _ _ _ _ hH
    (intrinsicMatrix_abs_det (FiniteMixture.pure p hp alpha halpha) Q x hx)

/-- Exact ordinary expectation equality follows from the actual law, without
an expected-log or conditional-version premise. -/
theorem determinant_mean_eq_of_law {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω}
    {n : ℕ} {b k : ℝ} {D : Ω → ℝ}
    (hD : HasLaw D ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) η) :
    (∫ ω, D ω ∂η) = physicalMean n (n + 2) b k := by
  rw [hD.integral_eq]
  simpa only [id_eq, physicalMean] using
    (integral_map (φ := matrixAbsoluteDet n k) (f := id)
      (matrixAbsoluteDet_measurable n k).aemeasurable (aestronglyMeasurable_id (μ := (goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k))))

/-- Actual law transport preserves own ordinary expectation normalization,
positivity and moment integrability; no conditional moment is an input. -/
lemma conditional_moment_of_physical_law {Ω : Type*} [MeasurableSpace Ω]
    {η : Measure Ω} {n : ℕ} {b k r C : ℝ} {D : Ω → ℝ}
    (hD : HasLaw D ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) η)
    (hphysical : Integrable (matrixAbsoluteDet n k) (goeLaw (n + 1) (n + 2) b) ∧
      0 < physicalMean n (n + 2) b k ∧
      Integrable (fun W => (matrixAbsoluteDet n k W / physicalMean n (n + 2) b k) ^ r)
        (goeLaw (n + 1) (n + 2) b) ∧
      (∫ W, (matrixAbsoluteDet n k W / physicalMean n (n + 2) b k) ^ r
        ∂goeLaw (n + 1) (n + 2) b) ≤ C) :
    Integrable D η ∧ (∫ ω, D ω ∂η) = physicalMean n (n + 2) b k ∧
      0 < ∫ ω, D ω ∂η ∧
      Integrable (fun ω => (D ω / (∫ v, D v ∂η)) ^ r) η ∧
      (∫ ω, (D ω / (∫ v, D v ∂η)) ^ r ∂η) ≤ C := by
  have hmeas := matrixAbsoluteDet_measurable n k
  have hIntId : Integrable id ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) :=
    (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).mpr hphysical.1
  have hIntD : Integrable D η := by
    simpa only [Function.comp_def, id_eq] using hD.integrable_comp hIntId
  have hmean := determinant_mean_eq_of_law hD
  refine ⟨hIntD, hmean, by rw [hmean]; exact hphysical.2.1, ?_⟩
  rw [hmean]
  let f : ℝ → ℝ := fun y => (y / physicalMean n (n + 2) b k) ^ r
  have hf : Measurable f := (measurable_id.div_const _).pow_const r
  have hIntF : Integrable f ((goeLaw (n + 1) (n + 2) b).map (matrixAbsoluteDet n k)) :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas.aemeasurable).mpr hphysical.2.2.1
  refine ⟨hD.integrable_comp hIntF, ?_⟩
  have he := hD.integral_comp hf.aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable] at he
  exact he.trans_le hphysical.2.2.2

/-- Every actual conditioned nonpure spherical determinant has the source
positive ordinary mean and uniform all-dimension normalized moment bound. -/
theorem mixed_conditioned_determinant_moments (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z r : ℝ} (hg : 0 < g) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : Vector (n + 2))
      (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)),
      2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) + g ≤ z 1 → z 1 ≤ Z →
      Integrable (intrinsicDet μ Q x) (mixedLaw μ Q x hx z) ∧
      (∫ J, intrinsicDet μ Q x J ∂mixedLaw μ Q x hx z) = physicalMean n (n + 2) (Q ^ 2 * μ.xi2 Q) (z 1) ∧
      0 < ∫ J, intrinsicDet μ Q x J ∂mixedLaw μ Q x hx z ∧
      Integrable (fun J => (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂mixedLaw μ Q x hx z)) ^ r) (mixedLaw μ Q x hx z) ∧
      (∫ J, (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂mixedLaw μ Q x hx z)) ^ r ∂mixedLaw μ Q x hx z) ≤ C := by
  have hb : 0 < Q ^ 2 * μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨C, hC, h⟩ := normalized_physical_moments 1 (Z := Z) hb hg hr
  refine ⟨C, hC, ?_⟩
  intro n x hx z hk hZ
  exact conditional_moment_of_physical_law (mixed_intrinsicDet_hasLaw μ hQ hnp x hx z)
    (h n (z 1) hk hZ)

/-- The same actual own-mean normalization in the pure model, under its
proper H=Nh/gradient=0 posterior and with the required shift k=ph. -/
theorem pure_conditioned_determinant_moments (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    {g Z r : ℝ} (hg : 0 < g) (hr : 0 ≤ r) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : Vector (n + 2))
      (hx : ‖x‖ ^ 2 = (n + 2 : ℕ)) (h : ℝ),
      2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) + g ≤ (p : ℝ) * h → (p : ℝ) * h ≤ Z →
      Integrable (intrinsicDet μ Q x) (pureLaw p hp alpha halpha Q x hx h) ∧
      (∫ J, intrinsicDet μ Q x J ∂pureLaw p hp alpha halpha Q x hx h) = physicalMean n (n + 2) (Q ^ 2 * μ.xi2 Q) ((p : ℝ) * h) ∧
      0 < ∫ J, intrinsicDet μ Q x J ∂pureLaw p hp alpha halpha Q x hx h ∧
      Integrable (fun J => (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂pureLaw p hp alpha halpha Q x hx h)) ^ r) (pureLaw p hp alpha halpha Q x hx h) ∧
      (∫ J, (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂pureLaw p hp alpha halpha Q x hx h)) ^ r ∂pureLaw p hp alpha halpha Q x hx h) ≤ C := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  have hb : 0 < Q ^ 2 * μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨C, hC, hbound⟩ := normalized_physical_moments 1 (Z := Z) hb hg hr
  refine ⟨C, hC, ?_⟩
  intro n x hx h hk hZ
  exact conditional_moment_of_physical_law (pure_intrinsicDet_hasLaw p hp alpha halpha hQ x hx h)
    (hbound n ((p : ℝ) * h) hk hZ)

/-- Sharp source large-dimension normalized moments under the actual nonpure
whole-field posterior, uniformly over every mark above the physical edge gap. -/
theorem mixed_conditioned_determinant_moments_sharp_eventually (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ))
      (z : EuclideanSpace ℝ (Fin 2)), 2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) + g ≤ z 1 →
      ∀ r : ℝ, 0 ≤ r →
      Integrable (intrinsicDet μ Q x) (mixedLaw μ Q x hx z) ∧
      (∫ J, intrinsicDet μ Q x J ∂mixedLaw μ Q x hx z) = physicalMean n (n + 2) (Q ^ 2 * μ.xi2 Q) (z 1) ∧
      0 < ∫ J, intrinsicDet μ Q x J ∂mixedLaw μ Q x hx z ∧
      Integrable (fun J => (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂mixedLaw μ Q x hx z)) ^ r) (mixedLaw μ Q x hx z) ∧
      (∫ J, (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂mixedLaw μ Q x hx z)) ^ r ∂mixedLaw μ Q x hx z) ≤
          (2 : ℝ) ^ r * Real.exp (4 * (Q ^ 2 * μ.xi2 Q) * r ^ 2 / g ^ 2) := by
  have hb : 0 < Q ^ 2 * μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  filter_upwards [normalized_physical_moments_sharp_eventually 1 hb hg] with n hn
  intro x hx z hk r hr
  obtain ⟨C, hC, hraw⟩ := GOEPhysicalPrefactors.physical_moments_prefactors 1
    (Z := z 1) hb hg (by norm_num : (0 : ℝ) ≤ 1)
  have hInt : Integrable (matrixAbsoluteDet n (z 1)) (goeLaw (n + 1) (n + 2) (Q ^ 2 * μ.xi2 Q)) := by
    simpa only [Real.rpow_one] using (hraw n (z 1) hk le_rfl).1
  have hpos := physicalMean_pos n 1 hb (by linarith : 2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) < z 1)
  exact conditional_moment_of_physical_law (mixed_intrinsicDet_hasLaw μ hQ hnp x hx z)
    ⟨hInt, hpos, (hn (z 1) hk r hr).1, (hn (z 1) hk r hr).2⟩

/-- Sharp source large-dimension moments for the genuine proper pure posterior,
with k=ph and with its actual own determinant expectation as denominator. -/
theorem pure_conditioned_determinant_moments_sharp_eventually (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᶠ n : ℕ in atTop, ∀ (x : Vector (n + 2)) (hx : ‖x‖ ^ 2 = (n + 2 : ℕ))
      (h : ℝ), 2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) + g ≤ (p : ℝ) * h →
      ∀ r : ℝ, 0 ≤ r →
      Integrable (intrinsicDet μ Q x) (pureLaw p hp alpha halpha Q x hx h) ∧
      (∫ J, intrinsicDet μ Q x J ∂pureLaw p hp alpha halpha Q x hx h) = physicalMean n (n + 2) (Q ^ 2 * μ.xi2 Q) ((p : ℝ) * h) ∧
      0 < ∫ J, intrinsicDet μ Q x J ∂pureLaw p hp alpha halpha Q x hx h ∧
      Integrable (fun J => (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂pureLaw p hp alpha halpha Q x hx h)) ^ r) (pureLaw p hp alpha halpha Q x hx h) ∧
      (∫ J, (intrinsicDet μ Q x J /
        (∫ K, intrinsicDet μ Q x K ∂pureLaw p hp alpha halpha Q x hx h)) ^ r ∂pureLaw p hp alpha halpha Q x hx h) ≤
          (2 : ℝ) ^ r * Real.exp (4 * (Q ^ 2 * μ.xi2 Q) * r ^ 2 / g ^ 2) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  have hb : 0 < Q ^ 2 * μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  filter_upwards [normalized_physical_moments_sharp_eventually 1 hb hg] with n hn
  intro x hx h hk r hr
  obtain ⟨C, hC, hraw⟩ := GOEPhysicalPrefactors.physical_moments_prefactors 1
    (Z := (p : ℝ) * h) hb hg (by norm_num : (0 : ℝ) ≤ 1)
  have hInt : Integrable (matrixAbsoluteDet n ((p : ℝ) * h)) (goeLaw (n + 1) (n + 2) (Q ^ 2 * μ.xi2 Q)) := by
    simpa only [Real.rpow_one] using (hraw n ((p : ℝ) * h) hk le_rfl).1
  have hpos := physicalMean_pos n 1 hb (by linarith : 2 * Real.sqrt (Q ^ 2 * μ.xi2 Q) < (p : ℝ) * h)
  exact conditional_moment_of_physical_law (pure_intrinsicDet_hasLaw p hp alpha halpha hQ x hx h)
    ⟨hInt, hpos, (hn ((p : ℝ) * h) hk r hr).1, (hn ((p : ℝ) * h) hk r hr).2⟩

end
end SlowEquilibration.ConditionedDeterminantMoments
