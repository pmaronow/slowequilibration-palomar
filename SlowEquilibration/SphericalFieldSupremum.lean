-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpatialRegularity
public import SlowEquilibration.GaussianNormConcentration

@[expose] public section

/-!
# Linear-in-dimension bounds for the actual spherical field supremum

The spatial feature increment bound gives a genuine compact
Sudakov--Fernique comparison with a linear spherical Gaussian field.
Gaussian concentration then controls the supremum of the actual tensor
realization, without a regularity or ground-state estimate as a premise.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open GaussianCompactMaximum
open scoped Topology BigOperators InnerProductSpace ENNReal

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev SpinSphere (n : ℕ) := ↥(Metric.sphere (0 : Vector (n+1)) (Real.sqrt ((n+1 : ℕ) : ℝ)))

instance spinSphere_nonempty (n : ℕ) : Nonempty (SpinSphere n) :=
  (NormedSpace.sphere_nonempty.mpr (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))).coe_sort

instance spinSphere_compact (n : ℕ) : CompactSpace (SpinSphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Vector (n+1)) (Real.sqrt ((n+1 : ℕ) : ℝ)))

theorem spinSphere_norm {n : ℕ} (x : SpinSphere n) : ‖(x : Vector (n+1))‖ = Real.sqrt ((n+1 : ℕ) : ℝ) := by
  simpa only [Metric.mem_sphere,dist_zero_right] using x.property

theorem spinSphere_norm_sq {n : ℕ} (x : SpinSphere n) : ‖(x : Vector (n+1))‖^2=((n+1 : ℕ) : ℝ) := by
  rw [spinSphere_norm,Real.sq_sqrt (by positivity)]

def sphericalFieldSupremum {n P : ℕ} (c : Degree P → ℝ) (σ : ℝ)
    (J : Disorder (n+1) P) : ℝ := ⨆ x : SpinSphere n, σ*field c J x

theorem signedFeatureSupremum_eq {n P : ℕ} (c : Degree P → ℝ) (σ : ℝ)
    (g : EuclideanDisorder (n+1) P) :
    (⨆ x : SpinSphere n, inner ℝ (σ • fieldFeature c (x : Vector (n+1))) g) =
      sphericalFieldSupremum c σ (unpackDisorder g) := by
  unfold sphericalFieldSupremum
  congr 1
  funext x
  rw [real_inner_smul_left,real_inner_comm,fieldFeature_inner]

theorem signedFeature_operator_bound {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {σ : ℝ} (hσ : |σ|=1) (x : SpinSphere n) :
    ‖innerSL ℝ (σ • fieldFeature c (x : Vector (n+1)))‖ ≤ Real.sqrt (((n+1 : ℕ) : ℝ)*covariancePolynomial c 1) := by
  rw [innerSL_apply_norm,norm_smul,Real.norm_eq_abs,hσ,one_mul,
    fieldFeature_norm (by omega) c hc (x : Vector (n+1)) (spinSphere_norm_sq x)]

theorem signedFeatureSupremum_lipschitz {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {σ : ℝ} (hσ : |σ|=1) :
    LipschitzWith (Real.sqrt (((n+1 : ℕ) : ℝ)*covariancePolynomial c 1)).toNNReal
      (fun g : EuclideanDisorder (n+1) P => ⨆ x : SpinSphere n, inner ℝ (σ • fieldFeature c (x : Vector (n+1))) g) := by
  classical
  exact field_supremum_lipschitz (fun x : SpinSphere n => innerSL ℝ (σ • fieldFeature c (x : Vector (n+1))))
    (signedFeature_operator_bound (n := n) c hc hσ)

theorem featureSupremum_integrable_of_continuous {V ι : Type*} [Fintype ι]
    [TopologicalSpace V] [CompactSpace V] [Nonempty V]
    (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    Integrable (fun g => ⨆ v, inner ℝ (a v) g) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  classical
  obtain ⟨K,hK,hb⟩ := exists_feature_bound (fun v => innerSL ℝ (a v)) ((innerSL ℝ).continuous.comp ha)
  apply (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul K).mono'
    (field_supremum_lipschitz (fun v => innerSL ℝ (a v)) hb).continuous.aestronglyMeasurable
  exact .of_forall fun g => norm_field_supremum_le (fun v => innerSL ℝ (a v)) hb g

/-- Actual Gaussian expected supremum bounded at the correct O(N) scale,
proved from feature increments and a genuine linear-field comparison. -/
theorem signedFeatureSupremum_mean_le {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {σ : ℝ} (hσ : |σ|=1) :
    (∫ g : EuclideanDisorder (n+1) P, (⨆ x : SpinSphere n, inner ℝ (σ • fieldFeature c (x : Vector (n+1))) g)
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+1) P)) ≤
        Real.sqrt (spatialVariance c)*((n+1 : ℕ) : ℝ) := by
  classical
  let a : SpinSphere n → EuclideanDisorder (n+1) P := fun x => σ • fieldFeature c (x : Vector (n+1))
  let b : SpinSphere n → Vector (n+1) := fun x => Real.sqrt (spatialVariance c) • (x : Vector (n+1))
  have ha : Continuous a := by
    dsimp [a]
    exact ((fieldFeature_continuous (N := n+1) c).comp continuous_subtype_val).const_smul σ
  have hb : Continuous b := by
    dsimp [b]
    exact (continuous_subtype_val : Continuous (Subtype.val : SpinSphere n → Vector (n+1))).const_smul (Real.sqrt (spatialVariance c))
  have hinc (x y : SpinSphere n) : ‖a x-a y‖ ≤ ‖b x-b y‖ := by
    dsimp [a,b]
    rw [← smul_sub,← smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hσ,one_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact fieldFeature_dist_le (by omega) c hc (x : Vector (n+1)) (y : Vector (n+1)) (spinSphere_norm_sq x) (spinSphere_norm_sq y)
  have hcomp := GaussianCompactFeatureComparison.expected_supremum_comparison_of_increment_norm a b ha hb hinc
  have hup := integral_mono (featureSupremum_integrable_of_continuous b hb)
    (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul
      (Real.sqrt (spatialVariance c)*Real.sqrt ((n+1 : ℕ) : ℝ))) (fun g => by
        apply ciSup_le
        intro x
        have hh := real_inner_le_norm (b x) g
        simpa only [b,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),spinSphere_norm] using hh)
  rw [integral_const_mul] at hup
  have hn := GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card (Fin (n+1))
  simp only [Fintype.card_fin] at hn
  have hm := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (Real.sqrt_nonneg (spatialVariance c)) (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ)))
  have he : Real.sqrt (spatialVariance c)*Real.sqrt ((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ) =
      Real.sqrt (spatialVariance c)*((n+1 : ℕ) : ℝ) := by
    rw [mul_assoc,← sq,Real.sq_sqrt (by positivity)]
  rw [he] at hm
  exact hcomp.trans (hup.trans hm)

theorem signed_field_le_supremum {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    {σ : ℝ} (hσ : |σ|=1) (J : Disorder (n+1) P) (x : SpinSphere n) :
    σ*field c J x ≤ sphericalFieldSupremum c σ J := by
  have h := le_field_supremum (fun v : SpinSphere n => innerSL ℝ (σ • fieldFeature c (v : Vector (n+1))))
    (signedFeature_operator_bound c hc hσ) (euclideanDisorder J) x
  simp only [innerSL_apply_apply] at h
  rw [signedFeatureSupremum_eq,unpack_euclideanDisorder,real_inner_smul_left,real_inner_comm,
    fieldFeature_inner,unpack_euclideanDisorder] at h
  exact h

/-- Actual finite-volume exponentially small upper tail for either sign
of the true tensor-field supremum, at its proved linear mean scale. -/
theorem sphericalFieldSupremum_upper_tail {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    {σ t : ℝ} (hσ : |σ|=1) (ht : 0 ≤ t) :
    disorderLaw (n+1) P {J | (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤
      sphericalFieldSupremum c σ J} ≤
        ENNReal.ofReal (Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*covariancePolynomial c 1))) := by
  let F : EuclideanDisorder (n+1) P → ℝ := fun g =>
    ⨆ x : SpinSphere n, inner ℝ (σ • fieldFeature c (x : Vector (n+1))) g
  let L : ℝ := Real.sqrt (((n+1 : ℕ) : ℝ)*covariancePolynomial c 1)
  have hLip : LipschitzWith L.toNNReal F := signedFeatureSupremum_lipschitz c hc hσ
  have hmean := signedFeatureSupremum_mean_le (n := n) c hc hσ
  have htail := GaussianNormConcentration.centered_lipschitz_upper_tail F
    (Real.sqrt_nonneg _) hLip (mul_nonneg ht (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity))
  have hr : (SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+1) P)).real
      {g | (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ F g} ≤
      Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*covariancePolynomial c 1)) := by
    have hs : {g | (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ F g} ⊆
        {g | (∫ h, F h ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+1) P))+
          t*((n+1 : ℕ) : ℝ) ≤ F g} := by
      intro g hg
      change _ ≤ F g
      change _ ≤ F g at hg
      dsimp only [F] at *
      nlinarith
    have he : -(t*((n+1 : ℕ) : ℝ))^2/(2*L^2) =
        -(t^2*((n+1 : ℕ) : ℝ))/(2*covariancePolynomial c 1) := by
      dsimp [L]
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    rw [he] at htail
    exact (measureReal_mono hs).trans htail
  have hp : SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+1) P)
      {g | (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ F g} ≤
      ENNReal.ofReal (Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*covariancePolynomial c 1))) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact hr
  have hlaw := euclideanDisorder_hasLaw (n+1) P
  rw [← hlaw.map_eq,Measure.map_apply_of_aemeasurable hlaw.aemeasurable
    (measurableSet_le measurable_const hLip.continuous.measurable)] at hp
  simpa only [Set.preimage_ofPred_eq,F,signedFeatureSupremum_eq,unpack_euclideanDisorder] using hp

/-- A true linear-in-dimension bound for the absolute tensor field over
the entire sphere, with an exponential finite-volume failure probability. -/
theorem spherical_field_uniform_upper_tail {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1) {t : ℝ} (ht : 0 ≤ t) :
    disorderLaw (n+1) P {J | ∃ x : Vector (n+1), ‖x‖^2=((n+1 : ℕ) : ℝ) ∧
      (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ |field c J x|} ≤
        ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*covariancePolynomial c 1))) := by
  have hsub : {J | ∃ x : Vector (n+1), ‖x‖^2=((n+1 : ℕ) : ℝ) ∧
      (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ |field c J x|} ⊆
      {J | (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ sphericalFieldSupremum c 1 J} ∪
      {J | (Real.sqrt (spatialVariance c)+t)*((n+1 : ℕ) : ℝ) ≤ sphericalFieldSupremum c (-1) J} := by
    rintro J ⟨x,hx,hJ⟩
    let v : SpinSphere n := ⟨x,by
      rw [Metric.mem_sphere,dist_zero_right,← hx,Real.sqrt_sq (norm_nonneg _)]⟩
    rcases le_abs.mp hJ with hp | hm
    · left
      exact hp.trans (by simpa using signed_field_le_supremum c hc (by norm_num : |(1 : ℝ)|=1) J v)
    · right
      exact hm.trans (by simpa using signed_field_le_supremum c hc (by norm_num : |(-1 : ℝ)|=1) J v)
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  have hh := add_le_add
    (sphericalFieldSupremum_upper_tail (n := n) c hc hcov (by norm_num : |(1 : ℝ)|=1) ht)
    (sphericalFieldSupremum_upper_tail (n := n) c hc hcov (by norm_num : |(-1 : ℝ)|=1) ht)
  simpa only [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _),← two_mul] using hh

end SlowEquilibration.SphericalModel
