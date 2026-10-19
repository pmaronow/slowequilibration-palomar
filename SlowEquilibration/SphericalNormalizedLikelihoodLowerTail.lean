-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralHSMoments
public import SlowEquilibration.GaussianFeatureAffineSupport
public import SlowEquilibration.GaussianFeatureMomentTail
public import SlowEquilibration.SphericalLikelihoodTransfer

@[expose] public section

/-! Genuine dimension-uniform lower tails of the normalized spherical
partition, including quadratic and odd mixed models throughout beta<beta_s.
The actual HS mass and feature moments supply the Gaussian affine support;
no pressure limit, tightness premise or HMP theorem is assumed. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unpack_measurable (N P : ℕ) :
    Measurable (unpackDisorder (N:=N) (P:=P)) := by
  unfold unpackDisorder
  fun_prop

/-- The inverse flattening has exactly the original ordered tensor law. -/
theorem unpackDisorder_hasLaw (N P : ℕ) :
    HasLaw (unpackDisorder (N:=N) (P:=P)) (disorderLaw N P)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) := by
  refine ⟨(unpack_measurable N P).aemeasurable,?_⟩
  rw [← (euclideanDisorder_hasLaw N P).map_eq,
    Measure.map_map (unpack_measurable N P) (by unfold euclideanDisorder flatDisorder; fun_prop)]
  have he : (unpackDisorder ∘ euclideanDisorder : Disorder N P → Disorder N P)=id := rfl
  rw [he,Measure.map_id]

/-- The actual physical partition has the affine support obtained from any
fixed Borel spin section of a genuine disorder-dependent truncation. -/
theorem logPartition_truncated_affine_support {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀p,0 ≤ c p) {β : ℝ} (hβ : 0 ≤ β)
    {T : Set (Disorder N P×Vector N)} (hT : MeasurableSet T)
    (g h : EuclideanDisorder N P)
    (hz : 0<truncatedPartition c β T (unpackDisorder g)) :
    Real.log (truncatedPartition c β T (unpackDisorder g))-
      (‖truncatedFeatureMean c β T (unpackDisorder g)‖/
        truncatedPartition c β T (unpackDisorder g))*dist h g ≤
      Real.log (partition N β (field c (unpackDisorder h))) := by
  let A := fun x : Vector N => β • fieldFeature c x
  let U : Set (Vector N) := {x | (unpackDisorder g,x)∈T}
  let M := β*Real.sqrt ((N:ℝ)*covariancePolynomial c 1)
  have hAm : Measurable A := ((fieldFeature_continuous c).const_smul β).measurable
  have hbound : ∀ᵐx ∂sphereLaw N,‖A x‖ ≤ M := by
    filter_upwards [sphereLaw_support hN] with x hx
    dsimp [A,M]
    rw [norm_smul,Real.norm_of_nonneg hβ,fieldFeature_norm hN c hc x hx]
  have hU : MeasurableSet U := hT.preimage (measurable_const.prodMk measurable_id)
  have hf (k : EuclideanDisorder N P) (x : Vector N) :
      inner ℝ k (A x)=β*field c (unpackDisorder k) x := by
    dsimp [A]
    rw [real_inner_smul_right,fieldFeature_inner]
  have hzEq : (∫x,U.indicator (fun y => Real.exp (inner ℝ g (A y))) x ∂sphereLaw N)=
      truncatedPartition c β T (unpackDisorder g) := by
    unfold truncatedPartition
    apply integral_congr_ae
    exact .of_forall fun x => by
      by_cases hx : (unpackDisorder g,x)∈T <;> simp [U,hx,hf]
  have hvEq : (∫x,U.indicator (fun y => Real.exp (inner ℝ g (A y)) • A y) x ∂sphereLaw N)=
      truncatedFeatureMean c β T (unpackDisorder g) := by
    unfold truncatedFeatureMean
    apply integral_congr_ae
    exact .of_forall fun x => by
      by_cases hx : (unpackDisorder g,x)∈T <;> simp [U,A,hx,hf]
  have hpart : (∫x,Real.exp (inner ℝ h (A x)) ∂sphereLaw N)=partition N β (field c (unpackDisorder h)) := by
    unfold partition
    simp_rw [hf]
  have hh := GaussianFeatureAffineSupport.log_partition_lower_support
    (sphereLaw N) A hAm (mul_nonneg hβ (Real.sqrt_nonneg _)) hbound U hU g h (hzEq.symm ▸ hz)
  rw [hzEq,hvEq,hpart] at hh
  have hi : -‖h-g‖*‖truncatedFeatureMean c β T (unpackDisorder g)‖ ≤
      inner ℝ (h-g) (truncatedFeatureMean c β T (unpackDisorder g)) :=
    by simpa only [neg_mul] using
      (neg_le_of_abs_le (abs_real_inner_le_norm (h-g) (truncatedFeatureMean c β T (unpackDisorder g))))
  have hid := div_le_div_of_nonneg_right hi hz.le
  rw [dist_eq_norm]
  apply le_trans _ hh
  convert add_le_add_left hid (Real.log (truncatedPartition c β T (unpackDisorder g))) using 1 <;> ring

/-- The proved mass/feature moments imply a genuine finite-N lower-tail bound
for the actual physical partition, with constants chosen before N. -/
theorem general_logPartition_lower_tail (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    ∃C K : ℝ,0<C ∧ 0<K ∧ ∀ᶠ n : ℕ in atTop,∀s : ℝ,0 ≤ s →
      (disorderLaw (n+1) μ.maxDegree).real {J |
        Real.log (mixturePartition μ β J) ≤
          annealedExponent (n+1) (mixtureCoefficients μ) β-C-K*s} ≤ Real.exp (-s^2/2) := by
  obtain ⟨δ,η,B,D,hδ,hη,hB,hD,hmoments⟩ := general_hs_normalized_moments μ hβ hβs
  refine ⟨GaussianFeatureMomentTail.tailOffset B D,GaussianFeatureMomentTail.tailSlope B D,
    GaussianFeatureMomentTail.tailOffset_pos hB hD,GaussianFeatureMomentTail.tailSlope_pos hB hD,?_⟩
  filter_upwards [hmoments] with n hn
  intro s hs
  let N := n+1
  let c := mixtureCoefficients μ
  let A := annealedExponent N c β
  let T := hsTruncation (N:=N) c β δ (A-(N:ℝ)*η)
  let Y₀ := fun J : Disorder N μ.maxDegree => Real.exp (-A)*truncatedPartition c β T J
  let V₀ := fun J : Disorder N μ.maxDegree => Real.exp (-A) • truncatedFeatureMean c β T J
  let Y := fun g : EuclideanDisorder N μ.maxDegree => Y₀ (unpackDisorder g)
  let V := fun g : EuclideanDisorder N μ.maxDegree => V₀ (unpackDisorder g)
  let f := fun g : EuclideanDisorder N μ.maxDegree => Real.log (partition N β (field c (unpackDisorder g)))
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hc := mixtureCoefficients_nonnegative μ
  have hT : MeasurableSet T := hsTruncation_measurable c β δ _
  have hLaw := unpackDisorder_hasLaw N μ.maxDegree
  have hY₀m : Measurable Y₀ := measurable_const.mul (truncatedPartition_measurable c β hT)
  have hV₀m : Measurable V₀ := (measurable_const (a:=Real.exp (-A))).smul (truncatedFeatureMean_measurable c β hT)
  have hYm : Measurable Y := hY₀m.comp (unpack_measurable N μ.maxDegree)
  have hVm : Measurable V := hV₀m.comp (unpack_measurable N μ.maxDegree)
  have hY₀i : Integrable Y₀ (disorderLaw N μ.maxDegree) :=
    (truncatedPartition_integrable hN c hc β hT).const_mul _
  have hY₀2i : Integrable (fun J => Y₀ J^2) (disorderLaw N μ.maxDegree) := by
    convert (truncatedPartition_sq_integrable hN c hc β hT).const_mul ((Real.exp (-A))^2) using 1
    funext J
    ring
  have hV₀2i := normalized_hsTruncatedFeatureMean_integrable hN c hc hβ.le δ η
  have hYi : Integrable Y (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) := hLaw.integrable_comp hY₀i
  have hY2i : Integrable (fun g => Y g^2) (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
    hLaw.integrable_comp hY₀2i
  have hV2i : Integrable (fun g => ‖V g‖^2) (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
    hLaw.integrable_comp hV₀2i
  have hY0 : ∀ᵐg ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree),0 ≤ Y g :=
    .of_forall fun g => mul_nonneg (Real.exp_pos _).le (truncatedPartition_nonneg c β T _)
  have hYmean := hLaw.integral_comp hY₀m.aestronglyMeasurable
  have hY2mean := hLaw.integral_comp (hY₀m.pow_const 2).aestronglyMeasurable
  have hV2mean := hLaw.integral_comp (hV₀m.norm.pow_const 2).aestronglyMeasurable
  dsimp only [Function.comp_apply] at hYmean hY2mean hV2mean
  have hMean : (1/2:ℝ) ≤ ∫g,Y g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) := by
    rw [hYmean]
    exact hn.1
  have hSecond : (∫g,Y g^2 ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) ≤ B := by
    rw [hY2mean]
    exact hn.2.1
  have hFeature : (∫g,‖V g‖^2 ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) ≤ D := by
    rw [hV2mean]
    exact hn.2.2
  have hSupport (x y : EuclideanDisorder N μ.maxDegree) (hy : 0<Y y) :
      A+Real.log (Y y)-(‖V y‖/Y y)*dist x y ≤ f x := by
    have hz : 0<truncatedPartition c β T (unpackDisorder y) :=
      (mul_pos_iff_of_pos_left (Real.exp_pos (-A))).mp hy
    have hh := logPartition_truncated_affine_support hN c hc hβ.le hT y x hz
    have hlog : A+Real.log (Y y)=Real.log (truncatedPartition c β T (unpackDisorder y)) := by
      dsimp [Y,Y₀]
      rw [Real.log_mul (Real.exp_ne_zero _) hz.ne',Real.log_exp]
      ring
    have hratio : ‖V y‖/Y y=‖truncatedFeatureMean c β T (unpackDisorder y)‖/
        truncatedPartition c β T (unpackDisorder y) := by
      dsimp [V,V₀,Y,Y₀]
      rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
      field_simp
    rw [hlog,hratio]
    exact hh
  have ht := GaussianFeatureMomentTail.lower_tail_le Y V hYm hYi hY2i hY0 hVm hV2i
    hB hD hMean hSecond hFeature f hSupport hs
  have hE : MeasurableSet {g : EuclideanDisorder N μ.maxDegree | f g ≤
      A-GaussianFeatureMomentTail.tailOffset B D-GaussianFeatureMomentTail.tailSlope B D*s} :=
    measurableSet_le ((partition_measurable c β).comp (unpack_measurable N μ.maxDegree) |>.log) measurable_const
  have he := (euclideanDisorder_hasLaw N μ.maxDegree).measureReal_eq hE
  rw [← he] at ht
  exact ht

end SlowEquilibration.SphericalModel
