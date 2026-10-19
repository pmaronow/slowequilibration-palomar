-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairProjectedJetConcentration

/-! The genuine ordered tensor operator norm under coefficient projection
and mean shift. This controls every ambient derivative through order three
using the existing actual finite-mixture derivative identities. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open PureTensorJetFeatures PureTensorJetBounds GaussianCompactMaximum
open SphericalAging.FiniteModel SphericalAging.GaussianLandscape GaussianNormConcentration
open scoped ENNReal BigOperators RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sourceUnitTensorFeature (N p:ℕ) (v:Fin p→UnitSphere N):
    EuclideanSpace ℝ (TensorIndex N p):=tensorFeature (fun k=>(v k).val)

lemma sourceUnitTensorFeature_continuous (N p:ℕ) : Continuous (sourceUnitTensorFeature N p):=
  (tensorFeature_continuous N p).comp
    (continuous_pi (fun k=>continuous_subtype_val.comp (continuous_apply k)))

lemma sourceUnitTensorFeature_norm (N p:ℕ) (v:Fin p→UnitSphere N) :
    ‖sourceUnitTensorFeature N p v‖=1:=by
  have h:=tensorFeature_norm_sq_of_unit (fun k=>(v k).val) (fun k=>unit_norm (v k))
  change ‖sourceUnitTensorFeature N p v‖^2=1 at h
  nlinarith [norm_nonneg (sourceUnitTensorFeature N p v)]

lemma source_tensorForm_norm_le_absoluteSupremum {N p:ℕ} (hN:0<N)
    (g:EuclideanSpace ℝ (TensorIndex N p)) :
    ‖tensorForm N p (WithLp.ofLp g)‖ ≤ absoluteSupremum (sourceUnitTensorFeature N p) g:=by
  let :NeZero N:=⟨Nat.ne_of_gt hN⟩
  classical
  apply multilinear_norm_le_of_unit_bound _ (absoluteSupremum_nonneg _
    (sourceUnitTensorFeature_continuous N p) g)
  intro v hv
  let w:Fin p→UnitSphere N:=fun k=>⟨v k,by simpa only [Metric.mem_sphere,dist_zero_right] using hv k⟩
  have he:tensorForm N p (WithLp.ofLp g) v=inner ℝ (sourceUnitTensorFeature N p w) g:=by
    rw [tensorForm_apply]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,sourceUnitTensorFeature,
      tensorFeature_apply,w]
  rw [he]
  exact norm_inner_le_absoluteSupremum _ (sourceUnitTensorFeature_continuous N p) g w

lemma source_tensorForm_norm_le_coefficient_norm {N p:ℕ}
    (g:EuclideanSpace ℝ (TensorIndex N p)) : ‖tensorForm N p (WithLp.ofLp g)‖ ≤ ‖g‖:=by
  apply multilinear_norm_le_of_unit_bound _ (norm_nonneg g)
  intro v hv
  have hf:‖tensorFeature v‖=1:=by
    have h:=tensorFeature_norm_sq_of_unit v hv
    nlinarith [norm_nonneg (tensorFeature v)]
  have he:tensorForm N p (WithLp.ofLp g) v=inner ℝ (tensorFeature v) g:=by
    rw [tensorForm_apply]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,tensorFeature_apply]
  rw [he,Real.norm_eq_abs]
  simpa only [hf,one_mul] using abs_real_inner_le_norm (tensorFeature v) g

theorem sourceProjectedTensorSupremum_mean_bound {ι:Type*} [Fintype ι]
    {N p:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1) :
    (∫ g,absoluteSupremum (sourceUnitTensorFeature N p) (T g)
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ 2*((p:ℝ)+1)*Real.sqrt N:=by
  let :NeZero N:=⟨Nat.ne_of_gt hN⟩
  classical
  let a:=fun v:Fin p→UnitSphere N=>T.adjoint (sourceUnitTensorFeature N p v)
  have ha:Continuous a:=T.adjoint.continuous.comp (sourceUnitTensorFeature_continuous N p)
  let z: (Fin p→UnitSphere N)→EuclideanSpace ℝ (Fin p×Fin N):=
    fun v=>blockFeature (fun k=>(v k).val)
  have hz:Continuous z:=(blockFeature_continuous N p).comp
    (continuous_pi (fun k=>continuous_subtype_val.comp (continuous_apply k)))
  have hab (v:Fin p→UnitSphere N):‖a v‖ ≤ 1:=
    (contraction_adjoint_norm_le T hT _).trans_eq (sourceUnitTensorFeature_norm N p v)
  have hinc (v w:Fin p→UnitSphere N):‖a v-a w‖ ≤ 1*1*‖z v-z w‖:=by
    rw [show a v-a w=T.adjoint (sourceUnitTensorFeature N p v-sourceUnitTensorFeature N p w) by simp only [a,map_sub]]
    apply (contraction_adjoint_norm_le T hT _).trans
    simp only [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [sourceUnitTensorFeature,z,blockFeature_sub,blockFeature_norm_sq,Pi.sub_apply] using
      tensorFeature_increment_sq_le (fun k=>(v k).val) (fun k=>(w k).val)
        (fun k=>unit_norm (v k)) (fun k=>unit_norm (w k))
  have hb:=expected_absoluteSupremum_le a z ha hz (M:=1) (P:=1) (Q:=p)
    (by norm_num) (by norm_num) (by positivity) hab
    (fun v=>by simp [z,blockFeature_norm_sq]) hinc
  have hcard:(Fintype.card (Fin p×Fin N):ℝ)=(p:ℝ)*N:=by simp
  rw [hcard] at hb
  simp only [mul_one] at hb
  rw [add_comm (1:ℝ) (p:ℝ)] at hb
  have hdim:1+(p:ℝ)*N ≤ ((p:ℝ)+1)*N:=by
    have hNr:(1:ℝ) ≤ N:=by exact_mod_cast hN
    nlinarith
  have hs:Real.sqrt (1+(p:ℝ)*N) ≤ Real.sqrt ((p:ℝ)+1)*Real.sqrt N:=by
    rw [←Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hdim
  simp only [projected_absoluteSupremum_eq]
  exact hb.trans (by
    calc
      _ ≤ 2*Real.sqrt ((p:ℝ)+1)*(Real.sqrt ((p:ℝ)+1)*Real.sqrt N):=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _:=by
        calc
          _ = 2*(Real.sqrt ((p:ℝ)+1)*Real.sqrt ((p:ℝ)+1))*Real.sqrt N:=by ring
          _ = _:=by rw [Real.mul_self_sqrt (by positivity)])

lemma sourceProjectedTensorSupremum_lipschitz {ι:Type*} [Fintype ι]
    {N p:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1) :
    LipschitzWith (1:ℝ).toNNReal (fun g=>absoluteSupremum (sourceUnitTensorFeature N p) (T g)):=by
  let :NeZero N:=⟨Nat.ne_of_gt hN⟩
  classical
  rw [show (fun g=>absoluteSupremum (sourceUnitTensorFeature N p) (T g))=
    absoluteSupremum (fun v=>T.adjoint (sourceUnitTensorFeature N p v)) by funext g;exact projected_absoluteSupremum_eq _ _ _]
  have hh:∀ v:Bool×(Fin p→UnitSphere N),
      ‖innerSL ℝ (signedFeature (fun v=>T.adjoint (sourceUnitTensorFeature N p v)) v)‖ ≤ (1:ℝ):=by
    intro v
    simp only [innerSL_apply_norm,signedFeature,norm_smul,norm_sign,one_mul]
    exact (contraction_adjoint_norm_le T hT _).trans_eq (sourceUnitTensorFeature_norm N p v.2)
  exact field_supremum_lipschitz
    (fun v:Bool×(Fin p→UnitSphere N)=>innerSL ℝ (signedFeature (fun v=>T.adjoint (sourceUnitTensorFeature N p v)) v)) hh

theorem sourceProjectedAffineTensorNorm_tail {ι:Type*} [Fintype ι]
    {N p:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1)
    (m:EuclideanSpace ℝ (TensorIndex N p)) {K:ℝ} (hm:‖m‖ ≤ K*Real.sqrt N) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g|(2*((p:ℝ)+1)+1+K)*Real.sqrt N ≤ ‖tensorForm N p (WithLp.ofLp (T g+m))‖} ≤
      Real.exp (-(N:ℝ)/2):=by
  have ht:=centered_lipschitz_upper_tail _ (show (0:ℝ) ≤ 1 by norm_num)
    (sourceProjectedTensorSupremum_lipschitz hN T hT) (Real.sqrt_nonneg (N:ℝ))
  rw [Real.sq_sqrt (Nat.cast_nonneg N)] at ht
  have ht':(SYK.standardGaussianMeasureOnEuclidean ι).real
      {x|(∫ y,absoluteSupremum (sourceUnitTensorFeature N p) (T y)
        ∂SYK.standardGaussianMeasureOnEuclidean ι)+Real.sqrt N ≤
        absoluteSupremum (sourceUnitTensorFeature N p) (T x)} ≤ Real.exp (-(N:ℝ)/2):=by
    simpa only [one_pow,mul_one] using ht
  have hb:=sourceProjectedTensorSupremum_mean_bound hN T hT
  refine (measureReal_mono (fun g hg=>?_)).trans ht'
  have hadd:tensorForm N p (WithLp.ofLp (T g+m))=
      tensorForm N p (WithLp.ofLp (T g))+tensorForm N p (WithLp.ofLp m):=by
    unfold tensorForm
    simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  have hn:‖tensorForm N p (WithLp.ofLp (T g+m))‖ ≤
      absoluteSupremum (sourceUnitTensorFeature N p) (T g)+K*Real.sqrt N:=by
    rw [hadd]
    exact (norm_add_le _ _).trans (add_le_add (source_tensorForm_norm_le_absoluteSupremum hN _)
      ((source_tensorForm_norm_le_coefficient_norm m).trans hm))
  change (2*((p:ℝ)+1)+1+K)*Real.sqrt N ≤ _ at hg
  change (∫ z,absoluteSupremum (sourceUnitTensorFeature N p) (T z)
    ∂SYK.standardGaussianMeasureOnEuclidean ι)+Real.sqrt N ≤ _
  nlinarith

end
end SlowEquilibration.PairConditionalDeterminantMoments
