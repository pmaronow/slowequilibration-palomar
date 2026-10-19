-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetConcentration
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Genuine operator-jet supremum bounds after an arbitrary coefficient
contraction. This applies to the actual centered Gaussian regression
projection; the contraction changes neither the physical dimension scale
nor the Gaussian tail exponent. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open PureTensorJetFeatures PureTensorJetBounds PureTensorJetConcentration
open GaussianCompactMaximum
open SphericalAging.FiniteModel
open scoped ENNReal RealInnerProductSpace InnerProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma contraction_adjoint_norm_le {ι κ:Type*} [Fintype ι] [Fintype κ]
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ κ) (hT:‖T‖ ≤ 1)
    (x:EuclideanSpace ℝ κ) : ‖T.adjoint x‖ ≤ ‖x‖:=by
  have hn:‖T.adjoint‖=‖T‖:=ContinuousLinearMap.adjoint.norm_map T
  calc
    _ ≤ ‖T.adjoint‖*‖x‖:=T.adjoint.le_opNorm x
    _ ≤ 1*‖x‖:=mul_le_mul_of_nonneg_right (hn ▸ hT) (norm_nonneg x)
    _ = _:=one_mul _

lemma projected_absoluteSupremum_eq {ι κ V:Type*} [Fintype ι] [Fintype κ]
    (a:V→EuclideanSpace ℝ κ) (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ κ)
    (g:EuclideanSpace ℝ ι) :
    absoluteSupremum a (T g)=absoluteSupremum (fun v=>T.adjoint (a v)) g:=by
  unfold absoluteSupremum
  congr 1
  funext v
  simp only [signedFeature,←map_smul,T.adjoint_inner_left]

def sourceProjectedUnitJetEnvelope {ι:Type*} [Fintype ι] (N p j:ℕ)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p))
    (g:EuclideanSpace ℝ ι):ℝ:=absoluteSupremum (unitInsertion N p j) (T g)

theorem sourceProjectedUnitJetEnvelope_mean_bound {ι:Type*} [Fintype ι]
    {N p j:ℕ} (hN:0<N) (hp:1 ≤ p)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1) :
    (∫ g,sourceProjectedUnitJetEnvelope N p j T g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
      2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p*Real.sqrt N:=by
  let :NeZero N:=⟨Nat.ne_of_gt hN⟩
  classical
  let a:=fun v:UnitBlocks N j=>T.adjoint (unitInsertion N p j v)
  have ha:Continuous a:=T.adjoint.continuous.comp (unitInsertion_continuous N p j)
  let z:UnitBlocks N j→EuclideanSpace ℝ (Fin (j+1)×Fin N):=
    fun v=>blockFeature (fun k=>(v k).val)
  have hz:Continuous z:=(blockFeature_continuous N (j+1)).comp
    (continuous_pi (fun k=>continuous_subtype_val.comp (continuous_apply k)))
  have hp':(1:ℝ) ≤ Real.sqrt p:=by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)]
    exact_mod_cast hp
  have hab (v:UnitBlocks N j):‖a v‖ ≤ (p:ℝ)^j:=
    (contraction_adjoint_norm_le T hT _).trans
      (insertionFeature_norm_le _ (fun k=>unit_norm (v k)))
  have hinc (v w:UnitBlocks N j):‖a v-a w‖ ≤
      (p:ℝ)^j*Real.sqrt p*‖z v-z w‖:=by
    rw [show a v-a w=T.adjoint (unitInsertion N p j v-unitInsertion N p j w) by simp only [a,map_sub]]
    exact (contraction_adjoint_norm_le T hT _).trans
      (insertionFeature_increment_le _ _ (fun k=>unit_norm (v k)) (fun k=>unit_norm (w k)))
  have h:=expected_absoluteSupremum_le a z ha hz (M:=(p:ℝ)^j) (P:=Real.sqrt p)
    (Q:=(j:ℝ)+1) (by positivity) hp' (by positivity) hab
    (fun v=>by simp [z,blockFeature_norm_sq]) hinc
  have hcard:(Fintype.card (Fin (j+1)×Fin N):ℝ)=((j:ℝ)+1)*N:=by simp
  rw [hcard] at h
  have hdim:1+((j:ℝ)+1)*N ≤ ((j:ℝ)+2)*N:=by
    have hNr:(1:ℝ) ≤ N:=by exact_mod_cast hN
    nlinarith
  have hsqrt:Real.sqrt (1+((j:ℝ)+1)*N) ≤ Real.sqrt ((j:ℝ)+2)*Real.sqrt N:=by
    rw [←Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hdim
  have hnum:2*(p:ℝ)^j*Real.sqrt p*Real.sqrt (1+((j:ℝ)+1))*Real.sqrt (1+((j:ℝ)+1)*N) ≤
      2*((j:ℝ)+2)*(p:ℝ)^j*Real.sqrt p*Real.sqrt N:=by
    rw [show 1+((j:ℝ)+1)=(j:ℝ)+2 by ring]
    calc
      _ ≤ 2*(p:ℝ)^j*Real.sqrt p*Real.sqrt ((j:ℝ)+2)*(Real.sqrt ((j:ℝ)+2)*Real.sqrt N):=by gcongr
      _ = _:=by rw [←mul_assoc,mul_assoc (2*(p:ℝ)^j*Real.sqrt p),Real.mul_self_sqrt (by positivity)];ring
  simp only [sourceProjectedUnitJetEnvelope,projected_absoluteSupremum_eq] 
  exact h.trans hnum

end
end SlowEquilibration.PairConditionalDeterminantMoments
