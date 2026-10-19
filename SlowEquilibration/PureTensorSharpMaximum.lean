-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSharpAbsoluteMaximum

/-! The exact factor two for the original pure ordered tensor Hamiltonian. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PureTensorJetBounds
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open SphericalAging.FiniteModel PureTensorJetFeatures GaussianSharpAbsoluteMaximum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem expected_unitJetEnvelope_zero_le_two {N p : ℕ} (hN : 0<N) (hp : 1≤p) :
    (∫ J,unitJetEnvelope N p 0 J ∂disorderLaw N p)≤2*Real.sqrt p*Real.sqrt N := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hp' : (1:ℝ)≤Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)]
    exact_mod_cast hp
  have hb (v w : UnitBlocks N 0) : ‖blockFeature (fun i => (v i).val)-
      blockFeature (fun i => (w i).val)‖=‖(v 0).val-(w 0).val‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [blockFeature_sub,blockFeature_norm_sq]
    simp
  have h := expected_absoluteSupremum_le_twice (unitInsertion N p 0)
    (fun v : UnitBlocks N 0 => (v 0).val) (unitInsertion_continuous N p 0)
    (continuous_subtype_val.comp (continuous_apply 0)) (L := Real.sqrt p) (by positivity)
    (fun v => by
      have h0 : ‖unitInsertion N p 0 v‖≤1 := by
        simpa [unitInsertion] using insertionFeature_norm_le (p := p) (j := 0)
          (fun i => (v i).val) (fun i => unit_norm (v i))
      exact h0.trans hp')
    (fun v => unit_norm (v 0))
    (fun v w => by
      have hh := insertionFeature_increment_le (p := p) (j := 0)
        (fun i => (v i).val) (fun i => (w i).val)
        (fun i => unit_norm (v i)) (fun i => unit_norm (w i))
      simpa only [unitInsertion,pow_zero,one_mul,hb] using hh)
  have hLaw : HasLaw (WithLp.toLp 2 : Disorder N p → EuclideanSpace ℝ (TensorIndex N p))
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N p)) (disorderLaw N p) :=
    ⟨by fun_prop,rfl⟩
  have he := hLaw.integral_comp (absoluteSupremum_integrable (unitInsertion N p 0)
    (unitInsertion_continuous N p 0)).aestronglyMeasurable
  simpa only [unitJetEnvelope,Function.comp_def,Fintype.card_fin,← he] using h

/-- The literal actual pure Hamiltonian is uniformly bounded by this envelope,
and its expectation has precisely the source constant `2 N sqrt p`. -/
theorem expected_pureJetEnvelope_zero_le_two {N p : ℕ} (hN : 0<N) (hp : 1≤p) :
    (∫ J,pureJetEnvelope N p 0 J ∂disorderLaw N p)≤2*N*Real.sqrt p := by
  unfold pureJetEnvelope
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (a := normalization N p*Real.sqrt N^(p-0))
    (expected_unitJetEnvelope_zero_le_two hN hp)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (pow_nonneg (Real.sqrt_nonneg _) _))
  refine hh.trans_eq ?_
  have he := physical_normalization_identity (j := 0) hN hp (Nat.zero_le p)
  norm_num only [Nat.sub_zero,Nat.cast_zero,zero_div,sub_zero,Real.rpow_one] at he
  calc
    _ = 2*Real.sqrt p*(normalization N p*Real.sqrt N^p*Real.sqrt N) := by simp only [Nat.sub_zero];ring
    _ = _ := by rw [he];ring

end SlowEquilibration.PureTensorJetBounds
