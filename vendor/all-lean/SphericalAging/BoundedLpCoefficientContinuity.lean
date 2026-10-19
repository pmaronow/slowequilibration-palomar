module

public import SphericalAging.BoundedLpComposition
public import SphericalAging.RandomLpCoefficient

public section

/-! Bounded uniformly continuous random matrix coefficients act jointly
continuously on L² vectors. Operator norm continuity is not required. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.BoundedLpCoefficientContinuity
open HardSphereDynamics BoundedLpComposition RandomLpCoefficient LpClassMomentAlgebra
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[expose] def coefficient (g : State N → (State N →L[ℝ] State N)) (hg : Continuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (U : Lp (State N) 2 P) :
    Coefficient (N := N) (P := P) K where
  value := fun ω => g (U ω)
  measurable := hg.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)
  bound := .of_forall (fun ω => hK (U ω))

@[expose] def action (g : State N → (State N →L[ℝ] State N)) (hg : Continuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (U V : Lp (State N) 2 P) : Lp (State N) 2 P :=
  operator (coefficient g hg K hK U) V

theorem action_coeFn (g : State N → (State N →L[ℝ] State N)) (hg : Continuous g)
    (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (U V : Lp (State N) 2 P) :
    action g hg K hK U V=ᵐ[P] fun ω => g (U ω) (V ω) :=
  apply_coeFn (coefficient g hg K hK U) V

theorem action_fixed_continuous (g : State N → (State N →L[ℝ] State N))
    (huc : UniformContinuous g) (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) (V : Lp (State N) 2 P) :
    Continuous (fun U : Lp (State N) 2 P => action g huc.continuous K hK U V) := by
  apply continuous_iff_continuousAt.mpr
  intro U0
  let a := action (P := P) g huc.continuous K hK
  let f := fun U : Lp (State N) 2 P => fun ω => g (U ω)-g (U0 ω)
  let r := fun U : Lp (State N) 2 P => fun ω => (g (U ω)-g (U0 ω)) (V ω)
  have hf (U : Lp (State N) 2 P) : MemLp (f U) 2 P :=
    (composition_memLp g huc.continuous K hK U).sub
      (composition_memLp g huc.continuous K hK U0)
  have hr (U : Lp (State N) 2 P) : AEStronglyMeasurable (r U) P :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((hf U).aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable V))
  have hc := composition_continuous (P := P) g huc K hK
  let c := composition (P := P) g huc.continuous K hK
  change Continuous c at hc
  have hfc (U : Lp (State N) 2 P) : (c U-c U0 : Lp (State N →L[ℝ] State N) 2 P)=ᵐ[P] f U := by
    filter_upwards [composition_coeFn g huc.continuous K hK U,
      composition_coeFn g huc.continuous K hK U0,Lp.coeFn_sub (c U) (c U0)] with ω hu hu0 hs
    simp only [Pi.sub_apply] at hs
    exact hs.trans (congrArg₂ (fun A B : State N →L[ℝ] State N => A-B) hu hu0)
  have hzero : Tendsto (fun U => lpNorm (f U) 2 P) (𝓝 U0) (𝓝 0) := by
    have ht := ((hc.sub (continuous_const (y := c U0))).norm).tendsto U0
    have he (U) : lpNorm (f U) 2 P=‖c U-c U0‖ := by
      rw [← lpNorm_two_coe]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (hfc U).symm)
    simpa only [he,Pi.sub_apply,sub_self,norm_zero] using ht
  have hz := LpMultiplierTruncation.lpNorm_two_tendsto_zero (Lp.memLp V)
    (l := 𝓝 U0) (f := f) (g := r) (L := 1) (K := 2*(K : ℝ))
    (by positivity) (by positivity) (.of_forall hf) (.of_forall hr) ?_ ?_ hzero
  · have he (U) : (a U V-a U0 V : Lp (State N) 2 P)=ᵐ[P] r U := by
      filter_upwards [action_coeFn g huc.continuous K hK U V,
        action_coeFn g huc.continuous K hK U0 V,Lp.coeFn_sub (a U V) (a U0 V)] with ω hu hu0 hs
      simp only [Pi.sub_apply] at hs
      exact hs.trans (by rw [hu,hu0];exact (sub_apply _ _ _).symm)
    have hn (U) : ‖a U V-a U0 V‖=lpNorm (r U) 2 P := by
      rw [← lpNorm_two_coe]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (he U))
    change Tendsto (fun U => a U V) (𝓝 U0) (𝓝 (a U0 V))
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [hn] using hz)
  · exact .of_forall (fun U => .of_forall (fun ω => by
      simpa only [r,f,one_mul] using (g (U ω)-g (U0 ω)).le_opNorm (V ω)))
  · exact .of_forall (fun U => .of_forall (fun ω => by
      have hb := (norm_sub_le (g (U ω)) (g (U0 ω))).trans (add_le_add (hK _) (hK _))
      exact ((g (U ω)-g (U0 ω)).le_opNorm (V ω)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))))

/-- Actual joint continuity of matrix evaluation on L². -/
theorem action_joint_continuous (g : State N → (State N →L[ℝ] State N))
    (huc : UniformContinuous g) (K : ℝ≥0) (hK : ∀ x,‖g x‖≤K) :
    Continuous (fun q : Lp (State N) 2 P × Lp (State N) 2 P =>
      action g huc.continuous K hK q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q0
  let a := fun U => operator (coefficient (P := P) g huc.continuous K hK U)
  have he (q : Lp (State N) 2 P × Lp (State N) 2 P) :
      a q.1 q.2-a q0.1 q0.2=a q.1 (q.2-q0.2)+(a q.1 q0.2-a q0.1 q0.2) := by
    rw [map_sub]
    abel
  have ht1 : Tendsto (fun q : Lp (State N) 2 P × Lp (State N) 2 P =>
      ‖a q.1 (q.2-q0.2)‖) (𝓝 q0) (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun q => norm_apply_le _ _)
    simpa only [mul_zero,Pi.sub_apply,sub_self,norm_zero] using
      ((continuous_snd.sub (continuous_const (y := q0.2))).norm.const_mul (K : ℝ)).tendsto q0
  have ht2 := ((action_fixed_continuous g huc K hK q0.2).comp continuous_fst).tendsto q0
  change Tendsto (fun q => a q.1 q0.2) (𝓝 q0) (𝓝 (a q0.1 q0.2)) at ht2
  have ht1' : Tendsto (fun q : Lp (State N) 2 P × Lp (State N) 2 P =>
      a q.1 (q.2-q0.2)) (𝓝 q0) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr ht1
  have ht := ht1'.add (ht2.sub (tendsto_const_nhds (x := a q0.1 q0.2)))
  change Tendsto (fun q => a q.1 q.2) (𝓝 q0) (𝓝 (a q0.1 q0.2))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [← he,sub_self,add_zero,norm_zero] using ht.norm

end SphericalAging.BoundedLpCoefficientContinuity
