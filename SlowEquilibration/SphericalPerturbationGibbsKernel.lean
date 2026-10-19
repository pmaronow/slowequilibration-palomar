-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSelectedPerturbationKernel
public import SlowEquilibration.GaussianSpinKernels

@[expose] public section

/-! A genuine jointly measurable coefficient/disorder Gibbs kernel for
the actual tensor positivity perturbation of an arbitrary unit-spin law. -/
namespace SlowEquilibration.SphericalPositivePerturbation
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel GaussianSpinInterpolation GaussianSpinComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def coefficientOperator {N K : ℕ} (x : Fin K → ℝ) :
    PerturbationDisorder N K →L[ℝ] PerturbationDisorder N K :=
  diagonal (fun i : TensorCoordinate N K => x i.1)

theorem coefficientOperator_joint_continuous (N K : ℕ) :
    Continuous (fun p : (Fin K → ℝ) × PerturbationDisorder N K => coefficientOperator p.1 p.2) := by
  have hc : Continuous (fun p : (Fin K → ℝ) × PerturbationDisorder N K =>
      fun i : TensorCoordinate N K => p.1 i.1*p.2 i) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i.1).comp continuous_fst).mul
      ((PiLp.continuous_apply 2 (fun _ : TensorCoordinate N K => ℝ) i).comp continuous_snd)
  exact (PiLp.continuous_toLp 2 (fun _ : TensorCoordinate N K => ℝ)).comp hc

theorem unitLinear_coefficientOperator {N K : ℕ} (v : ℝ) (x : Fin K → ℝ)
    (z : UnitSpin N) (w : PerturbationDisorder N K) :
    unitLinear (coefficients (K:=K) v (fun _ => 1)) z (coefficientOperator x w)=
      unitLinear (coefficients v x) z w := by
  simp only [unitLinear,linear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,feature,coefficientOperator,diagonal_apply,coefficients,mul_one]
  apply Finset.sum_congr rfl
  intro i _
  ring

def parameterizedGibbsKernel {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v : ℝ) : Kernel ((Fin K → ℝ) × PerturbationDisorder N K) (UnitSpin N) :=
  (gibbsKernel ν (unitLinear (coefficients (K:=K) v (fun _ => 1)))).comap
    (fun p => coefficientOperator p.1 p.2) (coefficientOperator_joint_continuous N K).measurable

theorem parameterizedGibbsKernel_apply {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    {v : ℝ} (hv : 0≤v) (x : Fin K → ℝ) (w : PerturbationDisorder N K) :
    parameterizedGibbsKernel ν v (x,w)=gibbsMeasure ν (unitLinear (coefficients v x)) w := by
  have hb : ∀ᵐ z ∂ν,‖unitLinear (coefficients (K:=K) v (fun _ => 1)) z‖≤2*v :=
    .of_forall (unitLinear_norm_bound hv (fun _ => 1) (fun _ => by norm_num))
  rw [parameterizedGibbsKernel,Kernel.comap_apply,
    gibbsKernel_apply ν _ (unitLinear_measurable _) (by positivity) hb]
  have hm : moment ν (fun _ => 1) (unitLinear (coefficients (K:=K) v (fun _ => 1))) (coefficientOperator x w)=
      moment ν (fun _ => 1) (unitLinear (coefficients v x)) w := by
    unfold GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun z => by
      change 1*Real.exp (unitLinear (coefficients (K:=K) v (fun _ => 1)) z (coefficientOperator x w))=
        1*Real.exp (unitLinear (coefficients v x) z w)
      rw [unitLinear_coefficientOperator]
  unfold gibbsMeasure
  rw [hm]
  congr 1
  funext z
  rw [unitLinear_coefficientOperator]

theorem parameterizedGibbsKernel_markov {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    {v : ℝ} (hv : 0≤v) : IsMarkovKernel (parameterizedGibbsKernel (K:=K) ν v) := by
  have hb : ∀ᵐ z ∂ν,‖unitLinear (coefficients (K:=K) v (fun _ => 1)) z‖≤2*v :=
    .of_forall (unitLinear_norm_bound hv (fun _ => 1) (fun _ => by norm_num))
  let _ := gibbsKernel_markov ν _ (unitLinear_measurable _) (by positivity : 0≤2*v) hb
  unfold parameterizedGibbsKernel
  infer_instance

def ambientParameterizedGibbsKernel {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v : ℝ) : Kernel ((Fin K → ℝ) × PerturbationDisorder N K) (Vector N) :=
  (parameterizedGibbsKernel ν v).map Subtype.val

theorem ambientParameterizedGibbsKernel_markov {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    {v : ℝ} (hv : 0≤v) : IsMarkovKernel (ambientParameterizedGibbsKernel (K:=K) ν v) := by
  let _ := parameterizedGibbsKernel_markov (K:=K) ν hv
  exact Kernel.IsMarkovKernel.map _ measurable_subtype_coe

theorem ambientParameterizedGibbsKernel_unit_support {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v : ℝ) (p : (Fin K → ℝ) × PerturbationDisorder N K) :
    ∀ᵐ z ∂ambientParameterizedGibbsKernel ν v p,‖z‖=1 := by
  rw [ambientParameterizedGibbsKernel,Kernel.map_apply _ measurable_subtype_coe]
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (measurableSet_eq_fun continuous_norm.measurable measurable_const)).mpr
  exact .of_forall fun z => z.property

end
end SlowEquilibration.SphericalPositivePerturbation
