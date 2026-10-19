module

public import SphericalAging.SphereFDTAlgebra
public import SphericalAging.SphereEntropyBudget

public section

/-! Genuine parameter continuity of the constructed backward generator. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SphereGeneratorRegularity

open FiniteModel SphericalIntegrationByParts SphereEntropyDissipation SphereEntropyBudget
open SphereGeneratorIntegrationByParts SphereFDTAlgebra
open scoped BigOperators

/-- Joint C2 regularity gives the genuine joint C1 first rotation derivative. -/
theorem joint_lieDerivative_contDiff_one {N : ℕ} (A : Operator N)
    {m : ℝ → Vector N → ℝ} (hm : ContDiff ℝ 2 (Function.uncurry m)) :
    ContDiff ℝ 1 (fun z : ℝ × Vector N => lieDerivative A (m z.1) z.2) := by
  have hf : ContDiff ℝ 2 (Function.uncurry (fun z : ℝ × Vector N => fun x : Vector N => m z.1 x)) :=
    hm.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ 1 (fun z : ℝ × Vector N => fderiv ℝ (m z.1) z.2) :=
    hf.fderiv contDiff_snd (by norm_num)
  exact hd.clm_apply (A.contDiff.comp contDiff_snd)

/-- Joint C1 regularity already gives continuity of the actual first rotation derivative. -/
theorem joint_lieDerivative_continuous_one {N : ℕ} (A : Operator N)
    {m : ℝ → Vector N → ℝ} (hm : ContDiff ℝ 1 (Function.uncurry m)) :
    Continuous (fun z : ℝ × Vector N => lieDerivative A (m z.1) z.2) := by
  have hf : ContDiff ℝ 1 (Function.uncurry (fun z : ℝ × Vector N => fun x : Vector N => m z.1 x)) :=
    hm.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : Continuous (fun z : ℝ × Vector N => fderiv ℝ (m z.1) z.2) :=
    Continuous.fderiv hf continuous_snd le_rfl
  exact hd.clm_apply (A.continuous.comp continuous_snd)

/-- The full genuine backward generator is jointly continuous for a joint C2 mean. -/
theorem joint_rotationGenerator_continuous {N p : ℕ} {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι → Operator N)
    {m : ℝ → Vector N → ℝ} (hm : ContDiff ℝ 2 (Function.uncurry m)) :
    Continuous (fun z : ℝ × Vector N => rotationGenerator κ β J A (m z.1) z.2) := by
  classical
  unfold rotationGenerator
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (joint_lieDerivative_continuous_one (A i)
      (m := fun t x => lieDerivative (A i) (m t) x) (joint_lieDerivative_contDiff_one (A i) hm)).add
      ((continuous_const.mul
        ((lieDerivative_continuous (A i) ((Hamiltonian_contDiff J).of_le (by simp))).comp continuous_snd)).mul
          (joint_lieDerivative_contDiff_one (A i) hm).continuous))

end SphericalAging.SphereGeneratorRegularity
