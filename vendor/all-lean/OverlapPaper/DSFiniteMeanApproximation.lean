module

public import OverlapPaper.DSFiniteCoordinateLaw
public import OverlapPaper.DSGramError
public import FourPapersCommon.L2ObservableBound

@[expose] public section

/-! An actual L² coupling bounds every finite Lipschitz overlap test by
its continuous coordinate-prefix approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace OverlapPaper
set_option maxHeartbeats 600000

def finiteGramSamplingMean (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ)
    (f : C(FiniteOverlapArray k,ℝ)) : ℝ :=
  ∫p,f (finiteCoordinateOverlap k p.2) ∂coordinateFiniteSamplingLaw ρ k

def finitePrefixGramSamplingMean (ρ : ProbabilityMeasure DSDirectingSpace) (k M : ℕ)
    (f : C(FiniteOverlapArray k,ℝ)) : ℝ :=
  ∫p,f (finiteCoordinateOverlapPrefix k M p.2) ∂coordinateFiniteSamplingLaw ρ k

theorem finitePrefixGramSamplingMean_eq (ρ : ProbabilityMeasure DSDirectingSpace) (k M : ℕ)
    (f : C(FiniteOverlapArray k,ℝ)) :
    finitePrefixGramSamplingMean ρ k M f=
      ∫μ,finiteCoordinateSamplingMean k
        ⟨fun v => f (finiteCoordinateOverlapPrefix k M v),
          f.continuous.comp (continuous_finiteCoordinateOverlapPrefix k M)⟩ μ
        ∂(ρ : Measure DSDirectingSpace) := by
  exact integral_coordinateFiniteSamplingLaw ρ k _
    (f.continuous.comp (continuous_finiteCoordinateOverlapPrefix k M)).measurable
    ‖BoundedContinuousFunction.mkOfCompact f‖
    (fun v => (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _)

theorem finiteGramSamplingMean_prefix_bound (ρ : ProbabilityMeasure DSDirectingSpace) (k M : ℕ)
    (f : C(FiniteOverlapArray k,ℝ)) (K : ℝ≥0) (hK : LipschitzWith K f) :
    |finiteGramSamplingMean ρ k f-finitePrefixGramSamplingMean ρ k M f|≤
      (K:ℝ)*(Fintype.card (FiniteReplicaPair k):ℝ)*Real.sqrt (coordinatePairTailEnergy ρ M) := by
  let P := coordinateFiniteSamplingLaw ρ k
  let E := fun (ij : FiniteReplicaPair k) (p : DSDirectingSpace×(Fin k→DSCoordinateBall)) =>
    coordinateGramError M (p.2 ij.1.1,p.2 ij.1.2)
  have hE (ij : FiniteReplicaPair k) : MemLp (E ij) 2 P :=
    MemLp.of_bound ((measurable_coordinateGramError M).comp
      (((measurable_pi_apply ij.1.1).comp measurable_snd).prodMk
        ((measurable_pi_apply ij.1.2).comp measurable_snd))).aestronglyMeasurable 2
      (Eventually.of_forall (fun p => coordinateGramError_norm_le M _))
  have hI (ij : FiniteReplicaPair k) : Integrable (fun p => |E ij p|) P := by
    simpa only [Real.norm_eq_abs] using ((hE ij).integrable (by norm_num)).norm
  have heq (ij : FiniteReplicaPair k) : (∫p,(E ij p)^2 ∂P)=coordinatePairTailEnergy ρ M :=
    integral_coordinateFiniteSamplingLaw_pair ρ ij.1.1 ij.1.2 (ne_of_lt ij.2)
      (fun p => coordinateGramError M p^2) ((measurable_coordinateGramError M).pow_const 2)
      4 (coordinateGramError_sq_norm_le M)
  have habs (ij : FiniteReplicaPair k) : (∫p,|E ij p| ∂P)≤Real.sqrt (coordinatePairTailEnergy ρ M) := by
    have hh := FourPapersCommon.integral_abs_le_sqrt_square (E ij) (hE ij)
    rw [heq ij] at hh
    exact hh
  let C := ‖BoundedContinuousFunction.mkOfCompact f‖
  have hfi : Integrable (fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) =>
      f (finiteCoordinateOverlap k p.2)) P :=
    (integrable_const C).mono'
      (f.continuous.measurable.comp ((measurable_finiteCoordinateOverlap k).comp measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall (fun p => (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _))
  have hgi : Integrable (fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) =>
      f (finiteCoordinateOverlapPrefix k M p.2)) P :=
    (integrable_const C).mono'
      (f.continuous.measurable.comp ((continuous_finiteCoordinateOverlapPrefix k M).measurable.comp measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall (fun p => (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _))
  have hp (p : DSDirectingSpace×(Fin k→DSCoordinateBall)) :
      |f (finiteCoordinateOverlap k p.2)-f (finiteCoordinateOverlapPrefix k M p.2)|≤
        (K:ℝ)*∑ij : FiniteReplicaPair k,|E ij p| := by
    have hl := hK.dist_le_mul (finiteCoordinateOverlap k p.2) (finiteCoordinateOverlapPrefix k M p.2)
    rw [Real.dist_eq] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (finiteCoordinateOverlap_distance_le k M p.2) K.2)
  change |(∫p,f (finiteCoordinateOverlap k p.2) ∂P)-
    (∫p,f (finiteCoordinateOverlapPrefix k M p.2) ∂P)|≤_
  calc
    _ = |∫p,f (finiteCoordinateOverlap k p.2)-f (finiteCoordinateOverlapPrefix k M p.2) ∂P| :=
      by rw [integral_sub hfi hgi]
    _ ≤ ∫p,|f (finiteCoordinateOverlap k p.2)-f (finiteCoordinateOverlapPrefix k M p.2)| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) =>
          f (finiteCoordinateOverlap k p.2)-f (finiteCoordinateOverlapPrefix k M p.2))
    _ ≤ ∫p,(K:ℝ)*(∑ij : FiniteReplicaPair k,|E ij p|) ∂P :=
      integral_mono (hfi.sub hgi).norm
        ((integrable_finsetSum Finset.univ (fun ij _ => hI ij)).const_mul (K:ℝ)) hp
    _ = (K:ℝ)*∑ij : FiniteReplicaPair k,(∫p,|E ij p| ∂P) := by
      rw [integral_const_mul,integral_finsetSum _ (fun ij _ => hI ij)]
    _ ≤ (K:ℝ)*∑ _ij : FiniteReplicaPair k,Real.sqrt (coordinatePairTailEnergy ρ M) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ij _ => habs ij)) K.2
    _ = _ := by simp [mul_assoc]

end OverlapPaper
