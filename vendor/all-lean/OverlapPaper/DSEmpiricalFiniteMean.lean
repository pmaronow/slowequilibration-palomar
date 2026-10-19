module

public import OverlapPaper.DSFiniteMeanApproximation

@[expose] public section

/-! Actual empirical conditional iid Gram tests coincide with iid sampling
of the original finite array, with the exchangeability collision error. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace OverlapPaper
set_option maxHeartbeats 700000

def finiteGramConditionalMean (k : ℕ) (f : C(FiniteOverlapArray k,ℝ)) (μ : DSDirectingSpace) : ℝ :=
  ∫v,f (finiteCoordinateOverlap k v) ∂(finiteIIDProbability k (toCoordinateProbability μ) : Measure _)

theorem measurable_finiteGramConditionalMean (k : ℕ) (f : C(FiniteOverlapArray k,ℝ)) :
    Measurable (finiteGramConditionalMean k f) := by
  have hm : StronglyMeasurable (fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) =>
      f (finiteCoordinateOverlap k p.2)) :=
    (f.continuous.measurable.comp ((measurable_finiteCoordinateOverlap k).comp measurable_snd)).stronglyMeasurable
  have hh := hm.integral_kernel_prod_right' (κ := coordinateFiniteSamplingKernel k)
  have he : (fun μ : DSDirectingSpace => ∫v,f (finiteCoordinateOverlap k v)
      ∂coordinateFiniteSamplingKernel k μ)=finiteGramConditionalMean k f := by
    funext μ
    rw [coordinateFiniteSamplingKernel_apply]
    rfl
  rw [←he]
  exact hh.measurable

theorem finiteGramSamplingMean_eq (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ)
    (f : C(FiniteOverlapArray k,ℝ)) : finiteGramSamplingMean ρ k f=
      ∫μ,finiteGramConditionalMean k f μ ∂(ρ : Measure DSDirectingSpace) :=
  integral_coordinateFiniteSamplingLaw ρ k _
    (f.continuous.measurable.comp (measurable_finiteCoordinateOverlap k))
    ‖BoundedContinuousFunction.mkOfCompact f‖
    (fun _ => (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _)

theorem finiteCoordinateOverlap_empirical {n k : ℕ} (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (a : Fin k→Fin n) :
    finiteCoordinateOverlap k (fun i => empiricalGramCoordinates n hn ε hε R (a i))=
      finiteSampleOverlapPrefix R.1 a := by
  funext ij
  apply Subtype.ext
  exact empiricalGramCoordinates_inner n hn ε hε R (a ij.1.1) (a ij.1.2)

theorem finiteGramConditionalMean_empirical {n k : ℕ} (hn : 0<n) (ε : ℝ) (hε : 0<ε)
    (R : GramArray) (f : C(FiniteOverlapArray k,ℝ)) :
    finiteGramConditionalMean k f (empiricalDirectingPoint hn (empiricalGramCoordinates n hn ε hε R))=
      ∫a,f (finiteSampleOverlapPrefix R.1 a) ∂iidUniformSamplingLaw n k hn := by
  change (∫v,f (finiteCoordinateOverlap k v)
    ∂(finiteIIDProbability k (finiteEmpiricalProbability hn (empiricalGramCoordinates n hn ε hε R)) : Measure _))=_
  rw [finiteIIDProbability_empirical]
  rw [integral_map (μ := iidUniformSamplingLaw n k hn)
    (φ := fun a : Fin k→Fin n => fun i => empiricalGramCoordinates n hn ε hε R (a i))
    (f := fun v : Fin k→DSCoordinateBall => f (finiteCoordinateOverlap k v))
    (Measurable.of_eval (fun i => measurable_of_countable
      (fun a : Fin k→Fin n => empiricalGramCoordinates n hn ε hε R (a i)))).aemeasurable
    (f.continuous.measurable.comp (measurable_finiteCoordinateOverlap k)).aestronglyMeasurable]
  simp_rw [finiteCoordinateOverlap_empirical]

theorem finiteGramSamplingMean_empirical (ν : ProbabilityMeasure GramArray) (n k : ℕ)
    (f : C(FiniteOverlapArray k,ℝ)) :
    finiteGramSamplingMean (gramEmpiricalDirectingLaw ν n) k f=
      ∫a,(∫R,f (finiteSampleOverlapPrefix R.1 a) ∂(ν : Measure GramArray))
        ∂iidUniformSamplingLaw (n+1) k (Nat.succ_pos n) := by
  rw [finiteGramSamplingMean_eq,gramEmpiricalDirectingLaw,ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_gramEmpiricalDirectingPoint n).aemeasurable
      (measurable_finiteGramConditionalMean k f).aestronglyMeasurable]
  change (∫R,finiteGramConditionalMean k f
    (empiricalDirectingPoint (Nat.succ_pos n)
      (empiricalGramCoordinates (n+1) (Nat.succ_pos n) (1/(n+1:ℝ)) (by positivity) R))
      ∂(ν : Measure GramArray))=_
  simp_rw [finiteGramConditionalMean_empirical]
  apply integral_integral_swap
  have hm : Measurable (fun p : GramArray×(Fin k→Fin (n+1)) => f (finiteSampleOverlapPrefix p.1.1 p.2)) :=
    measurable_from_prod_countable_left (fun a =>
      (f.continuous.comp ((continuous_finiteSampleOverlapPrefix a).comp continuous_subtype_val)).measurable)
  exact (integrable_const ‖BoundedContinuousFunction.mkOfCompact f‖).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun _ => (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _))

theorem finiteGramSamplingMean_empirical_collision_bound (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val)) {n k : ℕ} (hkn : k≤n+1)
    (f : C(FiniteOverlapArray k,ℝ)) :
    |finiteGramSamplingMean (gramEmpiricalDirectingLaw ν n) k f-
      (∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray))|≤
      2*‖BoundedContinuousFunction.mkOfCompact f‖*uniformSamplingCollisionRate (n+1) k := by
  rw [finiteGramSamplingMean_empirical]
  have hh := iid_finiteExchangeableSampling_bound (Nat.succ_pos n) hkn (ν.map Subtype.val) hν f
  have hbase : (∫R,f (finiteOverlapPrefix k R) ∂(ν.map Subtype.val : Measure OverlapArray))=
      ∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray) :=
    integral_map (φ := (Subtype.val : GramArray→OverlapArray))
      (f := fun R : OverlapArray => f (finiteOverlapPrefix k R)) measurable_subtype_coe.aemeasurable
      (f.continuous.comp (continuous_finiteOverlapPrefix k)).measurable.aestronglyMeasurable
  have he (a : Fin k→Fin (n+1)) :
      (∫R,f (finiteSampleOverlapPrefix R a) ∂(ν.map Subtype.val : Measure OverlapArray))=
        ∫R,f (finiteSampleOverlapPrefix R.1 a) ∂(ν : Measure GramArray) :=
    integral_map (φ := (Subtype.val : GramArray→OverlapArray))
      (f := fun R : OverlapArray => f (finiteSampleOverlapPrefix R a)) measurable_subtype_coe.aemeasurable
      (f.continuous.comp (continuous_finiteSampleOverlapPrefix a)).measurable.aestronglyMeasurable
  rw [hbase] at hh
  simp_rw [he] at hh
  rw [Real.norm_eq_abs] at hh
  exact hh

end OverlapPaper
