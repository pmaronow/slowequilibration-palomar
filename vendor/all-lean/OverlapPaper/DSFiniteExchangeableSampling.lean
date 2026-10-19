module

public import OverlapPaper.DSArrayPermutation
public import OverlapPaper.DSSamplingCollision

@[expose] public section

/-! Actual finite sampling from a weakly exchangeable array law. Distinct
samples have exactly the original finite law; iid sampling differs only on
the explicitly bounded collision event. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace OverlapPaper
set_option maxHeartbeats 500000

abbrev FiniteReplicaPair (k : ℕ) := {ij : Fin k×Fin k // ij.1 < ij.2}
abbrev FiniteOverlapArray (k : ℕ) := FiniteReplicaPair k→Icc (-1:ℝ) 1

def finiteOverlapPrefix (k : ℕ) (R : OverlapArray) : FiniteOverlapArray k := fun ij =>
  R ⟨(ij.1.1.val,ij.1.2.val),ij.2⟩

theorem continuous_finiteOverlapPrefix (k : ℕ) : Continuous (finiteOverlapPrefix k) := by
  apply continuous_pi
  intro ij
  exact continuous_apply _

def finiteSampleOverlapPrefix {n k : ℕ} (R : OverlapArray) (a : Fin k→Fin n) : FiniteOverlapArray k := fun ij =>
  ⟨completeArray R (a ij.1.1).val (a ij.1.2).val,completeArray_mem_Icc R _ _⟩

theorem continuous_finiteSampleOverlapPrefix {n k : ℕ} (a : Fin k→Fin n) :
    Continuous (fun R => finiteSampleOverlapPrefix R a) := by
  apply continuous_pi
  intro ij
  exact (continuous_completeArray _ _).subtype_mk _

theorem injective_finiteSampleOverlapPrefix_relabel {n k : ℕ} (hkn : k≤n) (a : Fin k→Fin n)
    (ha : Function.Injective a) : ∃π : Equiv.Perm ℕ,
      ({i | π i≠i}:Set ℕ).Finite ∧ ∀R,
        finiteSampleOverlapPrefix R a=finiteOverlapPrefix k (arrayRelabel π R) := by
  obtain ⟨σ,hσ⟩ := injective_sample_extends_permutation hkn a ha
  let π := extendFinitePermutation σ
  have hp (i : Fin k) : π i.val=(a i).val := by
    calc
      _ = (σ (Fin.castLE hkn i)).val := extendFinitePermutation_apply_fin σ (Fin.castLE hkn i)
      _ = _ := congrArg Fin.val (hσ i)
  refine ⟨π,extendFinitePermutation_finite_moves σ,fun R => ?_⟩
  funext ij
  apply Subtype.ext
  change completeArray R (a ij.1.1).val (a ij.1.2).val=completeArray R (π ij.1.1.val) (π ij.1.2.val)
  rw [hp,hp]

theorem integral_injective_finiteSampleOverlapPrefix {n k : ℕ} (ν : ProbabilityMeasure OverlapArray)
    (hν : WeaklyExchangeableOverlapLaw ν) (hkn : k≤n) (a : Fin k→Fin n) (ha : Function.Injective a)
    (f : C(FiniteOverlapArray k,ℝ)) :
    ∫R,f (finiteSampleOverlapPrefix R a) ∂(ν : Measure OverlapArray)=
      ∫R,f (finiteOverlapPrefix k R) ∂(ν : Measure OverlapArray) := by
  obtain ⟨π,hπ,he⟩ := injective_finiteSampleOverlapPrefix_relabel hkn a ha
  simp_rw [he]
  have hf : AEStronglyMeasurable (fun R => f (finiteOverlapPrefix k R))
      (ν.map (arrayRelabel π) : Measure OverlapArray) :=
    (f.continuous.comp (continuous_finiteOverlapPrefix k)).measurable.aestronglyMeasurable
  have hh := integral_map (continuous_arrayRelabel π).measurable.aemeasurable hf
  change (∫R,f (finiteOverlapPrefix k (arrayRelabel π R)) ∂(ν : Measure OverlapArray))=_
  rw [←hh]
  change (∫R,f (finiteOverlapPrefix k R) ∂(ν.map (arrayRelabel π) : Measure OverlapArray))=_
  rw [hν π hπ]

theorem iid_finiteExchangeableSampling_bound {n k : ℕ} (hn : 0<n) (hkn : k≤n)
    (ν : ProbabilityMeasure OverlapArray) (hν : WeaklyExchangeableOverlapLaw ν)
    (f : C(FiniteOverlapArray k,ℝ)) :
    ‖(∫a,(∫R,f (finiteSampleOverlapPrefix R a) ∂(ν : Measure OverlapArray))
        ∂iidUniformSamplingLaw n k hn)-
      (∫R,f (finiteOverlapPrefix k R) ∂(ν : Measure OverlapArray))‖ ≤
      2*‖(BoundedContinuousFunction.mkOfCompact f)‖*uniformSamplingCollisionRate n k := by
  let C := ‖(BoundedContinuousFunction.mkOfCompact f)‖
  have hbound (R : OverlapArray) (a : Fin k→Fin n) : ‖f (finiteSampleOverlapPrefix R a)‖≤C :=
    (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _
  have hF (a : Fin k→Fin n) : ‖∫R,f (finiteSampleOverlapPrefix R a) ∂(ν : Measure OverlapArray)‖≤C := by
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := (ν : Measure OverlapArray)) (C := C)
        (f := fun R => f (finiteSampleOverlapPrefix R a))
        (Filter.Eventually.of_forall (fun R => hbound R a))
  have hbase : ‖∫R,f (finiteOverlapPrefix k R) ∂(ν : Measure OverlapArray)‖≤C := by
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := (ν : Measure OverlapArray)) (C := C)
        (f := fun R => f (finiteOverlapPrefix k R))
        (Filter.Eventually.of_forall (fun R => (BoundedContinuousFunction.mkOfCompact f).norm_coe_le_norm _))
  exact iidUniformSamplingLaw_bounded_test hn _ _ C (norm_nonneg _) hF hbase
    (fun a ha => integral_injective_finiteSampleOverlapPrefix ν hν hkn a ha f)

end OverlapPaper
