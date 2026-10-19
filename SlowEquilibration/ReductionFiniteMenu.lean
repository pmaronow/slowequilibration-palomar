-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.KernelTVMeasurable
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.IsLUB

/-! Literal convex mixtures of a finite menu of probability measures and
the total-variation dependence on their weights. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

abbrev Weights (ι : Type*) [Fintype ι] := ↥(stdSimplex ℝ ι)

def mixture (μ : ι → Measure X) (w : Weights ι) : Measure X :=
  ∑ j, ENNReal.ofReal (w.1 j) • μ j

lemma mixture_apply (μ : ι → Measure X) (w : Weights ι) (A : Set X) :
    mixture μ w A = ∑ j, ENNReal.ofReal (w.1 j) * μ j A := by
  simp only [mixture,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]

instance mixture_probability (μ : ι → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (w : Weights ι) : IsProbabilityMeasure (mixture μ w) := by
  constructor
  rw [mixture_apply]
  simp only [measure_univ,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => w.property.1 j),w.property.2]
  simp

lemma mixture_real (μ : ι → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (w : Weights ι) (A : Set X) :
    (mixture μ w).real A = ∑ j, w.1 j * (μ j).real A := by
  rw [Measure.real,mixture_apply,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (w.property.1 j)]
    rfl
  · intro j _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem mixture_mass_le (μ : ι → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (w : Weights ι) (A : Set X) {c : ℝ} (hc : ∀ j, (μ j).real A ≤ c) :
    (mixture μ w).real A ≤ c := by
  rw [mixture_real]
  calc
    _ ≤ ∑ j, w.1 j*c := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hc j) (w.property.1 j))
    _ = c := by rw [← Finset.sum_mul,w.property.2,one_mul]

theorem mixture_mass_le_sum (μ : ι → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (w : Weights ι) (A : Set X) :
    (mixture μ w).real A ≤ ∑ j, (μ j).real A := by
  apply mixture_mass_le
  intro j
  exact Finset.single_le_sum (fun i _ => measureReal_nonneg) (Finset.mem_univ j)

lemma mixture_mass_difference_le (μ : ι → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (w v : Weights ι) (A : Set X) :
    |(mixture μ w).real A-(mixture μ v).real A| ≤ ∑ j, |w.1 j-v.1 j| := by
  rw [mixture_real,mixture_real,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |w.1 j*(μ j).real A-v.1 j*(μ j).real A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w.1 j-v.1 j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [← sub_mul,abs_mul,abs_of_nonneg measureReal_nonneg]
      exact mul_le_of_le_one_right (abs_nonneg _) measureReal_le_one

theorem totalVariation_mixture_le_add (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π]
    (w v : Weights ι) :
    totalVariation (mixture μ w) π ≤ totalVariation (mixture μ v) π + ∑ j, |w.1 j-v.1 j| := by
  apply csSup_le
  · exact ⟨0,∅,MeasurableSet.empty,by simp⟩
  · rintro r ⟨A,hA,rfl⟩
    calc
      _ ≤ |(mixture μ w).real A-(mixture μ v).real A| +
        |(mixture μ v).real A-π.real A| := abs_sub_le _ _ _
      _ ≤ (∑ j, |w.1 j-v.1 j|) + totalVariation (mixture μ v) π :=
        add_le_add (mixture_mass_difference_le μ w v A) (event_difference_le_totalVariation _ _ hA)
      _ = _ := add_comm _ _

theorem totalVariation_mixture_abs_sub_le (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π]
    (w v : Weights ι) :
    |totalVariation (mixture μ w) π-totalVariation (mixture μ v) π| ≤ ∑ j, |w.1 j-v.1 j| := by
  have h := totalVariation_mixture_le_add μ π w v
  have h' := totalVariation_mixture_le_add μ π v w
  simp only [abs_sub_comm (v.1 _) (w.1 _)] at h'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem totalVariation_mixture_lipschitz (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π] :
    LipschitzWith ⟨Fintype.card ι, Nat.cast_nonneg _⟩
      (fun w : Weights ι => totalVariation (mixture μ w) π) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  rw [Real.dist_eq]
  calc
    _ ≤ ∑ j, |w.1 j-v.1 j| := totalVariation_mixture_abs_sub_le μ π w v
    _ ≤ ∑ _j : ι, dist w v := by
      apply Finset.sum_le_sum
      intro j _
      exact (show dist (w.1 j) (v.1 j) ≤ dist w.1 v.1 from dist_le_pi_dist w.1 v.1 j)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rfl

theorem totalVariation_mixture_continuous (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π] :
    Continuous (fun w : Weights ι => totalVariation (mixture μ w) π) :=
  (totalVariation_mixture_lipschitz μ π).continuous

instance weights_nonempty [Nonempty ι] : Nonempty (Weights ι) := by
  classical
  exact ⟨⟨Pi.single (Classical.arbitrary ι) 1,single_mem_stdSimplex ℝ _⟩⟩

/-- The literal infimum over every admissible probability weight. -/
def menuDistance (μ : ι → Measure X) (π : Measure X) : ℝ :=
  ⨅ w : Weights ι, totalVariation (mixture μ w) π

/-- Continuity permits an exact countable dense reduction; no selected
weight, or optimizing weight, is assumed as input. -/
theorem menuDistance_eq_countable_inf [Nonempty ι] (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π] :
    menuDistance μ π = ⨅ k : ℕ, totalVariation (mixture μ (TopologicalSpace.denseSeq (Weights ι) k)) π := by
  have h := (TopologicalSpace.denseRange_denseSeq (Weights ι)).ciInf'
    (totalVariation_mixture_continuous μ π)
  rw [menuDistance,← h]
  change sInf _ = sInf _
  congr 1
  ext r
  constructor
  · rintro ⟨⟨w,⟨k,rfl⟩⟩,rfl⟩
    exact ⟨k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨⟨_,⟨k,rfl⟩⟩,rfl⟩

lemma menuDistance_nonneg [Nonempty ι] (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π] :
    0 ≤ menuDistance μ π := by
  exact le_ciInf (fun _ => totalVariation_nonneg _ _)

lemma menuDistance_le [Nonempty ι] (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π]
    (w : Weights ι) : menuDistance μ π ≤ totalVariation (mixture μ w) π := by
  exact ciInf_le ⟨0,by rintro _ ⟨v,rfl⟩; exact totalVariation_nonneg _ _⟩ w

lemma menuDistance_le_one [Nonempty ι] (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π] :
    menuDistance μ π ≤ 1 :=
  (menuDistance_le μ π (Classical.arbitrary (Weights ι))).trans (totalVariation_le_one _ _)

theorem menuDistance_separation [Nonempty ι] (μ : ι → Measure X)
    [∀ j, IsProbabilityMeasure (μ j)] (π : Measure X) [IsProbabilityMeasure π]
    {A : Set X} (hA : MeasurableSet A) :
    1-π.real Aᶜ-(∑ j, (μ j).real A) ≤ menuDistance μ π := by
  apply le_ciInf
  intro w
  exact (sub_le_sub_left (mixture_mass_le_sum μ w A) _).trans (separation_from_event _ _ hA)

end SlowEquilibration.ReductionFiniteMenu
