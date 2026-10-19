module

public import OverlapPaper.ReplicaProcess
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-! Genuine physical subsequential laws and passage of Gram positivity to limits. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology
namespace OverlapPaper

def completeArray (R : OverlapArray) (i j : ℕ) : ℝ :=
  if hij : i < j then R ⟨(i,j),hij⟩ else
  if hji : j < i then R ⟨(j,i),hji⟩ else 1

def principalMatrix (R : OverlapArray) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun i j=>completeArray R i j)

def GramArrays : Set OverlapArray := {R | ∀m,(principalMatrix R m).PosSemidef}

theorem continuous_completeArray (i j : ℕ) : Continuous (fun R:OverlapArray=>completeArray R i j) := by
  unfold completeArray
  split_ifs <;> fun_prop

theorem continuous_principalMatrix (m : ℕ) : Continuous (fun R:OverlapArray=>principalMatrix R m) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_completeArray i j

theorem isClosed_GramArrays : IsClosed GramArrays := by
  have he : GramArrays=⋂m,(fun R=>principalMatrix R m) ⁻¹'
      {A:Matrix (Fin m) (Fin m) ℝ | A.PosSemidef} := by ext R;simp [GramArrays]
  rw [he]
  exact isClosed_iInter (fun m=>Matrix.posSemidef_is_closed.preimage (continuous_principalMatrix m))

theorem completeArray_finiteOverlapArray {n : ℕ} (hn : 0<n) (σ : ℕ → Configuration n)
    (i j : ℕ) : completeArray (finiteOverlapArray σ) i j=overlap (σ i) (σ j) := by
  unfold completeArray
  split_ifs with hij hji
  · rfl
  · exact overlap_symm _ _
  · have he : i=j := by omega
    subst j
    exact (overlap_self hn _).symm

theorem finiteOverlapArray_mem_GramArrays {n : ℕ} (hn : 0<n)
    (σ : ℕ → Configuration n) : finiteOverlapArray σ∈GramArrays := by
  intro m
  have he : principalMatrix (finiteOverlapArray σ) m=
      (overlapMatrix n).submatrix (fun i:Fin m=>σ i) (fun i:Fin m=>σ i) := by
    ext i j
    exact completeArray_finiteOverlapArray hn σ i j
  rw [he]
  exact (overlapMatrix_posSemidef n).submatrix _

def annealedProbabilityLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) (n : ℕ) :
    ProbabilityMeasure OverlapArray := ⟨annealedOverlapLaw ξ h n,inferInstance⟩

def IsPhysicalOverlapLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ)
    (ν : ProbabilityMeasure OverlapArray) : Prop :=
  ∃ φ:ℕ → ℕ,StrictMono φ ∧ Tendsto (annealedProbabilityLaw ξ h ∘ φ) atTop (𝓝 ν)

theorem exists_physicalOverlapLaw (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ) :
    ∃ν,IsPhysicalOverlapLaw ξ h ν := by
  rcases CompactSpace.tendsto_subseq (annealedProbabilityLaw ξ h) with ⟨ν,φ,hφ,hlim⟩
  exact ⟨ν,φ,hφ,hlim⟩

theorem annealedOverlapLaw_GramArrays (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ)
    {n : ℕ} (hn : 0<n) : annealedOverlapLaw ξ h n GramArrays=1 := by
  unfold annealedOverlapLaw
  rw [Measure.map_apply measurable_trajectoryOverlapArray isClosed_GramArrays.measurableSet]
  have he : trajectoryOverlapArray ⁻¹' GramArrays=(univ:Set (Πk,trajectorySpace n k)) := by
    ext y
    simp only [mem_preimage,mem_univ,iff_true]
    exact finiteOverlapArray_mem_GramArrays hn _
  rw [he]
  exact measure_univ

theorem physicalOverlapLaw_GramArrays (ξ : FourPapersCommon.AdmissibleEvenMixture) (h : ℝ)
    {ν : ProbabilityMeasure OverlapArray} (hν : IsPhysicalOverlapLaw ξ h ν) :
    (ν:Measure OverlapArray) GramArrays=1 := by
  rcases hν with ⟨φ,hφ,hlim⟩
  have he : (fun k=>(annealedProbabilityLaw ξ h (φ k):Measure OverlapArray) GramArrays)
      =ᶠ[atTop] fun _=>(1:ENNReal) := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)] with k hk
    exact annealedOverlapLaw_GramArrays ξ h hk
  have hp := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim isClosed_GramArrays
  simp only [Function.comp_def] at hp
  rw [Filter.limsup_congr he] at hp
  simp only [limsup_const] at hp
  have hle : (ν:Measure OverlapArray) GramArrays≤(ν:Measure OverlapArray) univ :=
    measure_mono (subset_univ GramArrays)
  exact le_antisymm (by simpa using hle) hp

end OverlapPaper
