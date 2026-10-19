module
public import FourPapersCommon.MixedModel
public import FRSB.ConstantMassEvolution

@[expose] public section

/-! Actual Cole–Hopf evolution in the original overlap coordinate of a mixed
model. The CDF coefficient remains literal, and endpoint atoms are included. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace FourPapersCommon
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 500000
open ColeHopfFoundation.ProbabilityTheory

theorem parisiCDF_mixedMeasure_constant_interval (ξ:AdmissibleEvenMixture)
    (μ:ParisiMeasure) {a b m:ℝ} (ha:a∈Icc (0:ℝ) 1) (hb:b∈Icc (0:ℝ) 1)
    (hc:∀q∈Ico a b,Paper.parisiCDF μ q=m) :
    ∀t∈Ico (ξ.clock a) (ξ.clock b),Paper.parisiCDF (mixedMeasure ξ μ) t=m := by
  intro t ht
  have htunit : t∈Icc (0:ℝ) 1 :=
    ⟨(ξ.clock_mem_unitInterval ha).1.trans ht.1,
      ht.2.le.trans (ξ.clock_mem_unitInterval hb).2⟩
  let q : Overlap := ξ.clockOrderIso.symm ⟨t,htunit⟩
  have hqclock : ξ.clock (q:ℝ)=t :=
    congrArg (fun z:Overlap=>(z:ℝ)) (ξ.clockOrderIso.apply_symm_apply ⟨t,htunit⟩)
  have hqI : (q:ℝ)∈Ico a b := by
    refine ⟨(ξ.clock_strictMonoOn.le_iff_le ha q.property).mp ?_,
      (ξ.clock_strictMonoOn.lt_iff_lt q.property hb).mp ?_⟩
    · rw [hqclock]; exact ht.1
    · rw [hqclock]; exact ht.2
  rw [←hqclock,parisiCDF_mixedMeasure ξ μ (q:ℝ) q.property]
  exact hc q hqI

theorem mixedPotential_coleHopf_on_constantCDF (ξ:AdmissibleEvenMixture)
    (μ:ParisiMeasure) {a b m:ℝ} (ha:a∈Icc (0:ℝ) 1) (hb:b∈Icc (0:ℝ) 1)
    (hab:a<b) (hc:∀q∈Ico a b,Paper.parisiCDF μ q=m) (x:ℝ) :
    mixedPotential ξ μ (a,x)=
      coleHopf m (ξ.first b-ξ.first a).toNNReal (fun y=>mixedPotential ξ μ (b,y)) x := by
  have hv : mixedBeta ξ^2*(ξ.clock b-ξ.clock a)=ξ.first b-ξ.first a := by
    rw [mixedBeta_sq]
    unfold AdmissibleEvenMixture.clock
    field_simp [ξ.variance_pos.ne']
  have h := FRSB.parisiPotential_coleHopf_on_constantCDF (mixedBeta ξ) (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (ξ.clock_mem_unitInterval ha).1
    (ξ.clock_strictMonoOn ha hb hab) (ξ.clock_mem_unitInterval hb).2
    (parisiCDF_mixedMeasure_constant_interval ξ μ ha hb hc) x
  rw [hv] at h
  exact h

end FourPapersCommon
