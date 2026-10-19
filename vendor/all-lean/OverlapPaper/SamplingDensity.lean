module

public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

@[expose] public section

/-! Every tail of an actual independent sample is dense in the law's support. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace OverlapPaper

section
variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

omit [TopologicalSpace E] [SecondCountableTopology E] [BorelSpace E] in
theorem iid_sample_frequently_mem {U : Set E} (hU : MeasurableSet U) (hpos : 0<μ U) :
    ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ), ∃ᶠn in atTop,v n∈U := by
  let P:=Measure.infinitePi (fun _ : ℕ=>μ)
  let A:ℕ→Set (ℕ→E):=fun n=>(fun v=>v n) ⁻¹' U
  have hm : ∀n,MeasurableSet (A n):=fun n=>hU.preimage (measurable_pi_apply n)
  have hi : iIndepSet A P := by
    apply (iIndepSet_iff_meas_biInter hm).mpr
    intro S
    exact (iIndepFun_infinitePi (fun _ : ℕ=>measurable_id)).measure_inter_preimage_eq_mul S
      (sets:=fun _=>U) (fun _ _=>hU)
  have he : ∀n,P (A n)=μ U:=fun n=>
    (measurePreserving_eval_infinitePi (fun _ : ℕ=>μ) n).measure_preimage hU.nullMeasurableSet
  have ht : (∑'n,P (A n))=∞ := by
    simp_rw [he]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hpos.ne'
  have hl:=measure_limsup_eq_one hm hi ht
  have ha : ∀ᵐv ∂P,v∈limsup A atTop := by
    rw [ae_iff]
    change P ((limsup A atTop)ᶜ)=0
    rw [measure_compl (MeasurableSet.measurableSet_limsup hm) (measure_ne_top _ _),hl,measure_univ]
    simp
  exact ha.mono fun v hv=>mem_limsup_iff_frequently_mem.mp hv

theorem iid_sample_support_of_every_tail :
    ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ), ∀N:ℕ,
      μ.support⊆closure (v '' {n:ℕ|N≤n}) := by
  have hb : ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ),
      ∀U:TopologicalSpace.countableBasis E,0<μ U.val→∃ᶠn in atTop,v n∈U.val := by
    apply ae_all_iff.mpr
    intro U
    by_cases hp : 0<μ U.val
    · exact (iid_sample_frequently_mem μ
        (TopologicalSpace.isOpen_of_mem_countableBasis U.property).measurableSet hp).mono
        fun v hv _=>hv
    · exact Filter.Eventually.of_forall fun _ h=>False.elim (hp h)
  filter_upwards [hb] with v hv
  intro N x hx
  apply mem_closure_iff.mpr
  intro O hO hxO
  obtain ⟨U,hUb,hxU,hUO⟩:=
    (TopologicalSpace.isBasis_countableBasis E).exists_subset_of_mem_open hxO hO
  have hp : 0<μ U := (Measure.mem_support_iff_forall x).mp hx U
    ((TopologicalSpace.isOpen_of_mem_countableBasis hUb).mem_nhds hxU)
  obtain ⟨n,hn,hvn⟩:=frequently_atTop.mp (hv ⟨U,hUb⟩ hp) N
  exact ⟨v n,hUO hvn,⟨n,hn,rfl⟩⟩

omit [BorelSpace E] in theorem iid_sample_mem_support :
    ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ),∀n,v n∈μ.support := by
  apply ae_all_iff.mpr
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ=>μ) n).quasiMeasurePreserving.ae
    μ.support_mem_ae

end
end OverlapPaper
