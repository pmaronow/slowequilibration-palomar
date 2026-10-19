-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionRegularity

/-! The literal retained selection event: a negative intrinsic Hessian
margin, normalized sphere derivatives, and the height bound at every point
of the specified positive-overlap band. No probability or loss estimate
enters its definition or Borel proof. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Filter Set Metric
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalPairCountGluing
open scoped ENNReal Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] Classical.propDecidable

def sourceOverlapBandHeight {N P:ℕ} (c:Degree P→ℝ) (ε η H:ℝ)
    (J:Disorder N P) (u:Vector N):Prop:=
  ∀ w:Vector N,‖w‖^2=(N:ℝ) → ε ≤ overlap u w → overlap u w ≤ 1-η → field c J w ≤ H

lemma sourceOverlapBandHeight_measurable {N P:ℕ} (c:Degree P→ℝ) (ε η H:ℝ) :
    MeasurableSet {p:Disorder N P×Vector N|sourceOverlapBandHeight c ε η H p.1 p.2}:=by
  let S:={w:Vector N|‖w‖^2=(N:ℝ)}
  let :CompactSpace S:=isCompact_iff_compactSpace.mp (sourceSphere_compact N)
  let B:={p:Disorder N P×Vector N|∃ w:S,ε ≤ overlap p.2 w ∧ overlap p.2 w ≤ 1-η ∧ H<field c p.1 w}
  let A:=fun m:ℕ=>{z:(Disorder N P×Vector N)×S|
    ε ≤ overlap z.1.2 z.2 ∧ overlap z.1.2 z.2 ≤ 1-η ∧ H+1/(m+1:ℝ) ≤ field c z.1.1 z.2}
  have hR:Continuous (fun z:(Disorder N P×Vector N)×S=>overlap z.1.2 z.2):=by
    unfold overlap
    fun_prop
  have hF:Continuous (fun z:(Disorder N P×Vector N)×S=>field c z.1.1 z.2):=
    (field_jointContinuous c).comp (continuous_fst.fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hA:∀ m,IsClosed (A m):=by
    intro m
    exact (isClosed_le continuous_const hR).inter
      ((isClosed_le hR continuous_const).inter (isClosed_le continuous_const hF))
  have hImage:∀ m,IsClosed (Prod.fst '' A m):=fun m=>isClosedMap_fst_of_compactSpace _ (hA m)
  have hEq:B=⋃ m:ℕ,Prod.fst '' A m:=by
    ext p
    simp only [B,mem_ofPred_eq,mem_iUnion,mem_image]
    constructor
    · rintro ⟨w,hε,hη,hH⟩
      obtain ⟨m,hm⟩:=exists_nat_one_div_lt (sub_pos.mpr hH)
      refine ⟨m,(p,w),?_,rfl⟩
      exact ⟨hε,hη,by linarith⟩
    · rintro ⟨m,⟨p',w⟩,hm,rfl⟩
      have hpos:0<(1:ℝ)/(m+1):=by positivity
      refine ⟨w,hm.1,hm.2.1,?_⟩
      have hf:=hm.2.2
      dsimp only [A] at hf
      linarith
  have hB:MeasurableSet B:=by rw [hEq];exact MeasurableSet.iUnion (fun m=>(hImage m).measurableSet)
  have hComp:{p:Disorder N P×Vector N|sourceOverlapBandHeight c ε η H p.1 p.2}=Bᶜ:=by
    ext p
    simp only [sourceOverlapBandHeight,B,mem_compl_iff,mem_ofPred_eq]
    constructor
    · intro h ⟨w,hε,hη,hH⟩
      exact (not_lt_of_ge (h w w.property hε hη)) hH
    · intro h w hw hε hη
      by_contra hbad
      exact h ⟨⟨w,hw⟩,hε,hη,lt_of_not_ge hbad⟩
  rw [hComp]
  exact hB.compl

def sourceSelectionEvent {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (u:Vector N):Prop:=
  sourceHessianMargin c κ J u ∧ sourceSphereRegularity c J ≤ C ∧
    sourceOverlapBandHeight c ε η ((N:ℝ)*(E-G/2)) J u

lemma sourceSelectionEvent_measurable {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ) :
    MeasurableSet {p:Disorder N P×Vector N|sourceSelectionEvent c κ C ε η E G p.1 p.2}:=
  (sourceHessianMargin_closed c κ).measurableSet.inter
    ((measurableSet_le ((sourceSphereRegularity_continuous c).measurable.comp measurable_fst) measurable_const).inter
      (sourceOverlapBandHeight_measurable c ε η ((N:ℝ)*(E-G/2))))

def sourceSelectionMark {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (u:Vector N):ℝ≥0∞:=
  if sourceSelectionEvent c κ C ε η E G J u then 1 else 0

lemma sourceSelectionMark_measurable {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ) :
    Measurable (fun p:Disorder N P×Vector N=>sourceSelectionMark c κ C ε η E G p.1 p.2):=
  Measurable.ite (sourceSelectionEvent_measurable c κ C ε η E G) measurable_const measurable_const

lemma sourceSelectionMark_le_one {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (u:Vector N) : sourceSelectionMark c κ C ε η E G J u ≤ 1:=by
  unfold sourceSelectionMark
  split_ifs <;> simp only [le_refl,zero_le]

def sourceRetainedScoreWindowCount {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G:ℝ)
    (J:Disorder (n+1) P):ℝ≥0∞:=
  actualScoreWindowCount n c K (sourceSelectionMark c κ C ε η E G) J

def sourceRetainedValueWindowCount {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (I:Set ℝ) (κ C ε η E G:ℝ) (J:Disorder (n+1) P):ℝ≥0∞:=
  actualValueWindowCount n c I (sourceSelectionMark c κ C ε η E G) J

end
end SlowEquilibration.PairConditionalDeterminantMoments
