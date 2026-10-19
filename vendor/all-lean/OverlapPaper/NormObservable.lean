module

public import OverlapPaper.SamplingDensity
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! The literal off-diagonal norm observable of Lemma 4.5. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace OverlapPaper

def normObservableDistance (R : ℕ→ℕ→ℝ) (i j : ℕ) : ℝ :=
  ⨆l:{l:ℕ//l≠i∧l≠j},|R i l.val-R j l.val|

def normObservable (R : ℕ→ℕ→ℝ) (i : ℕ) : ℝ :=
  ⨅j:{j:ℕ//j≠i},R i j.val+normObservableDistance R i j.val

theorem measurable_normObservableDistance (i j : ℕ) :
    Measurable (fun R:ℕ→ℕ→ℝ=>normObservableDistance R i j) := by
  apply Measurable.iSup
  intro l
  have hi : Measurable (fun R:ℕ→ℕ→ℝ=>R i l.val) :=
    (measurable_pi_apply l.val).comp (measurable_pi_apply i)
  have hj : Measurable (fun R:ℕ→ℕ→ℝ=>R j l.val) :=
    (measurable_pi_apply l.val).comp (measurable_pi_apply j)
  exact continuous_abs.measurable.comp (hi.sub hj)

theorem measurable_normObservable (i : ℕ) :
    Measurable (fun R:ℕ→ℕ→ℝ=>normObservable R i) := by
  apply Measurable.iInf
  intro j
  have hi : Measurable (fun R:ℕ→ℕ→ℝ=>R i j.val) :=
    (measurable_pi_apply j.val).comp (measurable_pi_apply i)
  exact hi.add (measurable_normObservableDistance i j.val)

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : ℕ→E)

private theorem others_nonempty (i j : ℕ) : Nonempty {l:ℕ//l≠i∧l≠j} :=
  ⟨⟨max i j+1,⟨by omega,by omega⟩⟩⟩

private theorem distinct_nonempty (i : ℕ) : Nonempty {j:ℕ//j≠i} :=
  ⟨⟨i+1,by omega⟩⟩

theorem normObservableDistance_le (hball : ∀l,‖v l‖≤1) (i j : ℕ) :
    normObservableDistance (fun i j=>inner ℝ (v i) (v j)) i j≤‖v i-v j‖ := by
  let:=others_nonempty i j
  apply ciSup_le
  intro l
  rw [←inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (hball l.val))

theorem normObservableDistance_bddAbove (hball : ∀l,‖v l‖≤1) (i j : ℕ) :
    BddAbove (range (fun l:{l:ℕ//l≠i∧l≠j}=>
      |inner ℝ (v i) (v l.val)-inner ℝ (v j) (v l.val)|)) := by
  refine ⟨‖v i-v j‖,?_⟩
  rintro a ⟨l,rfl⟩
  change |inner ℝ (v i) (v l.val)-inner ℝ (v j) (v l.val)|≤‖v i-v j‖
  rw [←inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (hball l.val))

theorem normObservableDistance_lower (hball : ∀l,‖v l‖≤1)
    (hdense : ∀N i,v i∈closure (v '' {n:ℕ|N≤n})) (i j : ℕ) :
    |‖v i‖^2-inner ℝ (v i) (v j)|≤
      normObservableDistance (fun i j=>inner ℝ (v i) (v j)) i j := by
  let d:=normObservableDistance (fun i j=>inner ℝ (v i) (v j)) i j
  have hc : IsClosed {x : E | |inner ℝ (v i-v j) x|≤d} :=
    isClosed_le (by fun_prop) continuous_const
  have hs : v '' {n:ℕ|max i j+1≤n}⊆{x : E | |inner ℝ (v i-v j) x|≤d} := by
    rintro x ⟨l,hl,rfl⟩
    change |inner ℝ (v i-v j) (v l)|≤d
    change max i j+1≤l at hl
    rw [inner_sub_left]
    exact le_ciSup (normObservableDistance_bddAbove v hball i j)
      ⟨l,⟨by omega,by omega⟩⟩
  have hx:=closure_minimal hs hc (hdense (max i j+1) i)
  change |inner ℝ (v i-v j) (v i)|≤d at hx
  rw [inner_sub_left,real_inner_self_eq_norm_sq,real_inner_comm (v i) (v j)] at hx
  exact hx

theorem normObservable_eq_norm_sq (hball : ∀l,‖v l‖≤1)
    (hdense : ∀N i,v i∈closure (v '' {n:ℕ|N≤n})) (i : ℕ) :
    normObservable (fun i j=>inner ℝ (v i) (v j)) i=‖v i‖^2 := by
  let:=distinct_nonempty i
  have hlo : ∀j:{j:ℕ//j≠i},‖v i‖^2 ≤ inner ℝ (v i) (v j.val)+
      normObservableDistance (fun i j=>inner ℝ (v i) (v j)) i j.val := by
    intro j
    have hh:=normObservableDistance_lower v hball hdense i j.val
    have ha:=le_abs_self (‖v i‖^2-inner ℝ (v i) (v j.val))
    linarith
  have hb : BddBelow (range (fun j:{j:ℕ//j≠i}=>inner ℝ (v i) (v j.val)+
      normObservableDistance (fun i j=>inner ℝ (v i) (v j)) i j.val)) := by
    exact ⟨‖v i‖^2,by rintro a ⟨j,rfl⟩;exact hlo j⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x,⟨j,hj,rfl⟩,hd⟩:=Metric.mem_closure_iff.mp (hdense (i+1) i) (ε/2) (by linarith)
    change i+1≤j at hj
    have hjne : j≠i:=by omega
    have hinf:=ciInf_le hb ⟨j,hjne⟩
    have hup:=normObservableDistance_le v hball i j
    have hi : inner ℝ (v i) (v j) ≤ ‖v i‖^2+‖v i-v j‖ := by
      have hh:=abs_real_inner_le_norm (v i) (v j-v i)
      have ht:=mul_le_of_le_one_left (norm_nonneg (v j-v i)) (hball i)
      rw [inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_rev] at hh
      rw [norm_sub_rev] at ht
      have hl:=le_abs_self (inner ℝ (v i) (v j)-‖v i‖^2)
      linarith
    rw [dist_eq_norm] at hd
    change normObservable (fun i j=>inner ℝ (v i) (v j)) i≤_ at hinf
    linarith
  · exact le_ciInf hlo

theorem normObservable_ball_iff (hball : ∀l,‖v l‖≤1)
    (hdense : ∀N i,v i∈closure (v '' {n:ℕ|N≤n})) (i j : ℕ) {ε : ℝ} (hε : 0<ε) :
    v j∈Metric.ball (v i) ε ↔
      normObservable (fun i j=>inner ℝ (v i) (v j)) i+
      normObservable (fun i j=>inner ℝ (v i) (v j)) j-
      2*inner ℝ (v i) (v j)<ε^2 := by
  rw [normObservable_eq_norm_sq v hball hdense i,
    normObservable_eq_norm_sq v hball hdense j]
  rw [Metric.mem_ball,dist_comm,dist_eq_norm]
  have he:=norm_sub_sq_real (v i) (v j)
  constructor
  · intro h
    nlinarith [norm_nonneg (v i-v j)]
  · intro h
    nlinarith [norm_nonneg (v i-v j)]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsProbabilityMeasure μ]

theorem iid_normObservable_eq (hball : ∀ᵐx ∂μ,‖x‖≤1) :
    ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ),∀i,
      normObservable (fun i j=>inner ℝ (v i) (v j)) i=‖v i‖^2 := by
  have hb : ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ),∀i,‖v i‖≤1 :=
    ae_all_iff.mpr fun i=>(measurePreserving_eval_infinitePi (fun _ : ℕ=>μ) i).quasiMeasurePreserving.ae hball
  filter_upwards [hb,iid_sample_mem_support μ,iid_sample_support_of_every_tail μ]
    with v hv hs hd
  exact fun i=>normObservable_eq_norm_sq v hv (fun N i=>hd N (hs i)) i

theorem iid_normObservable_and_balls (hball : ∀ᵐx ∂μ,‖x‖≤1) :
    ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ),
      (∀i,normObservable (fun i j=>inner ℝ (v i) (v j)) i=‖v i‖^2)∧
      (∀i j ε,0<ε→(v j∈Metric.ball (v i) ε ↔
        normObservable (fun i j=>inner ℝ (v i) (v j)) i+
        normObservable (fun i j=>inner ℝ (v i) (v j)) j-
        2*inner ℝ (v i) (v j)<ε^2)) := by
  have hb : ∀ᵐv:(ℕ→E) ∂Measure.infinitePi (fun _ : ℕ=>μ),∀i,‖v i‖≤1 :=
    ae_all_iff.mpr fun i=>(measurePreserving_eval_infinitePi (fun _ : ℕ=>μ) i).quasiMeasurePreserving.ae hball
  filter_upwards [hb,iid_sample_mem_support μ,iid_sample_support_of_every_tail μ]
    with v hv hs hd
  exact ⟨fun i=>normObservable_eq_norm_sq v hv (fun N i=>hd N (hs i)) i,
    fun i j ε hε=>normObservable_ball_iff v hv (fun N i=>hd N (hs i)) i j hε⟩

end
end OverlapPaper
