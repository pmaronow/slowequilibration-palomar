module
public import FourPapersCommon.FiniteStateCascadePosteriorDensity
public import FourPapersCommon.FiniteStateCascadeSmoothJets
public import QuantitativePaper.VectorTailTranslation

@[expose] public section

/-! Literal normalized Gaussian posterior log density, with fixed reference
noise coordinates and arbitrary initial finite-state field. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT QuantitativePaper
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1200000

def cascadePosteriorHistoryPotential (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (H : FiniteStateField S)
    (z : Fin j→Field n) : ℝ :=
  finiteStateGaussianTerminalCascade V a L (j-i)
    (historyExtended (cascadePosteriorHistory L j H z) i)

def cascadePosteriorLogDensity (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    (z : (Fin j→Field n)×S) : ℝ :=
  V z.2+(cascadePosteriorHistory L j H z.1 (Fin.last j)) z.2-
    cascadePosteriorHistoryPotential V a L j j H z.1+
    ∑i : Fin j,a (j-1-i)*(cascadePosteriorHistoryPotential V a L j (i+1) H z.1-
      cascadePosteriorHistoryPotential V a L j i H z.1)

theorem cascadePosteriorHistory_eq_initial_add
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    (z : Fin j→Field n) (i : Fin (j+1)) :
    cascadePosteriorHistory L j H z i=H+cascadePosteriorHistory L j 0 z i := by
  have hh := independentHistory_state_conjugate (cascadePosteriorUpdate L j) (fun Q=>H+Q)
    (fun i Q w=>by simp only [cascadePosteriorUpdate];abel) j ((0 : FiniteStateField S),z) i
  simpa only [zero_add,add_zero,cascadePosteriorHistory] using hh

theorem contDiff_cascadePosteriorHistory (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) :
    ContDiff ℝ ∞ (fun z : FiniteStateField S×(Fin j→Field n)=>cascadePosteriorHistory L j z.1 z.2) :=
  contDiff_independentHistory ∞ _ (fun i=>by unfold cascadePosteriorUpdate;fun_prop) j

theorem contDiff_cascadePosteriorHistoryPotential (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) :
    ContDiff ℝ ∞ (fun z : FiniteStateField S×(Fin j→Field n)=>
      cascadePosteriorHistoryPotential V a L j i z.1 z.2) :=
  (contDiff_finiteStateGaussianTerminalCascade V a ha L (j-i)).comp
    ((contDiff_apply ℝ (FiniteStateField S) _).comp (contDiff_cascadePosteriorHistory L j))

theorem contDiff_cascadePosteriorLogDensity (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (σ : S) :
    ContDiff ℝ ∞ (fun z : FiniteStateField S×(Fin j→Field n)=>
      cascadePosteriorLogDensity V a L j z.1 (z.2,σ)) := by
  unfold cascadePosteriorLogDensity
  have hh := (EuclideanSpace.proj σ).contDiff.comp
    ((contDiff_apply ℝ (FiniteStateField S) (Fin.last j)).comp (contDiff_cascadePosteriorHistory L j))
  exact ((((contDiff_const (c:=V σ)).add hh).sub (contDiff_cascadePosteriorHistoryPotential V a ha L j j)).add
    (ContDiff.sum (s:=Finset.univ) fun (i : Fin j) _=>(contDiff_const (c:=a (j-1-(i : ℕ)))).mul
      ((contDiff_cascadePosteriorHistoryPotential V a ha L j (i+1)).sub
        (contDiff_cascadePosteriorHistoryPotential V a ha L j i))))

theorem measurable_cascadePosteriorLogDensity (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Measurable (cascadePosteriorLogDensity V a L j H) :=
  measurable_from_prod_countable_left fun σ=>
    ((contDiff_cascadePosteriorLogDensity V a ha L j σ).comp
      (contDiff_const.prodMk contDiff_id)).continuous.measurable

theorem cascadePosteriorJointDensity_eq_exp_log (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S)
    (z : (Fin j→Field n)×S) :
    cascadePosteriorJointDensity V a L j (cascadePosteriorCoordinateMap L j H z)=
      ENNReal.ofReal (Real.exp (cascadePosteriorLogDensity V a L j H z)) := by
  let h := cascadePosteriorHistory L j H z.1
  have he (i : Fin j) : cascadePosteriorTransitionWeight V a L j i (h i.castSucc) (h i.succ)=
      ENNReal.ofReal (Real.exp (a (j-1-i)*(cascadePosteriorHistoryPotential V a L j (i+1) H z.1-
        cascadePosteriorHistoryPotential V a L j i H z.1))) := by
    rw [cascadePosteriorTransitionWeight,finiteStateGaussianNormalizer_terminal_eq_exp V a ha L]
    have hd : j-1-(i : ℕ)+1=j-i := by omega
    rw [hd,←Real.exp_sub]
    unfold cascadePosteriorHistoryPotential
    rw [historyExtended_left,historyExtended_right]
    have hd' : j-((i : ℕ)+1)=j-1-i := by omega
    rw [hd']
    congr 2
    ring
  change finiteHistoryDensity (cascadePosteriorTransitionWeight V a L j) j h *
    ENNReal.ofReal (gtStateGibbs V (h (Fin.last j)) z.2)=_
  rw [finiteHistoryDensity_eq_prod]
  simp_rw [he]
  rw [←ENNReal.ofReal_prod_of_nonneg (fun i _=>(Real.exp_pos _).le),←Real.exp_sum]
  have hG : gtStateGibbs V (h (Fin.last j)) z.2=
      Real.exp (V z.2+(h (Fin.last j)) z.2-gtStateLogPartition V (h (Fin.last j))) := by
    unfold gtStateGibbs gtStateLogPartition
    rw [Real.exp_sub,Real.exp_log (gtStatePartition_pos V _)]
    rw [add_comm]
  rw [hG,←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
  congr 2
  unfold cascadePosteriorLogDensity cascadePosteriorHistoryPotential
  have ht := historyExtended_fin (cascadePosteriorHistory L j H z.1) (Fin.last j)
  simp only [Fin.val_last] at ht
  rw [ht,Nat.sub_self]
  change _=V z.2+(h (Fin.last j)) z.2-gtStateLogPartition V (h (Fin.last j))+_
  ring

theorem cascadePosteriorGaussianLaw_eq_exp_density (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    cascadePosteriorGaussianLaw V a L j H=(cascadePosteriorGaussianBase S (Fin n) j).withDensity
      (fun z=>ENNReal.ofReal (Real.exp (cascadePosteriorLogDensity V a L j H z))) := by
  unfold cascadePosteriorGaussianLaw
  congr 1
  exact funext (cascadePosteriorJointDensity_eq_exp_log V a ha L j H)

theorem lintegral_cascadePosterior_exp (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    (∫⁻z,ENNReal.ofReal (Real.exp (cascadePosteriorLogDensity V a L j H z))
      ∂cascadePosteriorGaussianBase S (Fin n) j)=1 := by
  haveI := cascadePosteriorGaussianLaw_probability V a ha L j H
  have hh := measure_univ (μ:=cascadePosteriorGaussianLaw V a L j H)
  rw [cascadePosteriorGaussianLaw_eq_exp_density V a ha L j H,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  exact hh

theorem integrable_cascadePosterior_exp (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    Integrable (fun z=>Real.exp (cascadePosteriorLogDensity V a L j H z))
      (cascadePosteriorGaussianBase S (Fin n) j) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_cascadePosteriorLogDensity V a ha L j H).exp.aestronglyMeasurable)
    (Eventually.of_forall fun z=>(Real.exp_pos _).le)).mp
  rw [lintegral_cascadePosterior_exp V a ha L j H]
  exact ENNReal.one_ne_top

theorem integral_cascadePosterior_exp (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (H : FiniteStateField S) :
    (∫z,Real.exp (cascadePosteriorLogDensity V a L j H z)
      ∂cascadePosteriorGaussianBase S (Fin n) j)=1 := by
  have hh := ofReal_integral_eq_lintegral_ofReal (integrable_cascadePosterior_exp V a ha L j H)
    (Eventually.of_forall fun z=>(Real.exp_pos _).le)
  rw [lintegral_cascadePosterior_exp V a ha L j H] at hh
  have hn := integral_nonneg (μ:=cascadePosteriorGaussianBase S (Fin n) j)
    (f:=fun z=>Real.exp (cascadePosteriorLogDensity V a L j H z)) (fun z=>(Real.exp_pos _).le)
  have h := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal hn,ENNReal.toReal_one] using h

end FourPapersCommon
