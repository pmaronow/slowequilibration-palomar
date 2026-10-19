module
public import QuantitativePaper.VectorConditionalLaw
public import QuantitativePaper.VectorDensityExponent
public import FourPapersCommon.HistoryInitial

@[expose] public section

/-! Actual finite posterior chains begun at any fixed disorder and any field.
The spin expectation is the genuine derivative of the finite recursion, not a
conditional-law assumption. This retains the entire remaining Gaussian path. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorTailFieldLaw (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (j : ℕ) : Measure (FiniteHistory (VectorState n) j) :=
  finiteHistoryLaw (Measure.dirac (p,x)) (fun i => vectorProfileKernel s β t (k+2-j+i)) j

instance vectorTailFieldLaw_probability (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    IsProbabilityMeasure (vectorTailFieldLaw s β t p x j) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (fun i => vectorProfileKernel_markov s β t _) _

def vectorTailTerminalKernel (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    Kernel (FiniteHistory (VectorState n) j) (Configuration n) :=
  (terminalSpinKernel (fun z : VectorState n => vectorTerminalExponent n β t z.1 z.2)
    (measurable_vectorTerminalExponent_state n β t)).comap
      (fun h => h (Fin.last j)) (measurable_pi_apply _)

instance vectorTailTerminalKernel_markov (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    IsMarkovKernel (vectorTailTerminalKernel (n := n) s β t j) := by
  unfold vectorTailTerminalKernel
  infer_instance

def vectorTailPosteriorLaw (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (j : ℕ) : Measure (FiniteHistory (VectorState n) j × Configuration n) :=
  (vectorTailFieldLaw s β t p x j) ⊗ₘ vectorTailTerminalKernel s β t j

instance vectorTailPosteriorLaw_probability (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    IsProbabilityMeasure (vectorTailPosteriorLaw s β t p x j) := by
  unfold vectorTailPosteriorLaw
  infer_instance

theorem integral_vectorTailPosteriorLaw_spin (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (hj : j ≤ k+2)
    (d : Configuration n → ℝ) :
    (∫z,d z.2 ∂vectorTailPosteriorLaw s β t p x j)=
      vectorConditionalMean s β t p (fun _ => 0) d j 0 x := by
  let L := k+2-j
  let R := ∑σ : Configuration n,|d σ|
  have hd (σ) : |d σ| ≤ R :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hip : Integrable (fun z : FiniteHistory (VectorState n) j × Configuration n => d z.2)
      (vectorTailPosteriorLaw s β t p x j) := by
    apply memLp_one_iff_integrable.mp
    exact MemLp.of_bound ((measurable_of_finite d).comp measurable_snd).aestronglyMeasurable R
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hd z.2))
  have he : (∫z,d z.2 ∂vectorTailPosteriorLaw s β t p x j)=
      ∫h,vectorBackwardMean s β t d (L+j) (h (Fin.last j)) ∂vectorTailFieldLaw s β t p x j := by
    rw [vectorTailPosteriorLaw,Measure.integral_compProd hip]
    apply integral_congr_ae
    exact Eventually.of_forall (fun h => by
      dsimp only
      change (∫σ,d σ ∂terminalLaw (vectorTerminalExponent n β t (h (Fin.last j)).1 (h (Fin.last j)).2))=_
      rw [integral_terminalLaw]
      have he : L+j=k+2 := by dsimp only [L];omega
      rw [he,vectorBackwardMean_terminal])
  rw [he]
  change (∫h,vectorBackwardMean s β t d (L+j) (h (Fin.last j))
    ∂finiteHistoryLaw (Measure.dirac (p,x)) (fun i => vectorProfileKernel s β t (L+i)) j)=_
  rw [integral_history_backward_at_initial (Measure.dirac (p,x))
    (fun i => vectorProfileKernel s β t (L+i)) (fun i => vectorProfileKernel_markov s β t _)
    (fun i => vectorBackwardMean s β t d (L+i))
    (fun i => measurable_vectorBackwardMean s β t d _) R
    (fun i y => abs_vectorBackwardMean_le s β t d R hd _ y)
    (fun i y => by
      simpa only [Nat.add_assoc] using vectorBackwardMean_kernel s β t d (L+i) y) j,
    integral_dirac]
  unfold vectorBackwardMean
  have he : k+2-(L+0)=j := by dsimp only [L];omega
  rw [he]

end QuantitativePaper
