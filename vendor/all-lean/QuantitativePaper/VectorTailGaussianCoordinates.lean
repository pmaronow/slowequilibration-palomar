module
public import QuantitativePaper.VectorTailPosterior
public import QuantitativePaper.VectorCoordinateSmooth

@[expose] public section

/-! Genuine independent Gaussian coordinates for a remaining posterior chain
started at arbitrary initial field. No covariance or conditional-law premise
is supplied to the probability and density conclusions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorHistoryFrom (s : RSBScheme k) (β t : ℝ) (L : ℕ) (p : Couplings n × ℝ)
    (x : Field n) (j : ℕ) (z : Fin j → Field n) : FiniteHistory (VectorState n) j :=
  independentHistory (fun i => vectorCoordinateUpdate s β t (L+i)) j ((p,x),z)

theorem measurable_vectorHistoryFrom (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    Measurable (vectorHistoryFrom s β t L p x j) :=
  (measurable_independentHistory _ (fun i => measurable_vectorCoordinateUpdate s β t _) _).comp
    (measurable_const.prodMk measurable_id)

theorem vectorHistoryFrom_initial (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (z : Fin j → Field n) :
    vectorHistoryFrom s β t L p x j z 0=(p,x) := independentHistory_initial _ _ _

theorem vectorHistoryFrom_disorder (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) (z : Fin j → Field n) (i : Fin (j+1)) :
    (vectorHistoryFrom s β t L p x j z i).1=p :=
  independentHistory_preserved _ Prod.fst (fun i => vectorCoordinateUpdate_disorder s β t _) _ _ i

theorem vectorHistoryFrom_map (s : RSBScheme k) (β t : ℝ) (L : ℕ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    (Measure.pi (fun _ : Fin j => fieldGaussian n)).map (vectorHistoryFrom s β t L p x j)=
      finiteHistoryLaw (Measure.dirac (p,x)) (fun i => vectorProfileBaseKernel s β t (L+i)) j := by
  have hh := independentHistory_law (Measure.dirac (p,x)) (fieldGaussian n)
    (fun i => vectorCoordinateUpdate s β t (L+i))
    (fun i => measurable_vectorCoordinateUpdate s β t _)
    (fun i => vectorProfileBaseKernel s β t (L+i))
    (fun i => vectorProfileBaseKernel_markov s β t _)
    (fun i y => vectorProfileBaseKernel_eq_coordinateUpdate s β t _ y) j
  rw [Measure.dirac_prod,Measure.map_map
    (measurable_independentHistory _ (fun i => measurable_vectorCoordinateUpdate s β t _) _)
    measurable_prodMk_left] at hh
  exact hh

def vectorTailBaseFieldLaw (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (j : ℕ) : Measure (FiniteHistory (VectorState n) j) :=
  finiteHistoryLaw (Measure.dirac (p,x)) (fun i => vectorProfileBaseKernel s β t (k+2-j+i)) j

instance vectorTailBaseFieldLaw_probability (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    IsProbabilityMeasure (vectorTailBaseFieldLaw s β t p x j) :=
  isProbabilityMeasure_finiteHistoryLaw _ _ (fun i => vectorProfileBaseKernel_markov s β t _) _

def vectorTailPathDensity (s : RSBScheme k) (β t : ℝ) (j : ℕ)
    (h : FiniteHistory (VectorState n) j) : ℝ≥0∞ :=
  finiteHistoryDensity (fun i => vectorProfileWeight s β t (k+2-j+i)) j h

theorem measurable_vectorTailPathDensity (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    Measurable (vectorTailPathDensity (n := n) s β t j) :=
  measurable_finiteHistoryDensity _ (fun i => measurable_vectorProfileWeight s β t _) _

theorem vectorTailFieldLaw_density (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    vectorTailFieldLaw s β t p x j=
      (vectorTailBaseFieldLaw s β t p x j).withDensity (vectorTailPathDensity s β t j) :=
  finiteHistoryLaw_withDensity _ _ _ (fun i => vectorProfileBaseKernel_markov s β t _)
    (fun i => vectorProfileKernel_markov s β t _) _ (fun i => measurable_vectorProfileWeight s β t _)
    (fun i => vectorProfileKernel_eq_withDensity s β t _) j

def vectorTailJointDensity (s : RSBScheme k) (β t : ℝ) (j : ℕ)
    (z : FiniteHistory (VectorState n) j × Configuration n) : ℝ≥0∞ :=
  vectorTailPathDensity s β t j z.1*ENNReal.ofReal
    (terminalWeight (vectorTerminalExponent n β t (z.1 (Fin.last j)).1 (z.1 (Fin.last j)).2) z.2)

theorem measurable_vectorTailJointDensity (s : RSBScheme k) (β t : ℝ) (j : ℕ) :
    Measurable (vectorTailJointDensity (n := n) s β t j) := by
  unfold vectorTailJointDensity
  apply ((measurable_vectorTailPathDensity s β t j).comp measurable_fst).mul
  unfold terminalWeight terminalPartition vectorTerminalExponent fieldDot energy Paper.skHamiltonian
  fun_prop

theorem vectorTailPosteriorLaw_density (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    vectorTailPosteriorLaw s β t p x j=
      ((vectorTailBaseFieldLaw s β t p x j).prod (Measure.count : Measure (Configuration n))).withDensity
        (vectorTailJointDensity s β t j) := by
  let w := fun (h : FiniteHistory (VectorState n) j) (σ : Configuration n) => ENNReal.ofReal
    (terminalWeight (vectorTerminalExponent n β t (h (Fin.last j)).1 (h (Fin.last j)).2) σ)
  have hw : Measurable (Function.uncurry w) := by
    dsimp only [w]
    unfold terminalWeight terminalPartition vectorTerminalExponent fieldDot energy Paper.skHamiltonian
    fun_prop
  have he : vectorTailTerminalKernel (n := n) s β t j=
      (Kernel.const (FiniteHistory (VectorState n) j) (Measure.count : Measure (Configuration n))).withDensity w := by
    ext h : 1
    rw [Kernel.withDensity_apply _ hw,Kernel.const_apply]
    exact terminalLaw_eq_count_withDensity _
  haveI : IsSFiniteKernel ((Kernel.const (FiniteHistory (VectorState n) j)
      (Measure.count : Measure (Configuration n))).withDensity w) := by rw [←he];infer_instance
  rw [vectorTailPosteriorLaw,vectorTailFieldLaw_density,he,
    Measure.withDensity_compProd_withDensity (measurable_vectorTailPathDensity s β t j) hw,
    Measure.compProd_const]
  rfl

def vectorTailCoordinateJointMap (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (x : Field n) (j : ℕ) (z : (Fin j → Field n) × Configuration n) :
    FiniteHistory (VectorState n) j × Configuration n :=
  (vectorHistoryFrom s β t (k+2-j) p x j z.1,z.2)

theorem measurable_vectorTailCoordinateJointMap (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    Measurable (vectorTailCoordinateJointMap s β t p x j) :=
  (measurable_vectorHistoryFrom s β t _ p x j).prodMap measurable_id

def vectorTailGaussianBase (n j : ℕ) : Measure ((Fin j → Field n) × Configuration n) :=
  (Measure.pi (fun _ : Fin j => fieldGaussian n)).prod Measure.count

def vectorTailGaussianPosterior (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) : Measure ((Fin j → Field n) × Configuration n) :=
  (vectorTailGaussianBase n j).withDensity
    (fun z => vectorTailJointDensity s β t j (vectorTailCoordinateJointMap s β t p x j z))

theorem vectorTailGaussianPosterior_map (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    (vectorTailGaussianPosterior s β t p x j).map (vectorTailCoordinateJointMap s β t p x j)=
      vectorTailPosteriorLaw s β t p x j := by
  rw [vectorTailGaussianPosterior,map_withDensity_pullback _ _
    (measurable_vectorTailCoordinateJointMap s β t p x j) _ (measurable_vectorTailJointDensity s β t j)]
  change (((Measure.pi (fun _ : Fin j => fieldGaussian n)).prod Measure.count).map
    (Prod.map (vectorHistoryFrom s β t (k+2-j) p x j) id)).withDensity _=_
  rw [←Measure.map_prod_map _ _ (measurable_vectorHistoryFrom s β t _ p x j) measurable_id,
    vectorHistoryFrom_map,Measure.map_id,vectorTailPosteriorLaw_density]
  rfl

instance vectorTailGaussianPosterior_probability (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (j : ℕ) :
    IsProbabilityMeasure (vectorTailGaussianPosterior s β t p x j) := by
  constructor
  have hh := congrArg (fun P : Measure (FiniteHistory (VectorState n) j × Configuration n) => P univ)
    (vectorTailGaussianPosterior_map s β t p x j)
  rw [Measure.map_apply (measurable_vectorTailCoordinateJointMap s β t p x j) MeasurableSet.univ,preimage_univ] at hh
  exact hh.trans (measure_univ (μ := vectorTailPosteriorLaw s β t p x j))

end QuantitativePaper
