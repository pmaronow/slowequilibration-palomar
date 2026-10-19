module
public import QuantitativeFollowup.AnisotropicFiniteDensity
public import QuantitativePaper.VectorDensityExponent

@[expose] public section

/-! Literal terminal-spin and full joint densities of the anisotropic
finite-profile model, and their exact physical Stieltjes exponent. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
variable {n k : ℕ}

theorem anisotropicFiniteSpinKernel_zero (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (P : AnisotropicParameter n) : anisotropicFiniteSpinKernel D s 0 P =
      (Measure.count : Measure (Configuration n)).withDensity
        (fun σ => ENNReal.ofReal (Real.exp (anisotropicTerminalLinear D σ P-
          anisotropicFinitePotential D s 0 P))) := by
  unfold anisotropicFiniteSpinKernel finiteStateCascadeGibbsKernel finiteStateCascadeFieldKernel
  rw [OverlapPaper.sourceKernelLaw,Kernel.comp_id,Kernel.comap_apply,finiteStateGibbsKernel_apply]
  congr 1
  funext σ
  congr 1
  unfold gtStateGibbs anisotropicFinitePotential finiteStateGaussianTerminalCascade
    finiteStateGaussianCascade gtStateLogPartition
  rw [Real.exp_sub,Real.exp_log (gtStatePartition_pos _ _)]
  simp only [anisotropicEnergyMap_apply,add_zero]

def anisotropicFiniteTerminalWeight (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p : FiniteHistory (AnisotropicParameter n) (k+2)) (σ : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (anisotropicTerminalLinear D σ (p (Fin.last (k+2)))-
    anisotropicFinitePotential D s 0 (p (Fin.last (k+2)))))

theorem measurable_anisotropicFiniteTerminalWeight (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : Measurable (Function.uncurry (anisotropicFiniteTerminalWeight D s)) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (((anisotropicTerminalLinear D σ).continuous.measurable.comp (measurable_pi_apply (Fin.last (k+2)))).sub
    ((contDiff_one_anisotropicFinitePotential D s 0).continuous.measurable.comp
      (measurable_pi_apply (Fin.last (k+2))))).exp.ennreal_ofReal

theorem anisotropicFiniteTerminalKernel_eq_withDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) : anisotropicFiniteTerminalKernel D s =
      (Kernel.const (FiniteHistory (AnisotropicParameter n) (k+2))
        (Measure.count : Measure (Configuration n))).withDensity (anisotropicFiniteTerminalWeight D s) := by
  ext p : 1
  rw [Kernel.withDensity_apply _ (measurable_anisotropicFiniteTerminalWeight D s),Kernel.const_apply]
  exact anisotropicFiniteSpinKernel_zero D s _

def anisotropicFiniteJointDensity (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (p : FiniteHistory (AnisotropicParameter n) (k+2)×Configuration n) : ℝ≥0∞ :=
  anisotropicFiniteHistoryDensity D s a p.1*anisotropicFiniteTerminalWeight D s p.1 p.2

theorem measurable_anisotropicFiniteJointDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : Measurable (anisotropicFiniteJointDensity D s a) :=
  ((measurable_anisotropicFiniteHistoryDensity D s a).comp measurable_fst).mul
    (measurable_anisotropicFiniteTerminalWeight D s)

theorem anisotropicFiniteJointLaw_eq_withDensity (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) : anisotropicFiniteJointLaw D s a =
      ((anisotropicFiniteBaseHistoryLaw D s).prod (Measure.count : Measure (Configuration n))).withDensity
        (anisotropicFiniteJointDensity D s a) := by
  haveI : IsSFiniteKernel ((Kernel.const (FiniteHistory (AnisotropicParameter n) (k+2))
      (Measure.count : Measure (Configuration n))).withDensity (anisotropicFiniteTerminalWeight D s)) := by
    rw [←anisotropicFiniteTerminalKernel_eq_withDensity]
    infer_instance
  unfold anisotropicFiniteJointLaw
  rw [anisotropicFiniteHistoryLaw_eq_withDensity,anisotropicFiniteTerminalKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity (measurable_anisotropicFiniteHistoryDensity D s a)
      (measurable_anisotropicFiniteTerminalWeight D s),Measure.compProd_const]
  rfl

def anisotropicHistoryPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (p : FiniteHistory (AnisotropicParameter n) (k+2)) (i : ℕ) : ℝ :=
  anisotropicFinitePotential D s (k+2-i) (historyExtended p i)

theorem anisotropicFinitePathDensity_eq_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (p : FiniteHistory (AnisotropicParameter n) (k+2)) :
    finiteHistoryDensity (anisotropicFiniteTransitionWeight D s) (k+2) p = ENNReal.ofReal
      (Real.exp (anisotropicHistoryPotential D s p (k+2)-
        ∑i ∈ Finset.range (k+1),(s.m (i+1)-s.m i)*anisotropicHistoryPotential D s p (i+1))) := by
  rw [finiteHistoryDensity_eq_prod]
  have he (i : Fin (k+2)) : anisotropicFiniteTransitionWeight D s i (p i.castSucc) (p i.succ) =
      ENNReal.ofReal (Real.exp (s.m i*(anisotropicHistoryPotential D s p (i+1)-
        anisotropicHistoryPotential D s p i))) := by
    rw [anisotropicFiniteTransitionWeight_eq_exp D s i (by omega)]
    unfold anisotropicHistoryPotential
    rw [historyExtended_right,historyExtended_left]
    have hd : k+2-((i:ℕ)+1) = k+1-i := by omega
    rw [hd]
  simp_rw [he]
  rw [←ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),←Real.exp_sum]
  congr 2
  rw [Fin.sum_univ_eq_sum_range
    (fun i => s.m i*(anisotropicHistoryPotential D s p (i+1)-anisotropicHistoryPotential D s p i)) (k+2),
    weighted_difference_sum s.m _ (k+1)]
  simp only [s.m_top,s.m_zero,one_mul,zero_mul,sub_zero]

theorem anisotropicFiniteJointDensity_eq_stieltjes (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (p : FiniteHistory (AnisotropicParameter n) (k+2))
    (σ : Configuration n) : anisotropicFiniteJointDensity D s a (p,σ) = ENNReal.ofReal
      (Real.exp (anisotropicTerminalLinear D σ (p (Fin.last (k+2)))-
        (∑i ∈ Finset.range (k+1),(s.m (i+1)-s.m i)*anisotropicHistoryPotential D s p (i+1))+
        a*anisotropicHistoryPotential D s p 0-Real.log (anisotropicFiniteOuterPartition D s a))) := by
  have hr : anisotropicHistoryPotential D s p 0 = anisotropicFinitePotential D s (k+2) (p 0) := by
    simp [anisotropicHistoryPotential,historyExtended]
  have ht : anisotropicHistoryPotential D s p (k+2) =
      anisotropicFinitePotential D s 0 (p (Fin.last (k+2))) := by
    unfold anisotropicHistoryPotential
    simp only [Nat.sub_self]
    congr 1
    simpa only [Fin.val_last] using historyExtended_fin p (Fin.last (k+2))
  rw [anisotropicFiniteJointDensity,anisotropicFiniteHistoryDensity,anisotropicFinitePathDensity_eq_stieltjes]
  unfold anisotropicFiniteInitialWeight anisotropicFiniteTerminalWeight
  rw [←Real.exp_log (anisotropicFiniteOuterPartition_pos D s a),←Real.exp_sub,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add,ht,hr,Real.exp_log (anisotropicFiniteOuterPartition_pos D s a)]
  congr 2
  ring

end QuantitativeFollowup
