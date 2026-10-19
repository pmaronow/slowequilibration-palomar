module
public import QuantitativeFollowup.AnisotropicSpinModel
public import FourPapersCommon.FiniteStateCascadeExpectations
public import FourPapersCommon.FiniteStateCascadeLinearTransport
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-! The literal anisotropic finite-profile Hopf--Cole solution and its
honest normalized terminal spin law. No posterior inequality is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def anisotropicEnergyMap (D : AnisotropicSpinModel n) :
    AnisotropicParameter n→L[ℝ]FiniteStateField (Configuration n) :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun P=>WithLp.toLp 2 (fun σ=>anisotropicTerminalLinear D σ P)
      map_add':=by intro P Q;ext σ;simp
      map_smul':=by intro c P;ext σ;simp }

@[simp] theorem anisotropicEnergyMap_apply (D : AnisotropicSpinModel n)
    (P : AnisotropicParameter n) (σ : Configuration n) :
    anisotropicEnergyMap D P σ=anisotropicTerminalLinear D σ P := rfl

def anisotropicSchemeMass (s : RSBScheme k) (j : ℕ) : ℝ := s.m (k+1-j)

theorem anisotropicSchemeMass_nonneg (s : RSBScheme k) (j : ℕ) :
    0 ≤ anisotropicSchemeMass s j := s.m_nonneg (Nat.sub_le _ _)

def anisotropicSchemeInput (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    Field n→L[ℝ]AnisotropicParameter n :=
  Real.sqrt (s.q (k+2-j)-s.q (k+1-j)) •
    (anisotropicFieldInjection n).comp (anisotropicNoiseMap D)

@[simp] theorem anisotropicSchemeInput_apply (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (z : Field n) :
    anisotropicSchemeInput D s j z=anisotropicFieldInjection n
      (Real.sqrt (s.q (k+2-j)-s.q (k+1-j)) • anisotropicNoiseMap D z) := by
  simp only [anisotropicSchemeInput,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_smul]

def anisotropicFinitePotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) : ℝ :=
  finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j (anisotropicEnergyMap D P)

def anisotropicFiniteSpinKernel (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    Kernel (AnisotropicParameter n) (Configuration n) :=
  (finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).comap
      (anisotropicEnergyMap D) (anisotropicEnergyMap D).continuous.measurable

instance anisotropicFiniteSpinKernel_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) : IsMarkovKernel (anisotropicFiniteSpinKernel D s j) := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  unfold anisotropicFiniteSpinKernel
  infer_instance

def anisotropicFiniteFieldPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (ω : AnisotropicDisorder n) (x : Field n) : ℝ :=
  anisotropicFinitePotential D s j (anisotropicParameterPoint ω x)

theorem anisotropicFinitePotential_terminal (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicFiniteFieldPotential D s 0 ω x =
      Real.log (∑σ : Configuration n,Real.exp (anisotropicHamiltonian D ω x σ)) := by
  simp only [anisotropicFiniteFieldPotential,anisotropicFinitePotential,
    finiteStateGaussianTerminalCascade,finiteStateGaussianCascade,gtStateLogPartition,gtStatePartition,
    zero_add,add_zero,anisotropicEnergyMap_apply,anisotropicTerminalLinear_apply]

theorem anisotropicFinitePotential_coleHopf (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    anisotropicFinitePotential D s (j+1) P=
      OverlapPaper.sourceLogAverage (stdGaussian (Field n)) (anisotropicSchemeMass s j)
        (fun z=>anisotropicFinitePotential D s j (P+anisotropicSchemeInput D s j z)) := by
  unfold anisotropicFinitePotential finiteStateGaussianTerminalCascade
  rw [finiteStateGaussianCascade]
  unfold finiteStateGaussianStep
  congr 1
  funext z
  simp only [map_add,ContinuousLinearMap.comp_apply]

theorem contDiff_one_anisotropicFinitePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) : ContDiff ℝ 1 (anisotropicFinitePotential D s j) :=
  (contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).comp
    (anisotropicEnergyMap D).contDiff

theorem anisotropicFinitePotential_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    LipschitzWith ‖anisotropicEnergyMap D‖₊ (anisotropicFinitePotential D s j) := by
  apply LipschitzWith.of_dist_le_mul
  intro P Q
  rw [Real.dist_eq,dist_eq_norm]
  have hL:=finiteStateGaussianTerminalCascade_lipschitz (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  have hh:=hL.norm_sub_le (anisotropicEnergyMap D P) (anisotropicEnergyMap D Q)
  simp only [NNReal.coe_one,one_mul,Real.norm_eq_abs,←map_sub] at hh
  exact hh.trans ((anisotropicEnergyMap D).le_opNorm (P-Q))

theorem fderiv_anisotropicFinitePotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P K : AnisotropicParameter n) :
    fderiv ℝ (anisotropicFinitePotential D s j) P K=
      ∫σ,anisotropicTerminalLinear D σ K∂anisotropicFiniteSpinKernel D s j P := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  have hF:=contDiff_one_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  have hd:=(hF.differentiable_one.differentiableAt.hasFDerivAt.comp P
    (anisotropicEnergyMap D).hasFDerivAt).fderiv
  change fderiv ℝ (fun P=>F (anisotropicEnergyMap D P)) P=
    (fderiv ℝ F (anisotropicEnergyMap D P)).comp (anisotropicEnergyMap D) at hd
  rw [show anisotropicFinitePotential D s j=(fun P=>F (anisotropicEnergyMap D P)) from rfl,hd]
  exact fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
    (anisotropicEnergyMap D P) (anisotropicEnergyMap D K)

theorem anisotropicParameterPoint_field (ω : AnisotropicDisorder n) (x : Field n) :
    anisotropicParameterPoint ω x=anisotropicParameterPoint ω 0+anisotropicFieldInjection n x := by
  ext i
  cases i <;> simp [anisotropicParameterPoint,anisotropicFieldInjection]

theorem fderiv_anisotropicFiniteFieldPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (ω : AnisotropicDisorder n) (x v : Field n) :
    fderiv ℝ (anisotropicFiniteFieldPotential D s j ω) x v=
      ∫σ,fieldDot v σ∂anisotropicFiniteSpinKernel D s j (anisotropicParameterPoint ω x) := by
  have hP : HasFDerivAt (fun x : Field n=>anisotropicParameterPoint ω x)
      (anisotropicFieldInjection n) x := by
    simpa only [←anisotropicParameterPoint_field,add_comm] using
      ((anisotropicFieldInjection n).hasFDerivAt (x:=x)).const_add (anisotropicParameterPoint ω 0)
  have hU : HasFDerivAt (anisotropicFinitePotential D s j)
      (fderiv ℝ (anisotropicFinitePotential D s j) (anisotropicParameterPoint ω x))
      (anisotropicParameterPoint ω x) :=
    (contDiff_one_anisotropicFinitePotential D s j).differentiable_one.differentiableAt.hasFDerivAt
  have hd:=(hU.comp x hP).fderiv
  change fderiv ℝ (anisotropicFiniteFieldPotential D s j ω) x=
    (fderiv ℝ (anisotropicFinitePotential D s j) (anisotropicParameterPoint ω x)).comp
      (anisotropicFieldInjection n) at hd
  rw [hd,ContinuousLinearMap.comp_apply,fderiv_anisotropicFinitePotential]
  congr 1
  funext σ
  rw [anisotropicFieldInjection_apply,anisotropicTerminalLinear_apply]
  simp [anisotropicHamiltonian]

end QuantitativeFollowup
