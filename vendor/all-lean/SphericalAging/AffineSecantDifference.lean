module

public import SphericalAging.InhomogeneousLinearSDE
public import SphericalAging.TerminalStateRepresentation
public import SphericalAging.StochasticDifferenceQuotient

public section

/-! Changing the nonlinear drift produces an actual affine predictable
secant SDE for the difference of the constructed nonlinear solutions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.AffineSecantDifference
open HardSphereDynamics LocalSDE SecantCoefficient SecantPredictable PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime TerminalStateRepresentation InhomogeneousLinearSDE
set_option maxHeartbeats 1400000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem coefficient_actual_ae {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    {K : ℝ≥0} {g : State N → ℝ} (hg : LipschitzWith K g) :
    (predictableCoefficient hg U T : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t omega => g (X t omega)) T := by
  filter_upwards [hXeq,predictableCoefficient_coeFn hg U T] with q hx hc
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · have hx' : X q.1 q.2=(U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [indicator_of_mem (show q ∈ Ioc 0 T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hx
    simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,hx'] using hc
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false] using hc

@[expose]  def forcing (X : ℝ≥0 → Ω → State N) (ha : StronglyAdapted F X)
    (hc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    {Jb Kb B : ℝ≥0} {bJ bK : Fin N → State N → ℝ}
    (hbJ : ∀ i,LipschitzWith Jb (bJ i)) (hbK : ∀ i,LipschitzWith Kb (bK i))
    (hB : ∀ i x,‖bK i x-bJ i x‖ ≤ B) (T : ℝ≥0) (i : Fin N) : Forcing (F := F) (P := P) B where
  value := FourPapersCommon.continuousAdaptedTimeCut (fun t omega => bK i (X t omega)-bJ i (X t omega)) T
  predictable := FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _
    (fun t => ((hbK i).continuous.comp_stronglyMeasurable (ha t)).sub
      ((hbJ i).continuous.comp_stronglyMeasurable (ha t)))
    (hc.mono (fun omega h => ((hbK i).continuous.comp h).sub ((hbJ i).continuous.comp h))) T
  bound := .of_forall (fun q => by
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true] using hB i (X q.1 q.2)
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,norm_zero];exact B.coe_nonneg)

 section Constructed
 variable (D : BrownianDriver N P F) {Jb Kb Ks B : ℝ≥0}
    {bJ bK : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (bK i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hbJ : ∀ i,LipschitzWith Jb (bJ i)) (hbK : ∀ i,LipschitzWith Kb (bK i))
    (hs : ∀ i j,LipschitzWith Ks (s i j)) (hB : ∀ i x,‖bK i x-bJ i x‖ ≤ B)
    (x : State N) (T : ℝ≥0)

@[expose]  def difference : ℝ≥0 → Ω → State N := fun t omega =>
    GlobalSDE.horizonProcess D hbK hs x T t omega-GlobalSDE.horizonProcess D hbJ hs x T t omega

@[expose]  def driftRows (i : Fin N) : Coefficient (N := N) (F := F) (P := P) Kb :=
    secantCoefficient (GlobalSDE.horizonProcess D hbJ hs x T) (GlobalSDE.horizonProcess D hbK hs x T)
      (GlobalSDE.horizonProcess_stronglyAdapted D hbJ hs x T) (GlobalSDE.horizonProcess_stronglyAdapted D hbK hs x T)
      (GlobalSDE.horizonProcess_continuous D hbJ hs x T) (GlobalSDE.horizonProcess_continuous D hbK hs x T)
      (hbg i) (hbK i) T

@[expose]  def noiseRows (i j : Fin N) : Coefficient (N := N) (F := F) (P := P) Ks :=
    secantCoefficient (GlobalSDE.horizonProcess D hbJ hs x T) (GlobalSDE.horizonProcess D hbK hs x T)
      (GlobalSDE.horizonProcess_stronglyAdapted D hbJ hs x T) (GlobalSDE.horizonProcess_stronglyAdapted D hbK hs x T)
      (GlobalSDE.horizonProcess_continuous D hbJ hs x T) (GlobalSDE.horizonProcess_continuous D hbK hs x T)
      (hsg i j) (hs i j) T

@[expose]  def driftForcing (i : Fin N) : Forcing (F := F) (P := P) B :=
    forcing (GlobalSDE.horizonProcess D hbJ hs x T) (GlobalSDE.horizonProcess_stronglyAdapted D hbJ hs x T)
      (GlobalSDE.horizonProcess_continuous D hbJ hs x T) hbJ hbK hB T i

/-- The drift change and the averaged Jacobians are evaluated along actual
constructed nonlinear paths; the true affine matrix integral equation is
proved here. -/
 theorem difference_strongSolution : InhomogeneousLinearSDE.IsStrongSolutionOn
    (driftRows D hbg hbJ hbK hs x T) (noiseRows D hsg hbJ hbK hs x T)
    (driftForcing D hbJ hbK hs hB x T) D 0 (difference D hbJ hbK hs x T) T := by
  let X := GlobalSDE.horizonProcess D hbJ hs x T
  let Y := GlobalSDE.horizonProcess D hbK hs x T
  let U := GlobalSDE.horizonClass D hbJ hs x T
  let V := GlobalSDE.horizonClass D hbK hs x T
  let Z := difference D hbJ hbK hs x T
  let a := driftRows D hbg hbJ hbK hs x T
  let n := noiseRows D hsg hbJ hbK hs x T
  let f := driftForcing D hbJ hbK hs hB x T
  let A := fun i => predictableCoefficient (hbK i) V T-predictableCoefficient (hbJ i) U T
  let S := fun i j => predictableCoefficient (hs i j) V T-predictableCoefficient (hs i j) U T
  let hXa := GlobalSDE.horizonProcess_stronglyAdapted D hbJ hs x T
  let hYa := GlobalSDE.horizonProcess_stronglyAdapted D hbK hs x T
  let hXc := GlobalSDE.horizonProcess_continuous D hbJ hs x T
  let hYc := GlobalSDE.horizonProcess_continuous D hbK hs x T
  have hXeq := GlobalSDE.horizonProcess_timeCut D hbJ hs x T
  have hYeq := GlobalSDE.horizonProcess_timeCut D hbK hs x T
  have hZa : StronglyAdapted F Z := fun t => continuous_sub.comp_stronglyMeasurable ((hYa t).prodMk (hXa t))
  have hZc : ∀ᵐ omega ∂P,Continuous (fun t => Z t omega) := by
    filter_upwards [hXc,hYc] with omega hx hy
    exact hy.sub hx
  have hA : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t omega => (a i).value (t,omega) (Z t omega)+(f i).value (t,omega)) T := by
    intro i
    filter_upwards [Lp.coeFn_sub (predictableCoefficient (hbK i) V T : TimeProcessL2 P)
        (predictableCoefficient (hbJ i) U T),coefficient_actual_ae hYeq (hbK i),coefficient_actual_ae hXeq (hbJ i)]
        with q hd hy hx
    change ((predictableCoefficient (hbK i) V T-predictableCoefficient (hbJ i) U T : PredictableProcessL2 F P) : TimeProcessL2 P) q = _
    simp only [Submodule.coe_sub] at hd ⊢
    rw [hd,Pi.sub_apply,hy,hx]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
        a,driftRows,secantCoefficient,f,driftForcing,forcing,Z,difference]
      rw [secantRow_increment (hbg i)]
      ring
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_self]
  have hS : ∀ i j,(S i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t omega => (n i j).value (t,omega) (Z t omega)) T := by
    intro i j
    filter_upwards [Lp.coeFn_sub (predictableCoefficient (hs i j) V T : TimeProcessL2 P)
        (predictableCoefficient (hs i j) U T),coefficient_actual_ae hYeq (hs i j),coefficient_actual_ae hXeq (hs i j)]
        with q hd hy hx
    change ((predictableCoefficient (hs i j) V T-predictableCoefficient (hs i j) U T : PredictableProcessL2 F P) : TimeProcessL2 P) q = _
    simp only [Submodule.coe_sub] at hd ⊢
    rw [hd,Pi.sub_apply,hy,hx]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,n,noiseRows,secantCoefficient,Z,difference]
      exact (secantRow_increment (hsg i j) _ _).symm
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_self]
  refine ⟨hZa,hZc,A,S,hA,hS,?_⟩
  intro t ht i
  have hcX := nonlinear_terminalClass_ae D hbJ hs x T t U
  have hcY := nonlinear_terminalClass_ae D hbK hs x T t V
  have hcZ := terminalClass_ae D (0 : State N) A S T t
  have he : terminalClass D x (fun i => predictableCoefficient (hbK i) V T)
      (fun i j => predictableCoefficient (hs i j) V T) T t-
      terminalClass D x (fun i => predictableCoefficient (hbJ i) U T)
      (fun i j => predictableCoefficient (hs i j) U T) T t=terminalClass D 0 A S T t := by
    rw [terminalClass_sub,sub_self]
  have hd := Lp.coeFn_sub
    (terminalClass D x (fun i => predictableCoefficient (hbK i) V T) (fun i j => predictableCoefficient (hs i j) V T) T t)
    (terminalClass D x (fun i => predictableCoefficient (hbJ i) U T) (fun i j => predictableCoefficient (hs i j) U T) T t)
  have hdi := driftVersion_eq_actual_of_coe _ T (A i) (hA i)
  have hni := driverIto_ae_eq_versions D (S i) t
  filter_upwards [hcX,hcY,hcZ,hd,hdi,hni] with omega hx hy hz hd hdi hni
  rw [he] at hd
  have hstate : Z t omega=∑ l : Fin N,((0 : State N) l+driftVersion (A l) T t omega+
      ∑ j : Fin N,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (S l j) t omega) • basisVector l := by
    change LocalSDE.version D hbK hs x T V t omega-LocalSDE.version D hbJ hs x T U t omega=_
    rw [← hx,← hy,← Pi.sub_apply,← hd,hz]
  have hcoord := congrArg (VariationalCoefficients.coordinate i) hstate
  simp only [map_sum,map_smul,VariationalCoefficients.coordinate_apply,basisVector,
    PiLp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] at hcoord
  simpa only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    zero_apply,zero_add,hdi t ht,← hni] using hcoord
 end Constructed
end SphericalAging.AffineSecantDifference
