module

public import SphericalAging.SecantPredictable
public import SphericalAging.VolterraLinearity
public import SphericalAging.ContinuousTimeCut

public section

/-! Nonlinear solution differences are genuine bounded predictable linear
SDEs with averaged Jacobian coefficients. The coefficients are constructed
from actual Fréchet derivatives, with bounds independent of the increment. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.StochasticDifferenceQuotient
open HardSphereDynamics LocalSDE SecantPredictable PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime VolterraLinearity
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section ActualStates
variable {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P} {T : ℝ≥0}
  (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y)
  (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
  (hYc : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
  (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
  (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
include hXeq hYeq

 theorem secant_finiteDrift {K : ℝ≥0} {b : Fin N → State N → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (b i)) (hb : ∀ i, LipschitzWith K (b i)) (c : ℝ) :
    LinearVariationalSDE.finiteDriftPicardMap
      (fun i => secantCoefficient X Y hXa hYa hXc hYc (hg i) (hb i) T) T (c • (V-U)) =
      c • (PredictableDriftTime.finiteDriftPicardMap hb T V-
        PredictableDriftTime.finiteDriftPicardMap hb T U) := by
  classical
  unfold LinearVariationalSDE.finiteDriftPicardMap LinearVariationalSDE.driftCoefficientMap
    PredictableDriftTime.finiteDriftPicardMap PredictableDriftTime.driftCoefficientMap
  rw [← Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [secant_apply_difference hXa hYa hXc hYc hXeq hYeq (hg i) (hb i) c,
    driftVolterra_smul,driftVolterra_sub,scalarToStatePredictable_smul,scalarToStatePredictable_sub]

 theorem secant_finiteNoise (D : BrownianDriver N P F) {K : ℝ≥0}
    {sigma : Fin N → Fin N → State N → ℝ}
    (hg : ∀ i j, ContDiff ℝ ∞ (sigma i j)) (hs : ∀ i j, LipschitzWith K (sigma i j)) (c : ℝ) :
    LinearVariationalSDE.finiteNoisePicardMap D
      (fun i j => secantCoefficient X Y hXa hYa hXc hYc (hg i j) (hs i j) T) T (c • (V-U)) =
      c • (PredictableItoTime.finiteNoisePicardMap D hs T V-
        PredictableItoTime.finiteNoisePicardMap D hs T U) := by
  classical
  unfold LinearVariationalSDE.finiteNoisePicardMap LinearVariationalSDE.stochasticCoefficientMap
    PredictableItoTime.finiteNoisePicardMap PredictableItoTime.stochasticCoefficientMap
  rw [← Finset.sum_sub_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← scalarToStatePredictable_sub,← scalarToStatePredictable_smul,← Finset.sum_sub_distrib,
    Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [secant_apply_difference hXa hYa hXc hYc hXeq hYeq (hg i j) (hs i j) c,
    itoVolterra_smul,itoVolterra_sub]

 theorem secant_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (sigma i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (x y : State N)
    (hU : U = initialClass (F := F) (P := P) x T+
      PredictableDriftTime.finiteDriftPicardMap hb T U+PredictableItoTime.finiteNoisePicardMap D hs T U)
    (hV : V = initialClass (F := F) (P := P) y T+
      PredictableDriftTime.finiteDriftPicardMap hb T V+PredictableItoTime.finiteNoisePicardMap D hs T V)
    (c : ℝ) : c • (V-U) = initialClass (F := F) (P := P) (c • (y-x)) T+
      LinearVariationalSDE.finiteDriftPicardMap
        (fun i => secantCoefficient X Y hXa hYa hXc hYc (hbg i) (hb i) T) T (c • (V-U))+
      LinearVariationalSDE.finiteNoisePicardMap D
        (fun i j => secantCoefficient X Y hXa hYa hXc hYc (hsg i j) (hs i j) T) T (c • (V-U)) := by
  rw [secant_finiteDrift hXa hYa hXc hYc hXeq hYeq hbg hb c,
    secant_finiteNoise hXa hYa hXc hYc hXeq hYeq D hsg hs c,
    initialClass_smul,PicardDependence.initialClass_sub]
  have hd := congrArg (fun z : PredictableStateL2 N F P => c • z) (congrArg₂ (fun v u => v-u) hV hU)
  simp only [smul_sub,smul_add] at hd ⊢
  exact hd.trans (by abel)

 theorem scaled_difference_timeCut (c : ℝ) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => c • (Y q.1 q.2-X q.1 q.2)))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((c • (V-U) : PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  filter_upwards [hXeq,hYeq,
    Lp.coeFn_smul c ((V-U : PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)),
    Lp.coeFn_sub (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) U] with q hx hy hsm hsub
  simp only [Submodule.coe_smul,Submodule.coe_sub] at hsm hsub ⊢
  rw [hsm,Pi.smul_apply,hsub,Pi.sub_apply,← hx,← hy]
  by_cases hq : q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) <;> simp [hq]

/-- The actual scaled nonlinear path difference agrees on a common event
with a constructed genuine linear strong solution, with the original
Lipschitz constants independent of the scale or initial increment. -/
 theorem exists_linear_scaled_difference (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (sigma i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (x y : State N)
    (hU : U = initialClass (F := F) (P := P) x T+
      PredictableDriftTime.finiteDriftPicardMap hb T U+PredictableItoTime.finiteNoisePicardMap D hs T U)
    (hV : V = initialClass (F := F) (P := P) y T+
      PredictableDriftTime.finiteDriftPicardMap hb T V+PredictableItoTime.finiteNoisePicardMap D hs T V)
    (c : ℝ) (hT : 0 < T) : ∃ Z,
      LinearVariationalSDE.IsStrongSolutionOn
        (fun i => secantCoefficient X Y hXa hYa hXc hYc (hbg i) (hb i) T)
        (fun i j => secantCoefficient X Y hXa hYa hXc hYc (hsg i j) (hs i j) T)
        D (c • (y-x)) Z T ∧
      ∀ᵐ omega ∂P, ∀ t, t ≤ T → Z t omega = c • (Y t omega-X t omega) := by
  let a := fun i => secantCoefficient X Y hXa hYa hXc hYc (hbg i) (hb i) T
  let s := fun i j => secantCoefficient X Y hXa hYa hXc hYc (hsg i j) (hs i j) T
  have hf := secant_fixedPoint hXa hYa hXc hYc hXeq hYeq D hbg hsg hb hs x y hU hV c
  let Z := LinearVariationalSDE.version D a s (c • (y-x)) T (c • (V-U))
  refine ⟨Z,LinearVariationalSDE.strongSolution_of_fixedPoint D a s _ T _ hf,?_⟩
  have hz := LinearVariationalSDE.version_timeCut_eq_fixedPoint_ae D a s (c • (y-x)) T _ hf
  have hq := scaled_difference_timeCut hXeq hYeq c
  have hqc : ∀ᵐ omega ∂P, Continuous (fun t => c • (Y t omega-X t omega)) := by
    filter_upwards [hXc,hYc] with omega hx hy
    exact (hy.sub hx).const_smul c
  exact ContinuousTimeCut.common_path_of_timeCut hT
    (LinearVariationalSDE.version_ae_continuous D a s _ T _) hqc (hz.trans hq.symm)
end ActualStates

/-- Actual constructed nonlinear solutions at two deterministic initial
points have the genuine bounded predictable secant linear-SDE semantics. -/
 theorem constructed_scaled_difference (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i, ContDiff ℝ ∞ (b i)) (hsg : ∀ i j, ContDiff ℝ ∞ (sigma i j))
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))
    (x y : State N) (T : ℝ≥0) (hT : 0 < T) (c : ℝ) : ∃ Z,
      LinearVariationalSDE.IsStrongSolutionOn
        (fun i => secantCoefficient (GlobalSDE.horizonProcess D hb hs x T)
          (GlobalSDE.horizonProcess D hb hs y T)
          (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
          (GlobalSDE.horizonProcess_stronglyAdapted D hb hs y T)
          (GlobalSDE.horizonProcess_continuous D hb hs x T)
          (GlobalSDE.horizonProcess_continuous D hb hs y T) (hbg i) (hb i) T)
        (fun i j => secantCoefficient (GlobalSDE.horizonProcess D hb hs x T)
          (GlobalSDE.horizonProcess D hb hs y T)
          (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
          (GlobalSDE.horizonProcess_stronglyAdapted D hb hs y T)
          (GlobalSDE.horizonProcess_continuous D hb hs x T)
          (GlobalSDE.horizonProcess_continuous D hb hs y T) (hsg i j) (hs i j) T)
        D (c • (y-x)) Z T ∧
      ∀ᵐ omega ∂P, ∀ t, t ≤ T → Z t omega = c •
        (GlobalSDE.horizonProcess D hb hs y T t omega-GlobalSDE.horizonProcess D hb hs x T t omega) :=
  exists_linear_scaled_difference
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs y T)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (GlobalSDE.horizonProcess_continuous D hb hs y T)
    (GlobalSDE.horizonProcess_timeCut D hb hs x T)
    (GlobalSDE.horizonProcess_timeCut D hb hs y T)
    D hbg hsg hb hs x y (GlobalSDE.horizonClass_fixedPoint D hb hs x T)
    (GlobalSDE.horizonClass_fixedPoint D hb hs y T) c hT

end SphericalAging.StochasticDifferenceQuotient
