module

public import SphericalAging.LocalRadialIto
public import SphericalAging.RandomInitialRadialMoment
public import SphericalAging.LinearSDELocalization

public section

/-! Actual scalar second moments from a second quadratic Itô identity.
The rate uses drift linearly and the true total noise square trace. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SharpScalarSecondMoment
open HardSphereDynamics PredictableDriftTime VectorIto RadialUniqueness
  LinearSDEFourthMoment LinearSDELocalization SharpRadialMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
lemma driftVersion_le_horizon (A : PredictableProcessL2 F P) (T s : ℝ≥0) (hs : s ≤ T) :
    driftVersion A T s=driftVersion A s s := by
  funext ω
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
    indicator_of_mem (show (r,ω) ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from
      ⟨⟨hr.1,hr.2.trans hs⟩,mem_univ _⟩),
    indicator_of_mem (show (r,ω) ∈ Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω) from ⟨hr,mem_univ _⟩)]

/-- A bounded actual scalar integral equation has the sharp squared-energy
estimate. Its quadratic drift and stochastic classes are constructed by
local Itô; no moment estimate or quadratic identity is a premise. -/
theorem scalar_equation_secondMoment (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P,Continuous (fun t => Z t ω)) (L M K S : ℝ≥0)
    (hbound : ∀ t ω,‖Z t ω‖ ≤ L) (T : ℝ≥0) (z0 : ℝ)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hAsupport : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∉ Ioc 0 T → (A : TimeProcessL2 P) q=0)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ)*‖Z q.1 q.2‖)
    (hUtrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (∑ j : Fin N,((U j : TimeProcessL2 P) q)^2) ≤ (K : ℝ)*(Z q.1 q.2)^2)
    (hUb : ∀ j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,‖(U j : TimeProcessL2 P) q‖ ≤ S)
    (heq : ∀ t,t ≤ T → ∀ᵐ ω ∂P,Z t ω=z0+driftVersion A t t ω+
      (vectorProcessLp D U t : Ω → ℝ) ω) (t : ℝ≥0) (ht : t ≤ T) :
    meanSquare (P := P) Z t ≤ z0^2*Real.exp (((2*M+K : ℝ≥0) : ℝ)*(t : ℝ)) := by
  obtain ⟨μ,hμm,hμint,hμsupport,hμcoe⟩ := exists_allPath_integrable_drift A T
  have hco : cutRepresentative A T=ᵐ[nonnegativeLebesgueMeasure.prod P] (A : TimeProcessL2 P) := by
    filter_upwards [representative_ae A,hAsupport] with q hr hs
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simpa only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
        indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hq,mem_univ _⟩)] using hr
    · simp [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq,hs hq]
  have hμA : (A : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P] Function.uncurry μ :=
    (hμcoe.trans hco).symm
  have hd := integratedDrift_eq_of_coe μ A T hμcoe
  have hzero : ∀ᵐ ω ∂P,Z 0 ω=z0 := by
    have hn := Lp.coeFn_zero ℝ 2 P
    have hh := heq 0 bot_le
    rw [vectorProcessLp_zero_time] at hh
    filter_upwards [hh,hn] with ω he hz
    simpa only [driftVersion,primitive,Ioc_self,Measure.restrict_empty,integral_zero_measure,hz,Pi.zero_apply,add_zero] using he
  have hdecomp : ∀ s,s ≤ T → Z s =ᵐ[P] fun ω => Z 0 ω+integratedDrift μ s ω+vectorProcess D U s ω := by
    intro s hs
    filter_upwards [heq s hs,hzero,hd,vectorProcessLp_ae_eq D U s] with ω he hz hd hn
    rw [hz,hd s,driftVersion_le_horizon A T s hs,← hn]
    exact he
  let X : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ => Z
  let AA : Fin 1 → PredictableProcessL2 F P := fun _ => A
  let UU : Fin 1 → Fin N → PredictableProcessL2 F P := fun _ => U
  let μμ : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ => μ
  let hXa : ∀ i,StronglyAdapted F (X i) := fun _ => hZa
  let hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun s => X i s ω) := fun _ => hZc
  let hXb : ∀ i s ω,‖X i s ω‖ ≤ L := fun _ => hbound
  let hUU : ∀ i j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,‖(UU i j : TimeProcessL2 P) q‖ ≤ S := fun _ => hUb
  let B := RadialProcess.radialDrift AA UU X hXa hXc L hXb S hUU T
  let V := RadialProcess.radialNoise UU X hXa hXc L hXb T
  let Y : ℝ≥0 → Ω → ℝ := fun s ω => (Z s ω)^2
  have hYa : StronglyAdapted F Y := fun s => (hZa s).pow 2
  have hYc : ∀ᵐ ω ∂P,Continuous (fun s => Y s ω) := hZc.mono (fun _ hz => hz.pow 2)
  have hYb : ∀ᵐ ω ∂P,∀ s,‖Y s ω‖ ≤ (L^2 : ℝ≥0) := .of_forall (fun ω s => by
    simpa only [Y,norm_pow,NNReal.coe_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound s ω) 2)
  have hB : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (B : TimeProcessL2 P) q ≤ ((2*M+K : ℝ≥0) : ℝ)*Y q.1 q.2 := by
    filter_upwards [RadialProcess.radialDrift_coe AA UU X hXa hXc L hXb S hUU T,hA,hUtrace]
      with q hb ha hu
    intro hq
    rw [hb]
    simp only [X,AA,UU,Fin.sum_univ_one,FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
      RadialItoRepresentation.twiceState]
    have hh : ‖2*Z q.1 q.2*(A : TimeProcessL2 P) q‖ ≤ 2*(M : ℝ)*(Z q.1 q.2)^2 := by
      rw [norm_mul,norm_mul,show ‖(2 : ℝ)‖=2 by norm_num]
      have hm := mul_le_mul_of_nonneg_left (ha hq) (show 0 ≤ 2*‖Z q.1 q.2‖ by positivity)
      calc
        _ ≤ 2*‖Z q.1 q.2‖*((M : ℝ)*‖Z q.1 q.2‖) := hm
        _ = _ := by rw [Real.norm_eq_abs];nlinarith [sq_abs (Z q.1 q.2)]
    have hs := (le_abs_self (2*Z q.1 q.2*(A : TimeProcessL2 P) q)).trans hh
    change _ ≤ ((2*M+K : ℝ≥0) : ℝ)*(Z q.1 q.2)^2
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
    linarith [hu hq]
  have hYe : ∀ s,s ≤ T → ∀ᵐ ω ∂P,Y s ω=z0^2+driftVersion B s s ω+
      (vectorProcessLp D V s : Ω → ℝ) ω := by
    intro s hs
    have hh := LocalRadialIto.quadratic_class_equation_on D AA UU X μμ hXa hXc L hXb S hUU T s hs
      (fun _ => hμA) (fun _ => hμm) (fun _ r => .of_forall (fun ω => (hμint ω).integrableOn))
      (fun _ => hdecomp)
    filter_upwards [hh,hzero] with ω he hz
    simp only [X,Fin.sum_univ_one,hz] at he
    dsimp only [Y]
    linarith
  exact scalar_equation_firstMoment D Y hYa hYc (L^2) (2*M+K) hYb T (z0^2) B V hB hYe t ht

theorem scalar_equation_randomInitial_secondMoment (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂P,Continuous (fun t => Z t ω)) (L M K S : ℝ≥0)
    (hbound : ∀ t ω,‖Z t ω‖ ≤ L) (T : ℝ≥0) (z0 : Ω → ℝ) (hz0 : MemLp z0 2 P)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hAsupport : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∉ Ioc 0 T → (A : TimeProcessL2 P) q=0)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ)*‖Z q.1 q.2‖)
    (hUtrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (∑ j : Fin N,((U j : TimeProcessL2 P) q)^2) ≤ (K : ℝ)*(Z q.1 q.2)^2)
    (hUb : ∀ j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,‖(U j : TimeProcessL2 P) q‖ ≤ S)
    (heq : ∀ t,t ≤ T → ∀ᵐ ω ∂P,Z t ω=z0 ω+driftVersion A t t ω+
      (vectorProcessLp D U t : Ω → ℝ) ω) (t : ℝ≥0) (ht : t ≤ T) :
    meanSquare (P := P) Z t ≤ (∫ ω,(z0 ω)^2 ∂P)*Real.exp (((2*M+K : ℝ≥0) : ℝ)*(t : ℝ)) := by
  obtain ⟨μ,hμm,hμint,hμsupport,hμcoe⟩ := exists_allPath_integrable_drift A T
  have hco : cutRepresentative A T=ᵐ[nonnegativeLebesgueMeasure.prod P] (A : TimeProcessL2 P) := by
    filter_upwards [representative_ae A,hAsupport] with q hr hs
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simpa only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
        indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hq,mem_univ _⟩)] using hr
    · simp [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq,hs hq]
  have hμA : (A : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P] Function.uncurry μ :=
    (hμcoe.trans hco).symm
  have hd := integratedDrift_eq_of_coe μ A T hμcoe
  have hzero : ∀ᵐ ω ∂P,Z 0 ω=z0 ω := by
    have hn := Lp.coeFn_zero ℝ 2 P
    have hh := heq 0 bot_le
    rw [vectorProcessLp_zero_time] at hh
    filter_upwards [hh,hn] with ω he hz
    simpa only [driftVersion,primitive,Ioc_self,Measure.restrict_empty,integral_zero_measure,hz,Pi.zero_apply,add_zero] using he
  have hdecomp : ∀ s,s ≤ T → Z s =ᵐ[P] fun ω => Z 0 ω+integratedDrift μ s ω+vectorProcess D U s ω := by
    intro s hs
    filter_upwards [heq s hs,hzero,hd,vectorProcessLp_ae_eq D U s] with ω he hz hd hn
    rw [hz,hd s,driftVersion_le_horizon A T s hs,← hn]
    exact he
  let X : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ => Z
  let AA : Fin 1 → PredictableProcessL2 F P := fun _ => A
  let UU : Fin 1 → Fin N → PredictableProcessL2 F P := fun _ => U
  let μμ : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ => μ
  let hXa : ∀ i,StronglyAdapted F (X i) := fun _ => hZa
  let hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun s => X i s ω) := fun _ => hZc
  let hXb : ∀ i s ω,‖X i s ω‖ ≤ L := fun _ => hbound
  let hUU : ∀ i j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,‖(UU i j : TimeProcessL2 P) q‖ ≤ S := fun _ => hUb
  let B := RadialProcess.radialDrift AA UU X hXa hXc L hXb S hUU T
  let V := RadialProcess.radialNoise UU X hXa hXc L hXb T
  let Y : ℝ≥0 → Ω → ℝ := fun s ω => (Z s ω)^2
  have hYa : StronglyAdapted F Y := fun s => (hZa s).pow 2
  have hYc : ∀ᵐ ω ∂P,Continuous (fun s => Y s ω) := hZc.mono (fun _ hz => hz.pow 2)
  have hYb : ∀ᵐ ω ∂P,∀ s,‖Y s ω‖ ≤ (L^2 : ℝ≥0) := .of_forall (fun ω s => by
    simpa only [Y,norm_pow,NNReal.coe_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound s ω) 2)
  have hB : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (B : TimeProcessL2 P) q ≤ ((2*M+K : ℝ≥0) : ℝ)*Y q.1 q.2 := by
    filter_upwards [RadialProcess.radialDrift_coe AA UU X hXa hXc L hXb S hUU T,hA,hUtrace]
      with q hb ha hu
    intro hq
    rw [hb]
    simp only [X,AA,UU,Fin.sum_univ_one,FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
      RadialItoRepresentation.twiceState]
    have hh : ‖2*Z q.1 q.2*(A : TimeProcessL2 P) q‖ ≤ 2*(M : ℝ)*(Z q.1 q.2)^2 := by
      rw [norm_mul,norm_mul,show ‖(2 : ℝ)‖=2 by norm_num]
      have hm := mul_le_mul_of_nonneg_left (ha hq) (show 0 ≤ 2*‖Z q.1 q.2‖ by positivity)
      calc
        _ ≤ 2*‖Z q.1 q.2‖*((M : ℝ)*‖Z q.1 q.2‖) := hm
        _ = _ := by rw [Real.norm_eq_abs];nlinarith [sq_abs (Z q.1 q.2)]
    have hs := (le_abs_self (2*Z q.1 q.2*(A : TimeProcessL2 P) q)).trans hh
    change _ ≤ ((2*M+K : ℝ≥0) : ℝ)*(Z q.1 q.2)^2
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
    linarith [hu hq]
  have hYe : ∀ s,s ≤ T → ∀ᵐ ω ∂P,Y s ω=(z0 ω)^2+driftVersion B s s ω+
      (vectorProcessLp D V s : Ω → ℝ) ω := by
    intro s hs
    have hh := LocalRadialIto.quadratic_class_equation_on D AA UU X μμ hXa hXc L hXb S hUU T s hs
      (fun _ => hμA) (fun _ => hμm) (fun _ r => .of_forall (fun ω => (hμint ω).integrableOn))
      (fun _ => hdecomp)
    filter_upwards [hh,hzero] with ω he hz
    simp only [X,Fin.sum_univ_one,hz] at he
    dsimp only [Y]
    linarith
  exact RandomInitialRadialMoment.scalar_equation_randomInitial_firstMoment D Y hYa hYc (L^2) (2*M+K)
    hYb T (fun ω => (z0 ω)^2) hz0.integrable_sq B V hB hYe t ht

end SphericalAging.SharpScalarSecondMoment
