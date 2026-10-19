module

public import SphericalAging.HamiltonianDisorderLinearization
public import SphericalAging.HamiltonianFlowDerivative
public import SphericalAging.FlowCoefficientDerivative

public section

/-! Genuine Fréchet differentiation of the actual cutoff Hamiltonian SDE
in its ordered tensor disorder. The proof derives the local quadratic
error from the actual affine secant SDE, its fourth moments, and the true
Jacobian resolvent; the disorder derivative is not an assumed field. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianDisorderDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime HamiltonianPicardDependence
open StochasticTaylorRemainder StochasticLinearizationError LinearResolvent
open HamiltonianDisorderForcingOperator HamiltonianDisorderLinearization
open LinearSDETimeFourthMoment GlobalHamiltonianParameter
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem norm_remainder_le_parameter {E : Type*} [NormedAddCommGroup E] {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P} {T : ℝ≥0}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => Y q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    {K L : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g)
    (hder : LipschitzWith L (fderiv ℝ g))
    (hfour : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P))
    (C : ℝ) (hC : 0 ≤ C) (v : E)
    (hbound : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤ C*‖v‖^4) :
    ‖remainder hXa hXc hg hL T U V‖ ≤ (L : ℝ)*Real.sqrt C*‖v‖^2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (L : ℝ)^2 * (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
        (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) :=
      norm_remainder_sq_le hXa hXc hXeq hYeq hg hL hder hfour
    _ ≤ (L : ℝ)^2*(C*‖v‖^4) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hC];ring

 theorem bounded_increment_norm (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (A T : ℝ≥0) : ∃ K : ℝ≥0,∀ J K' : BoundedDisorder N p A,∀ x : State N,
      ‖hamiltonianClass D β R hR A T (K',x)-hamiltonianClass D β R hR A T (J,x)‖ ≤
        (K : ℝ)*‖K'.1-J.1‖ := by
  obtain ⟨K,hK⟩ := hamiltonianClass_lipschitz (p := p) D β R hR A T
  refine ⟨K,fun J K' x => ?_⟩
  have h := hK.dist_le_mul (K',x) (J,x)
  simpa only [Prod.dist_eq,Subtype.dist_eq,dist_self,dist_eq_norm,max_eq_left (norm_nonneg _)] using h

 theorem quadratic_error_bound (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (A : ℝ≥0) (J : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ K : BoundedDisorder N p A,
      ‖hamiltonianClass (NullAugmentation.driver D₀) β R hR A T (K,x)-
        hamiltonianClass (NullAugmentation.driver D₀) β R hR A T (J,x)-
        response (NullAugmentation.driver D₀) β R hR A J x T (K.1-J.1)‖ ≤ C*‖K.1-J.1‖^2 := by
  let D := NullAugmentation.driver D₀
  let hj := drift_family_lipschitz β R hR A J
  let hs := noise_family_lipschitz N R hR
  let X := GlobalSDE.horizonProcess D hj hs x T
  let U := hamiltonianClass D β R hR A T (J,x)
  let ha := GlobalSDE.horizonProcess_stronglyAdapted D hj hs x T
  let hc := GlobalSDE.horizonProcess_continuous D hj hs x T
  let a := HamiltonianDisorderLinearization.driftRows D β R hR A J x T
  let z := HamiltonianDisorderLinearization.noiseRows D β R hR A J x T
  let L := sourceLinearMap D a z T
  obtain ⟨Lb,hbd⟩ := HamiltonianFlowDerivative.cutoffDrift_derivative_uniform_lipschitz β J.1 R hR
  obtain ⟨Ls,hsd⟩ := HamiltonianFlowDerivative.cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  obtain ⟨Kh,hKh⟩ := bounded_increment_norm (p := p) D β R hR A T
  let C4 := HamiltonianDisorderIncrement.fourthConstant (N := N) (p := p) β R hR A T
  let Cb := (Lb : ℝ)*Real.sqrt C4
  let Cs := (Ls : ℝ)*Real.sqrt C4
  let Cc := (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*(Kh : ℝ)
  let C := ‖L‖*((N : ℝ)*T*(Cb+Cc)+(N : ℝ)^2*Real.sqrt T*Cs)
  refine ⟨C,by dsimp [C,Cb,Cc,Cs];positivity,?_⟩
  intro K
  let hk := drift_family_lipschitz β R hR A K
  let Y := GlobalSDE.horizonProcess D hk hs x T
  let V := hamiltonianClass D β R hR A T (K,x)
  let rb := fun i => remainder ha hc (cutoffDrift_contDiff β J.1 R hR i) (hj i) T U V
  let rs := fun i j => remainder ha hc (cutoffNoise_contDiff R hR i j) (hs i j) T U V
  let cross := fun i => forcingOperator β R hR T V i (K.1-J.1)-forcingOperator β R hR T U i (K.1-J.1)
  have h4 := HamiltonianDisorderIncrement.increment_fourthMoment D₀ β R hR A J K x T
  have hi : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [stateTimeCut_eq_indicator,HamiltonianDisorderIncrement.increment,AffineSecantDifference.difference] using
      h4.1.integrable_norm_pow (by norm_num)
  have hm : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤ C4*‖K.1-J.1‖^4 := by
    simpa only [stateTimeCut_eq_indicator,HamiltonianDisorderIncrement.increment,AffineSecantDifference.difference] using h4.2
  have hbr : ∀ i,‖rb i‖ ≤ Cb*‖K.1-J.1‖^2 := fun i =>
    norm_remainder_le_parameter ha hc (GlobalSDE.horizonProcess_timeCut D hj hs x T)
      (GlobalSDE.horizonProcess_timeCut D hk hs x T) (cutoffDrift_contDiff β J.1 R hR i) (hj i) (hbd i)
      hi _ (HamiltonianDisorderIncrement.fourthConstant_nonneg β R hR A T) (K.1-J.1) hm
  have hsr : ∀ i j,‖rs i j‖ ≤ Cs*‖K.1-J.1‖^2 := fun i j =>
    norm_remainder_le_parameter ha hc (GlobalSDE.horizonProcess_timeCut D hj hs x T)
      (GlobalSDE.horizonProcess_timeCut D hk hs x T) (cutoffNoise_contDiff R hR i j) (hs i j) (hsd i j)
      hi _ (HamiltonianDisorderIncrement.fourthConstant_nonneg β R hR A T) (K.1-J.1) hm
  have hcr : ∀ i,‖cross i‖ ≤ Cc*‖K.1-J.1‖^2 := by
    intro i
    calc
      _ ≤ (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*‖K.1-J.1‖*‖V-U‖ :=
        forcingOperator_state_sub_bound β R hR T U V i (K.1-J.1)
      _ ≤ (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*‖K.1-J.1‖*((Kh : ℝ)*‖K.1-J.1‖) :=
        mul_le_mul_of_nonneg_left (hKh J K x) (by positivity)
      _ = _ := by dsimp [Cc];ring
  have heq : V-U = L (driftSource T (fun i => forcingOperator β R hR T U i (K.1-J.1))+
      driftSource T rb+driftSource T cross+noiseSource D T rs) := increment_resolvent D β R hR A J K x T
  simp only [HamiltonianDisorderLinearization.response,ContinuousLinearMap.comp_apply,driftSourceOperator_apply,forcingVectorOperator,ContinuousLinearMap.pi_apply]
  change ‖V-U-L (driftSource T (fun i => forcingOperator β R hR T U i (K.1-J.1)))‖ ≤ _
  rw [heq,← map_sub]
  have he : driftSource T (fun i => forcingOperator β R hR T U i (K.1-J.1))+
      driftSource T rb+driftSource T cross+noiseSource D T rs-
      driftSource T (fun i => forcingOperator β R hR T U i (K.1-J.1)) =
      driftSource T rb+driftSource T cross+noiseSource D T rs := by abel
  rw [he]
  calc
    _ ≤ ‖L‖*‖driftSource T rb+driftSource T cross+noiseSource D T rs‖ := L.le_opNorm _
    _ ≤ ‖L‖*((‖driftSource T rb‖+‖driftSource T cross‖)+‖noiseSource D T rs‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) (norm_nonneg L)
    _ ≤ ‖L‖*((N : ℝ)*T*(Cb*‖K.1-J.1‖^2)+(N : ℝ)*T*(Cc*‖K.1-J.1‖^2)+
        (N : ℝ)^2*Real.sqrt T*(Cs*‖K.1-J.1‖^2)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (driftSource_norm_le T rb _ hbr) (driftSource_norm_le T cross _ hcr))
          (noiseSource_norm_le D T rs _ hsr)) (norm_nonneg L)
    _ = _ := by dsimp [C];ring

@[expose]  def disorderResponse (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    FiniteModel.Disorder N p →L[ℝ] PredictableStateL2 N F P :=
  response D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T

/-- Actual Fréchet derivative in every finite tensor disorder, with no
bounded-support restriction on the Gaussian disorder law. -/
 theorem globalClass_hasFDerivAt_disorder (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    HasFDerivAt (fun K : FiniteModel.Disorder N p => globalClass (NullAugmentation.driver D₀) β R hR T (K,x))
      (disorderResponse (NullAugmentation.driver D₀) β R hR J x T) J := by
  let D := NullAugmentation.driver D₀
  let A : ℝ≥0 := ‖J‖₊+1
  let jb : BoundedDisorder N p A := ⟨J,by simp [A]⟩
  obtain ⟨C,hC,hquad⟩ := quadratic_error_bound D₀ β R hR A jb x T
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hevent : ∀ᶠ K : FiniteModel.Disorder N p in 𝓝 J,‖K-J‖ < min 1 (ε/(C+1)) := by
    exact Filter.mem_of_superset (Metric.ball_mem_nhds J (lt_min zero_lt_one (div_pos hε (by linarith : 0 < C+1))))
      (fun K hK => by simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hK)
  filter_upwards [hevent] with K hK
  have hKA : ‖K‖₊ ≤ A := by
    rw [← NNReal.coe_le_coe]
    change ‖K‖ ≤ ‖J‖+1
    have hn' : ‖K‖ ≤ ‖K-J‖+‖J‖ := by simpa only [sub_add_cancel] using norm_add_le (K-J) J
    linarith [(lt_min_iff.mp hK).1]
  have h := hquad ⟨K,hKA⟩
  rw [← globalClass_eq_bounded D β R hR A T K hKA x,
      ← globalClass_eq_bounded D β R hR A T J jb.2 x] at h
  change ‖globalClass D β R hR T (K,x)-globalClass D β R hR T (J,x)-
      response D β R hR A jb x T (K-J)‖ ≤ _
  apply h.trans
  have hh : C*‖K-J‖ ≤ ε := by
    have he := (lt_div_iff₀ (by linarith : 0 < C+1)).mp ((lt_min_iff.mp hK).2)
    nlinarith [norm_nonneg (K-J)]
  nlinarith [norm_nonneg (K-J)]
end SphericalAging.HamiltonianDisorderDerivative
