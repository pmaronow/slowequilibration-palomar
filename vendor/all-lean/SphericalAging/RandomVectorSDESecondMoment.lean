module

public import SphericalAging.VectorSDESecondMoment
public import SphericalAging.RandomInitialRadialMoment

public section

/-! Actual vector norm-squared Itô expectation bound with random initial
energy. No coordinate-count factors or moment assumptions on the solution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomVectorSDESecondMoment
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto
  LinearSDEFourthMoment AffineSDEFourthMoment VectorSDESecondMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine second-moment bound for a bounded actual matrix SDE. The
radial integral equation is derived by the proved norm-squared Itô theorem.
The constant does not depend on the stopping radius. -/
theorem bounded_randomInitial_vector_secondMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0 → Ω → State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀ ω, Continuous (fun t => Y t ω)) (R Kb Ks forcingBound driftBound noiseTraceBound : ℝ≥0)
    (hYbound : ∀ t ω, ‖Y t ω‖ ≤ R) (T : ℝ≥0) (Z0 : Ω → State N) (hZ0 : MemLp Z0 2 P)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : Fin N → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i, (A i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ i q.1 q.2)
    (hμ : ∀ i, Measurable (Function.uncurry (μ i)))
    (hμint : ∀ i t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ i s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hAb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun i => (A i : TimeProcessL2 P) q)‖ ≤
        driftBound*‖Y q.1 q.2‖+forcingBound)
    (hUtrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,∑ j : Fin N,((U i j : TimeProcessL2 P) q)^2) ≤
        noiseTraceBound*‖Y q.1 q.2‖^2)
    (hUb : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖ ≤ Ks*‖Y q.1 q.2‖)
    (hinitial : ∀ᵐ ω ∂P, Y 0 ω = Z0 ω)
    (heq : ∀ i t, SpherePreservation.coordinates Y i t =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) t ω + vectorProcess D (U i) t ω)
    (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖Y t ω‖^2 ∂P) ≤ ((forcingBound : ℝ)^2+(∫ ω,‖Z0 ω‖^2 ∂P)) * Real.exp
      (((2*driftBound+1+noiseTraceBound) : ℝ)*(t : ℝ)) := by
  let X := SpherePreservation.coordinates Y
  have hXa := SpherePreservation.coordinates_adapted hYa
  have hXc := SpherePreservation.coordinates_continuous (P := P) hYc
  have hXbound := SpherePreservation.coordinates_bound hYbound
  let S : ℝ≥0 := Ks*R
  have hUbound : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, ‖(U i j : ℝ≥0 × Ω → ℝ) q‖ ≤ S := by
    intro i j
    filter_upwards [hUb i j] with q hq
    exact hq.trans (mul_le_mul_of_nonneg_left (hYbound q.1 q.2) Ks.coe_nonneg)
  let B := RadialProcess.radialDrift A U X hXa hXc R hXbound S hUbound T
  let V := RadialProcess.radialNoise U X hXa hXc R hXbound T
  let Z : ℝ≥0 → Ω → ℝ := fun s ω => (forcingBound : ℝ)^2+‖Y s ω‖^2
  have hZa : StronglyAdapted F Z := fun s => ((hYa s).norm.pow 2).const_add _
  have hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) := .of_forall (fun ω => ((hYc ω).norm.pow 2).const_add _)
  have hZbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ (forcingBound^2+R^2 : ℝ≥0) := .of_forall (fun ω t => by
    dsimp [Z]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hYbound t ω) 2])
  have hUs := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUb i))
  have hB : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(B : TimeProcessL2 P) q‖ ≤ ((2*driftBound+1+noiseTraceBound) : ℝ)*‖Z q.1 q.2‖ := by
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUbound T,hAb,hUtrace]
      with q hb ha hu
    intro hq
    rw [hb]
    have hcut (i : Fin N) :
        FourPapersCommon.continuousAdaptedTimeCut (RadialItoRepresentation.twiceState (X i)) T q = 2*(Y q.1 q.2) i := by
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [hcut]
    have hh := vector_radial_drift_bound (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
      (fun i j => (U i j : TimeProcessL2 P) q) driftBound noiseTraceBound forcingBound ha hu
    change ‖_‖ ≤ ((2*driftBound+1+noiseTraceBound) : ℝ)*‖(forcingBound : ℝ)^2+‖Y q.1 q.2‖^2‖
    rw [Real.norm_of_nonneg (show 0 ≤ (forcingBound : ℝ)^2+‖Y q.1 q.2‖^2 by positivity)]
    exact hh
  have hZe : ∀ s, s ≤ T → ∀ᵐ ω ∂P, Z s ω = (forcingBound : ℝ)^2+‖Z0 ω‖^2 + driftVersion B s s ω +
      (vectorProcessLp D V s : Ω → ℝ) ω := by
    intro s hs
    have h := RadialProcess.quadratic_class_equation D A U X μ hXa hXc R hXbound S hUbound
      T s hs hA hμ hμint heq
    filter_upwards [h,hinitial] with ω hω h0
    have hsum (u : ℝ≥0) : (∑ i : Fin N,X i u ω^2)=‖Y u ω‖^2 := by
      simpa only [X,SpherePreservation.coordinates,real_inner_self_eq_norm_sq] using coordinate_square_sum (Y u ω)
    rw [hsum s,hsum 0,h0] at hω
    dsimp only [Z]
    linarith
  have hBs : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (B : TimeProcessL2 P) q ≤ ((2*driftBound+1+noiseTraceBound) : ℝ)*Z q.1 q.2 := by
    filter_upwards [hB] with q hq
    intro hqt
    have hh := hq hqt
    rw [Real.norm_of_nonneg (show 0 ≤ Z q.1 q.2 by dsimp [Z];positivity)] at hh
    exact (le_abs_self _).trans hh
  have hZ0i : Integrable (fun ω => ‖Z0 ω‖^2) P := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hZ0.integrable_norm_rpow'
  have h := RandomInitialRadialMoment.scalar_equation_randomInitial_firstMoment D Z hZa hZc (forcingBound^2+R^2)
    (2*driftBound+1+noiseTraceBound) hZbound T
    (fun ω => (forcingBound : ℝ)^2+‖Z0 ω‖^2) ((integrable_const _).add hZ0i) B V hBs hZe t ht
  have hint : (∫ ω,(forcingBound : ℝ)^2+‖Z0 ω‖^2 ∂P)=
      (forcingBound : ℝ)^2+∫ ω,‖Z0 ω‖^2 ∂P := by
    have hh := integral_add (integrable_const ((forcingBound : ℝ)^2)) hZ0i
    rw [hh,integral_const]
    simp
  rw [hint] at h
  refine (show (∫ ω,‖Y t ω‖^2 ∂P) ≤ SharpRadialMoment.firstMoment (P := P) Z t from ?_).trans h
  have hm : MemLp (Y t) 2 P := MemLp.of_bound
    ((hYa t).mono (F.le t)).aestronglyMeasurable R (.of_forall (hYbound t))
  apply integral_mono_ae
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hm.integrable_norm_rpow'
  · exact (bounded_memLp Z hZa (forcingBound^2+R^2) hZbound t).integrable (by norm_num)
  · exact .of_forall (fun ω => by dsimp [Z];nlinarith [sq_nonneg (forcingBound : ℝ)])

end SphericalAging.RandomVectorSDESecondMoment
