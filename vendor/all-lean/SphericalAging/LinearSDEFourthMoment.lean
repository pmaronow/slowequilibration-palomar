module

public import SphericalAging.LinearVariationalSDE
public import SphericalAging.RadialProcess
public import SphericalAging.RadialUniqueness
public import SphericalAging.IntervalGronwall
public import SphericalAging.SpherePreservation

public section

/-! Fourth moments for actual bounded-coefficient linear stochastic equations.
The estimates use the constructed matrix Itô operator and its isometry.
No moment estimate is a field of the linear-equation data. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.LinearSDEFourthMoment
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto
set_option maxHeartbeats 1500000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The nonzero-initial integral Grönwall estimate used for the squared norm. -/
theorem integral_gronwall_bound (f : ℝ → ℝ) (a K T : ℝ) (hK : 0 ≤ K)
    (hf : Continuous f) (hle : ∀ t ∈ Icc 0 T, f t ≤ a + K * ∫ u in 0..t, f u) :
    ∀ t ∈ Icc 0 T, f t ≤ a * Real.exp (K*t) := by
  let G : ℝ → ℝ := fun t => a + K * ∫ u in 0..t, f u
  have hd (t : ℝ) : HasDerivAt G (K*f t) t := by
    exact ((intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul K).const_add a
  have hc : Continuous G := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hb := le_gronwallBound_of_liminf_deriv_right_le (δ := a) (K := K) (ε := 0)
    hc.continuousOn (fun t ht r hr => (hd t).hasDerivWithinAt.liminf_right_slope_le hr)
    (show G 0 ≤ a by simp [G]) (fun t ht => by
      simpa only [add_zero] using mul_le_mul_of_nonneg_left (hle t ⟨ht.1,ht.2.le⟩) hK)
  intro t ht
  exact (hle t ht).trans (by simpa only [gronwallBound_ε0,sub_zero] using hb t ht)

/-- An actual scalar integral equation with a deterministic initial value
has a finite second-moment estimate. The stochastic bound comes from the
proved full-filtration matrix isometry. -/
theorem nonzero_linear_equation_energy (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L M K : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (T : ℝ≥0) (z0 : ℝ)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖)
    (hU : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖)
    (heq : ∀ t, t ≤ T → ∀ᵐ omega ∂P, Z t omega = z0 + driftVersion A t t omega +
      (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega) (t : ℝ≥0) (ht : t ≤ T) :
    meanSquare (P := P) Z t ≤ 3*z0^2 +
      (3 * (T : ℝ) * (M : ℝ)^2 + 3 * N * (K : ℝ)^2) * energy (P := P) Z t := by
  have hdrift := integral_sq_driftVersion_le A t
  have hAenergy := restricted_norm_sq_le_energy Z hZa hZc L M hbound T t ht A hA
  have hnoise : (∫ omega, (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega ^ 2 ∂P) ≤
      (N : ℝ) * (K : ℝ)^2 * energy (P := P) Z t := by
    rw [PredictableItoTime.integral_sq_toLp _ (Lp.memLp _), Lp.toLp_coeFn,
      VectorIto.vectorProcessLp_norm_sq]
    calc
      _ ≤ ∑ j : Fin N, (K : ℝ)^2 * energy (P := P) Z t :=
        Finset.sum_le_sum (fun j _ =>
          restricted_norm_sq_le_energy Z hZa hZc L K hbound T t ht (U j) (hU j))
      _ = _ := by simp; ring
  have hbasic : meanSquare (P := P) Z t ≤ 3*z0^2 +
      3 * (∫ omega, driftVersion A t t omega ^ 2 ∂P) +
      3 * (∫ omega, (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega ^ 2 ∂P) := by
    calc
      _ ≤ ∫ omega, 3*z0^2 + 3 * driftVersion A t t omega ^ 2 +
          3 * (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega ^ 2 ∂P := by
        apply integral_mono_ae (bounded_memLp Z hZa L hbound t).integrable_sq
          ((integrable_const _).add ((driftVersion_memLp A t t).integrable_sq.const_mul 3) |>.add
            ((Lp.memLp (VectorIto.vectorProcessLp D U t)).integrable_sq.const_mul 3))
        filter_upwards [heq t ht] with omega homega
        dsimp only [Pi.add_apply]
        rw [homega]
        nlinarith [sq_nonneg (z0-driftVersion A t t omega),
          sq_nonneg (z0-(VectorIto.vectorProcessLp D U t : Ω → ℝ) omega),
          sq_nonneg (driftVersion A t t omega-(VectorIto.vectorProcessLp D U t : Ω → ℝ) omega)]
      _ = _ := by
        rw [integral_add,integral_add,integral_const,integral_const_mul,integral_const_mul]
        · simp
        · exact integrable_const _
        · exact (driftVersion_memLp A t t).integrable_sq.const_mul 3
        · exact (integrable_const _).add ((driftVersion_memLp A t t).integrable_sq.const_mul 3)
        · exact (Lp.memLp (VectorIto.vectorProcessLp D U t)).integrable_sq.const_mul 3
  have hd : (∫ omega, driftVersion A t t omega ^ 2 ∂P) ≤
      (T : ℝ) * (M : ℝ)^2 * energy (P := P) Z t := by
    calc
      _ ≤ (t : ℝ) * ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := hdrift
      _ ≤ (t : ℝ) * ((M : ℝ)^2 * energy (P := P) Z t) :=
        mul_le_mul_of_nonneg_left hAenergy t.coe_nonneg
      _ ≤ (T : ℝ) * ((M : ℝ)^2 * energy (P := P) Z t) :=
        mul_le_mul_of_nonneg_right (show (t : ℝ) ≤ T from ht)
          (mul_nonneg (sq_nonneg _) (energy_nonneg Z t))
      _ = _ := by ring
  nlinarith

/-- The actual bounded scalar equation has an explicit exponential
second-moment bound, independent of the localization radius `L`. -/
theorem nonzero_linear_equation_secondMoment (D : BrownianDriver N P F)
    (Z : ℝ≥0 → Ω → ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega)) (L M K : ℝ≥0)
    (hbound : ∀ᵐ omega ∂P, ∀ t, ‖Z t omega‖ ≤ L) (T : ℝ≥0) (z0 : ℝ)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖)
    (hU : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖)
    (heq : ∀ t, t ≤ T → ∀ᵐ omega ∂P, Z t omega = z0 + driftVersion A t t omega +
      (VectorIto.vectorProcessLp D U t : Ω → ℝ) omega) (t : ℝ≥0) (ht : t ≤ T) :
    meanSquare (P := P) Z t ≤ 3*z0^2 *
      Real.exp ((3*(T : ℝ)*(M : ℝ)^2+3*N*(K : ℝ)^2)*(t : ℝ)) := by
  let c : ℝ := 3*(T : ℝ)*(M : ℝ)^2+3*N*(K : ℝ)^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hf : Continuous (fun s : ℝ => meanSquare (P := P) Z s.toNNReal) :=
    (meanSquare_continuous Z hZa hZc L hbound).comp continuous_real_toNNReal
  have hb := integral_gronwall_bound (fun s => meanSquare (P := P) Z s.toNNReal)
    (3*z0^2) c T hc hf (by
      intro s hs
      have hst : s.toNNReal ≤ T := by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2
      have h := nonzero_linear_equation_energy D Z hZa hZc L M K hbound T z0 A U hA hU heq _ hst
      rw [energy_eq_real_integral, Real.coe_toNNReal _ hs.1] at h
      exact h)
  simpa only [Real.toNNReal_coe] using hb t ⟨t.coe_nonneg,ht⟩

/-- Coarse dimension-explicit radial drift bound for actual linear rows. -/
theorem radial_drift_bound (x : State N) (a : Fin N → ℝ) (b : Fin N → Fin N → ℝ)
    (Kb Ks : ℝ≥0) (ha : ∀ i, ‖a i‖ ≤ Kb*‖x‖) (hb : ∀ i j, ‖b i j‖ ≤ Ks*‖x‖) :
    ‖(∑ i,2*x i*a i)+(∑ i,∑ j,(b i j)^2)‖ ≤
      (2*N*(Kb : ℝ)+(N : ℝ)^2*(Ks : ℝ)^2)*‖x‖^2 := by
  have hfirst : ‖∑ i,2*x i*a i‖ ≤ (N : ℝ)*(2*Kb*‖x‖^2) := by
    calc
      _ ≤ ∑ i : Fin N,‖2*x i*a i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N,2*(Kb : ℝ)*‖x‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,norm_mul]
        have hc := PiLp.norm_apply_le x i
        have hm := mul_le_mul hc (ha i) (norm_nonneg _) (norm_nonneg _)
        rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
        nlinarith [hm]
      _ = _ := by simp
  have hsecond : ‖∑ i,∑ j,(b i j)^2‖ ≤ (N : ℝ)^2*(Ks : ℝ)^2*‖x‖^2 := by
    calc
      _ ≤ ∑ i : Fin N,‖∑ j : Fin N,(b i j)^2‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N,∑ _j : Fin N,(Ks : ℝ)^2*‖x‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro j _
        simpa only [norm_pow,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2
      _ = _ := by simp; ring
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans (by ring_nf; rfl))

/-- Every actual radial stochastic row is bounded linearly in the squared norm. -/
theorem radial_noise_bound (x : State N) (b : Fin N → ℝ) (Ks : ℝ≥0)
    (hb : ∀ i, ‖b i‖ ≤ Ks*‖x‖) :
    ‖∑ i,2*x i*b i‖ ≤ (2*N*(Ks : ℝ))*‖x‖^2 := by
  calc
    _ ≤ ∑ i : Fin N,‖2*x i*b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N,2*(Ks : ℝ)*‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_mul]
      have hm := mul_le_mul (PiLp.norm_apply_le x i) (hb i) (norm_nonneg _) (norm_nonneg _)
      rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
      nlinarith [hm]
    _ = _ := by simp; ring

@[expose] def squaredNorm (Y : ℝ≥0 → Ω → State N) : ℝ≥0 → Ω → ℝ := fun t ω => ‖Y t ω‖^2

@[expose] def radialDriftConstant (N : ℕ) (Kb Ks : ℝ≥0) : ℝ≥0 := 2*N*Kb+N^2*Ks^2

@[expose] def radialNoiseConstant (N : ℕ) (Ks : ℝ≥0) : ℝ≥0 := 2*N*Ks

/-- Genuine fourth-moment bound for a bounded actual matrix SDE. The
radial integral equation is derived by the proved norm-squared Itô theorem.
The constant does not depend on the stopping radius. -/
theorem bounded_matrix_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0 → Ω → State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀ ω, Continuous (fun t => Y t ω)) (R Kb Ks : ℝ≥0)
    (hYbound : ∀ t ω, ‖Y t ω‖ ≤ R) (T : ℝ≥0) (v0 : State N)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : Fin N → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i, (A i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ i q.1 q.2)
    (hμ : ∀ i, Measurable (Function.uncurry (μ i)))
    (hμint : ∀ i t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ i s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hAb : ∀ i, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(A i : TimeProcessL2 P) q‖ ≤ Kb*‖Y q.1 q.2‖)
    (hUb : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖ ≤ Ks*‖Y q.1 q.2‖)
    (hinitial : ∀ᵐ ω ∂P, Y 0 ω = v0)
    (heq : ∀ i t, SpherePreservation.coordinates Y i t =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) t ω + vectorProcess D (U i) t ω)
    (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖Y t ω‖^4 ∂P) ≤ 3*‖v0‖^4 * Real.exp
      ((3*(T : ℝ)*(radialDriftConstant N Kb Ks : ℝ)^2+
        3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) := by
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
  let Z := squaredNorm Y
  have hZa : StronglyAdapted F Z := fun s => (hYa s).norm.pow 2
  have hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) := .of_forall (fun ω => (hYc ω).norm.pow 2)
  have hZbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ (R^2 : ℝ≥0) := .of_forall (fun ω t => by
    dsimp [Z,squaredNorm]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hYbound t ω) 2)
  have hAs := ae_all_iff.mpr hAb
  have hUs := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUb i))
  have hB : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(B : TimeProcessL2 P) q‖ ≤ (radialDriftConstant N Kb Ks : ℝ)*‖Z q.1 q.2‖ := by
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUbound T,hAs,hUs]
      with q hb ha hu
    intro hq
    rw [hb]
    have hcut (i : Fin N) :
        FourPapersCommon.continuousAdaptedTimeCut (RadialItoRepresentation.twiceState (X i)) T q = 2*(Y q.1 q.2) i := by
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [hcut]
    have hh := radial_drift_bound (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
      (fun i j => (U i j : TimeProcessL2 P) q) Kb Ks ha hu
    simpa only [Z,squaredNorm,Real.norm_of_nonneg (sq_nonneg _),radialDriftConstant,
      NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,NNReal.coe_natCast] using hh
  have hV : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(V j : TimeProcessL2 P) q‖ ≤ (radialNoiseConstant N Ks : ℝ)*‖Z q.1 q.2‖ := by
    intro j
    filter_upwards [RadialProcess.radialNoise_coe U X hXa hXc R hXbound T j,hUs] with q hv hu
    intro hq
    rw [hv]
    have hcut (i : Fin N) :
        FourPapersCommon.continuousAdaptedTimeCut (RadialItoRepresentation.twiceState (X i)) T q = 2*(Y q.1 q.2) i := by
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [hcut]
    have hh := radial_noise_bound (Y q.1 q.2) (fun i => (U i j : TimeProcessL2 P) q) Ks (fun i => hu i j)
    simpa only [Z,squaredNorm,Real.norm_of_nonneg (sq_nonneg _),radialNoiseConstant,
      NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast] using hh
  have hZe : ∀ s, s ≤ T → ∀ᵐ ω ∂P, Z s ω = ‖v0‖^2 + driftVersion B s s ω +
      (vectorProcessLp D V s : Ω → ℝ) ω := by
    intro s hs
    have h := RadialProcess.quadratic_class_equation D A U X μ hXa hXc R hXbound S hUbound
      T s hs hA hμ hμint heq
    filter_upwards [h,hinitial] with ω hω h0
    have hsum (u : ℝ≥0) : (∑ i : Fin N,X i u ω^2)=‖Y u ω‖^2 := by
      simpa only [X,SpherePreservation.coordinates,real_inner_self_eq_norm_sq] using coordinate_square_sum (Y u ω)
    rw [hsum s,hsum 0,h0] at hω
    dsimp only [Z,squaredNorm]
    linarith
  have h := nonzero_linear_equation_secondMoment D Z hZa hZc (R^2)
    (radialDriftConstant N Kb Ks) (radialNoiseConstant N Ks) hZbound T (‖v0‖^2) B V hB hV hZe t ht
  simpa only [meanSquare,Z,squaredNorm,← pow_mul] using h

end SphericalAging.LinearSDEFourthMoment
