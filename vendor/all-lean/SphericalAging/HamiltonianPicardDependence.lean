module

public import SphericalAging.JointLpRepresentative
public import SphericalAging.HamiltonianParameter

public section

/-! Actual parameter dependence of the Hamiltonian cutoff Picard classes.
Uniform tensor-coupling bounds are connected to the genuine predictable
Nemytskii maps, deterministic Volterra operator and matrix Itô operator.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.HamiltonianPicardDependence
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open WeightedPredictable WeightedPicard PicardDependence HamiltonianParameter
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma norm_indicator_toLp (T : ℝ≥0) (C : ℝ) (hC : 0 ≤ C) :
    ‖(memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
      (measurableSet_Ioc.prod MeasurableSet.univ) C
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).toLp
        ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => C))‖ =
      C * (initialScale (P := P) T : ℝ) := by
  rw [Lp.norm_toLp, eLpNorm_indicator_const
    (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet (by norm_num) (by norm_num),
    ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg hC]
  congr 1

lemma coefficient_family_sub_norm_bound {Kb Kh : ℝ≥0} {g h : State N → ℝ}
    (hg : LipschitzWith Kb g) (hh : LipschitzWith Kh h) (U : PredictableStateL2 N F P)
    (T : ℝ≥0) (C : ℝ) (hC : 0 ≤ C) (hgh : ∀ x, ‖g x-h x‖ ≤ C) :
    ‖predictableCoefficient hg U T - predictableCoefficient hh U T‖ ≤ C * (initialScale (P := P) T : ℝ) := by
  let W := (memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
      (measurableSet_Ioc.prod MeasurableSet.univ) C
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).toLp
        ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => C))
  have hw : ‖W‖ = C * (initialScale (P := P) T : ℝ) := norm_indicator_toLp T C hC
  rw [← hw]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [predictableCoefficient_coeFn hg U T, predictableCoefficient_coeFn hh U T,
    Lp.coeFn_sub (predictableCoefficient hg U T : TimeProcessL2 P) (predictableCoefficient hh U T),
    (memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
      (measurableSet_Ioc.prod MeasurableSet.univ) C
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))).coeFn_toLp]
    with q hgq hhq hsub hwq
  change ‖((predictableCoefficient hg U T : TimeProcessL2 P) -
    (predictableCoefficient hh U T : TimeProcessL2 P)) q‖ ≤ ‖(W : ℝ≥0 × Ω → ℝ) q‖
  rw [hsub]
  simp only [Pi.sub_apply, hgq, hhq]
  change (W : ℝ≥0 × Ω → ℝ) q = _ at hwq
  rw [hwq]
  by_cases hqt : q.1 ∈ Ioc (0 : ℝ≥0) T
  · rw [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hqt, mem_univ _⟩)]
    simp only [hqt, ite_true, Real.norm_of_nonneg hC]
    exact hgh _
  · rw [indicator_of_notMem (show q ∉ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from fun h => hqt h.1)]
    simp only [hqt, ite_false, sub_self, norm_zero]
    exact le_rfl

lemma finiteDrift_coefficient_family_sub_le {Kb Kh : ℝ≥0} {b c : Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hc : ∀ i, LipschitzWith Kh (c i))
    (U : PredictableStateL2 N F P) (T : ℝ≥0) (C : ℝ) (hC : 0 ≤ C)
    (hbc : ∀ i x, ‖b i x-c i x‖ ≤ C) :
    ‖finiteDriftPicardMap hb T U - finiteDriftPicardMap hc T U‖ ≤
      (N : ℝ) * T * C * (initialScale (P := P) T : ℝ) := by
  unfold finiteDriftPicardMap driftCoefficientMap
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖scalarToStatePredictable i (driftVolterra T (predictableCoefficient (hb i) U T)) -
        scalarToStatePredictable i (driftVolterra T (predictableCoefficient (hc i) U T))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (T : ℝ) * (C * (initialScale (P := P) T : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarToStatePredictable_sub, ← driftVolterra_sub]
      exact (norm_scalarToStatePredictable_le i _).trans
        ((norm_driftVolterra_le T _).trans (mul_le_mul_of_nonneg_left
          (coefficient_family_sub_norm_bound (hb i) (hc i) U T C hC (hbc i)) T.coe_nonneg))
    _ = _ := by simp; ring

lemma weighted_sourceClass_family_sub_bound (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b c : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hc : ∀ i, LipschitzWith Kb (c i))
    (hs : ∀ i j, LipschitzWith Ks (sigma i j)) (α : ℝ) (T : ℝ≥0) (Cd Ci : ℝ≥0)
    (hd : ∀ V : PredictableProcessL2 F P,
      ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖)
    (hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖)
    (hsmall : (N : ℝ≥0) * Cd * Kb + (N : ℝ≥0)^2 * Ci * Ks < 1)
    (A B : PredictableStateL2 N F P) (C : ℝ) (hC : 0 ≤ C) (hbc : ∀ i x, ‖b i x-c i x‖ ≤ C) :
    ‖multiply α T (sourceClass D hb hs T A-sourceClass D hc hs T B)‖ ≤
      (‖multiply α T (A-B)‖ + Real.exp (|α| *T) * (N : ℝ)*T*C*(initialScale (P := P) T : ℝ)) /
        (1-((N : ℝ)*Cd*Kb+(N : ℝ)^2*Ci*Ks)) := by
  let U := sourceClass D hb hs T A
  let V := sourceClass D hc hs T B
  have hU := sourceClass_fixedPoint D hb hs T A
  have hV := sourceClass_fixedPoint D hc hs T B
  have heq : U-V = ((A-B) + (finiteDriftPicardMap hb T U-finiteDriftPicardMap hb T V)) +
      (finiteDriftPicardMap hb T V-finiteDriftPicardMap hc T V) +
      (finiteNoisePicardMap D hs T U-finiteNoisePicardMap D hs T V) := by
    calc
      _ = (A+finiteDriftPicardMap hb T U+finiteNoisePicardMap D hs T U) -
        (B+finiteDriftPicardMap hc T V+finiteNoisePicardMap D hs T V) := congrArg₂ (·-·) hU hV
      _ = _ := by abel
  have hn : ‖multiply α T (U-V)‖ ≤ ‖multiply α T (A-B)‖ +
      Real.exp (|α| *T)*(N : ℝ)*T*C*(initialScale (P := P) T : ℝ) +
      ((N : ℝ)*Cd*Kb+(N : ℝ)^2*Ci*Ks)*‖multiply α T (U-V)‖ := by
    calc
      _ = ‖((multiply α T (A-B) + multiply α T (finiteDriftPicardMap hb T U-finiteDriftPicardMap hb T V)) +
        multiply α T (finiteDriftPicardMap hb T V-finiteDriftPicardMap hc T V)) +
        multiply α T (finiteNoisePicardMap D hs T U-finiteNoisePicardMap D hs T V)‖ := by
          rw [heq, multiply_add, multiply_add, multiply_add]
      _ ≤ ((‖multiply α T (A-B)‖ + ‖multiply α T (finiteDriftPicardMap hb T U-finiteDriftPicardMap hb T V)‖) +
        ‖multiply α T (finiteDriftPicardMap hb T V-finiteDriftPicardMap hc T V)‖) +
        ‖multiply α T (finiteNoisePicardMap D hs T U-finiteNoisePicardMap D hs T V)‖ := by
          exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ ((‖multiply α T (A-B)‖ + (N : ℝ)*Cd*Kb*‖multiply α T (U-V)‖) +
        Real.exp (|α| *T)*((N : ℝ)*T*C*(initialScale (P := P) T : ℝ))) +
        (N : ℝ)^2*Ci*Ks*‖multiply α T (U-V)‖ := by
          apply add_le_add
          · apply add_le_add
            · exact add_le_add le_rfl (norm_weighted_finiteDrift_sub_le hb α T Cd hd U V)
            · exact (norm_multiply_le α T _).trans (mul_le_mul_of_nonneg_left
                (finiteDrift_coefficient_family_sub_le hb hc V T C hC hbc) (Real.exp_pos _).le)
          · exact norm_weighted_finiteNoise_sub_le D hs α T Ci hi U V
      _ = _ := by ring
  have hq : (N : ℝ)*Cd*Kb+(N : ℝ)^2*Ci*Ks < 1 := by exact_mod_cast hsmall
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  change ‖multiply α T (U-V)‖ * _ ≤ _
  nlinarith

@[expose] abbrev BoundedDisorder (N p : ℕ) (A : ℝ≥0) := {J : FiniteModel.Disorder N p // ‖J‖ ≤ A}

@[expose] def driftBound (β : ℝ) (R : ℝ) (hR : 0 < R) (A : ℝ≥0) : ℝ≥0 :=
  (cutoffDrift_uniform_state_lipschitz (N := N) (p := p) β R hR A).choose

lemma drift_family_lipschitz (β : ℝ) (R : ℝ) (hR : 0 < R) (A : ℝ≥0)
    (J : BoundedDisorder N p A) (i : Fin N) :
    LipschitzWith (driftBound (N := N) (p := p) β R hR A) (CutoffSDE.cutoffDrift β J.1 R hR i) := by
  have h := (cutoffDrift_uniform_state_lipschitz (N := N) (p := p) β R hR A).choose_spec J.1 J.2
  change LipschitzWith (driftBound (N := N) (p := p) β R hR A)
    (fun x => (cutoffCoefficient R hR (hamiltonianDrift β J.1) x) i)
  simpa only [driftBound, one_mul, Function.comp_def] using
    (CutoffSDE.coordinate_lipschitz i).comp h

@[expose] def noiseBound (N : ℕ) (R : ℝ) (hR : 0 < R) : ℝ≥0 := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose

lemma noise_family_lipschitz (N : ℕ) (R : ℝ) (hR : 0 < R) :
    ∀ i j, LipschitzWith (noiseBound N R hR) (CutoffSDE.cutoffNoise N R hR i j) :=
  (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec

/-- The actual cutoff SDE horizon class, parameterized by finite disorder
and the initial state; all common Lipschitz hypotheses have been proved. -/
@[expose] def hamiltonianClass (D : BrownianDriver N P F) (β : ℝ) (R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (q : BoundedDisorder N p A × State N) : PredictableStateL2 N F P :=
  GlobalSDE.horizonClass D (drift_family_lipschitz β R hR A q.1) (noise_family_lipschitz N R hR) q.2 T

/-- The actual cutoff Picard state class is jointly Lipschitz in disorder
and initial data on every bounded disorder set and finite time horizon. -/
theorem hamiltonianClass_lipschitz (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ) (hR : 0 < R) (A T : ℝ≥0) :
    ∃ K : ℝ≥0, LipschitzWith K (hamiltonianClass (p := p) D β R hR A T) := by
  let Kb := driftBound (N := N) (p := p) β R hR A
  let Ks := noiseBound N R hR
  obtain ⟨α, hα, Cd, Ci, hCd, hCi, hsmall⟩ := exists_contraction_parameters N Kb Ks T
  obtain ⟨C, hC⟩ := cutoffDrift_disorder_lipschitz (N := N) (p := p) β R hR
  have hd : ∀ V : PredictableProcessL2 F P, ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖ := by
    intro V
    rw [hCd]
    exact WeightedDriftNorm.norm_weighted_driftVolterra_le hα T V
  have hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖ := by
    intro j V
    rw [hCi, one_div]
    exact WeightedItoNorm.norm_weighted_itoVolterra_le (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) hα T V
  let Q : ℝ := (N : ℝ)*Cd*Kb+(N : ℝ)^2*Ci*Ks
  have hQ : Q < 1 := by dsimp only [Q]; exact_mod_cast hsmall
  let L : ℝ := Real.exp (|α| *T)*Real.exp (|α| *T)*(initialScale (P := P) T : ℝ)*
    (1+(N : ℝ)*T*C)/(1-Q)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨⟨L, hL⟩, LipschitzWith.of_dist_le_mul (fun q r => ?_)⟩
  have hbc : ∀ i x, ‖CutoffSDE.cutoffDrift β q.1.1 R hR i x-CutoffSDE.cutoffDrift β r.1.1 R hR i x‖ ≤
      (C : ℝ)*‖q.1.1-r.1.1‖ := by
    intro i x
    change ‖(cutoffCoefficient R hR (hamiltonianDrift β q.1.1) x) i -
      (cutoffCoefficient R hR (hamiltonianDrift β r.1.1) x) i‖ ≤ _
    rw [← PiLp.sub_apply]
    exact (PiLp.norm_apply_le _ i).trans (hC _ _ x)
  have hnormSource : ‖multiply α T (initialClass (F := F) (P := P) q.2 T-initialClass r.2 T)‖ ≤
      Real.exp (|α| *T) * (dist q r * (initialScale (P := P) T : ℝ)) := by
    have hh := norm_multiply_le α T (initialClass (F := F) (P := P) q.2 T-initialClass r.2 T)
    rw [← initialClass_sub, norm_initialClass] at hh
    rw [← initialClass_sub]
    exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (by simpa only [dist_eq_norm] using (show dist q.2 r.2 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_right _ _)) (initialScale (P := P) T).coe_nonneg) (Real.exp_pos _).le)
  have hJ : ‖q.1.1-r.1.1‖ ≤ dist q r := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using (show dist q.1 r.1 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_left _ _)
  have hw := weighted_sourceClass_family_sub_bound D
    (drift_family_lipschitz β R hR A q.1) (drift_family_lipschitz β R hR A r.1)
    (noise_family_lipschitz N R hR) α T Cd Ci hd hi hsmall
    (initialClass (F := F) (P := P) q.2 T) (initialClass r.2 T)
    ((C : ℝ)*‖q.1.1-r.1.1‖) (mul_nonneg C.coe_nonneg (norm_nonneg _)) hbc
  change ‖multiply α T (hamiltonianClass D β R hR A T q-hamiltonianClass D β R hR A T r)‖ ≤ _ at hw
  have hnum : ‖multiply α T (initialClass (F := F) (P := P) q.2 T-initialClass r.2 T)‖ +
      Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*‖q.1.1-r.1.1‖)*(initialScale (P := P) T : ℝ) ≤
      Real.exp (|α| *T)*(dist q r*(initialScale (P := P) T : ℝ)) +
      Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*dist q r)*(initialScale (P := P) T : ℝ) := by
    apply add_le_add hnormSource
    gcongr
  simp only [dist_eq_norm]
  have hu : hamiltonianClass D β R hR A T q-hamiltonianClass D β R hR A T r =
      multiply (-α) T (multiply α T (hamiltonianClass D β R hR A T q-hamiltonianClass D β R hR A T r)) :=
    (inverse_multiply α T _).symm
  calc
    _ = ‖multiply (-α) T (multiply α T (hamiltonianClass D β R hR A T q-hamiltonianClass D β R hR A T r))‖ := congrArg norm hu
    _ ≤ Real.exp (|α| *T) * ‖multiply α T (hamiltonianClass D β R hR A T q-hamiltonianClass D β R hR A T r)‖ := by
      simpa only [abs_neg] using norm_multiply_le (-α) T (multiply α T (hamiltonianClass D β R hR A T q-hamiltonianClass D β R hR A T r))
    _ ≤ Real.exp (|α| *T) * ((Real.exp (|α| *T)*(dist q r*(initialScale (P := P) T : ℝ)) +
        Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*dist q r)*(initialScale (P := P) T : ℝ))/(1-Q)) :=
      mul_le_mul_of_nonneg_left (hw.trans ((div_le_div_iff_of_pos_right (sub_pos.mpr hQ)).mpr hnum)) (Real.exp_pos _).le
    _ = L * dist q r := by dsimp only [L]; ring

/-- An actual jointly measurable representative of the Hamiltonian cutoff
state class on a bounded disorder set. Every deterministic parameter slice
represents the actual constructed Picard class. -/
theorem exists_joint_hamiltonianClass_representative (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ) (hR : 0 < R) (A T : ℝ≥0) :
    ∃ G : (BoundedDisorder N p A × State N) × (ℝ≥0 × Ω) → State N,
      StronglyMeasurable G ∧ ∀ q,
        (fun z => G (q, z)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
          (hamiltonianClass D β R hR A T q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  obtain ⟨K, hK⟩ := hamiltonianClass_lipschitz (p := p) D β R hR A T
  have hsm : StronglyMeasurable (fun q =>
      (hamiltonianClass D β R hR A T q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) :=
    (continuous_subtype_val.comp hK.continuous).stronglyMeasurable
  exact JointLpRepresentative.exists_joint_representative _ hsm

end SphericalAging.HamiltonianPicardDependence
