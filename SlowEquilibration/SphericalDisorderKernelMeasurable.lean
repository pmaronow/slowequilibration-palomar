-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDynamics
public import SlowEquilibration.SphericalMixedCoefficientParameter
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SlowEquilibration.SphericalDynamics.ParameterFamily
open SphericalAging HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open WeightedPredictable WeightedPicard PicardDependence HamiltonianPicardDependence
open GlobalHamiltonianParameter PredictableTerminalOperators
open FourPapersCommon.FilteredBrownian

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Θ] [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

variable (D : BrownianDriver N P F)
  (b : Θ → Fin N → State N → ℝ)
  (hfixed : ∀ θ, ∃ K : ℝ≥0, ∀ i, LipschitzWith K (b θ i))
  (hstate : ∀ A : ℝ≥0, ∃ K : ℝ≥0, ∀ θ, ‖θ‖ ≤ A → ∀ i, LipschitzWith K (b θ i))
  (hparam : ∃ C : ℝ≥0, ∀ θ φ i x, ‖b θ i x - b φ i x‖ ≤ C * ‖θ-φ‖)
  {Ks : ℝ≥0} {sigma : Fin N → Fin N → State N → ℝ}
  (hs : ∀ i j, LipschitzWith Ks (sigma i j))

abbrev BoundedParameter (A : ℝ≥0) := {θ : Θ // ‖θ‖ ≤ A}

def driftBound (A : ℝ≥0) : ℝ≥0 := (hstate A).choose

omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem boundedDrift_lipschitz (A : ℝ≥0) (θ : BoundedParameter (Θ := Θ) A) (i : Fin N) :
    LipschitzWith (driftBound b hstate A) (b θ.1 i) :=
  (hstate A).choose_spec θ.1 θ.2 i

def boundedClass (A T : ℝ≥0) (q : BoundedParameter (Θ := Θ) A × State N) :
    PredictableStateL2 N F P :=
  GlobalSDE.horizonClass D (boundedDrift_lipschitz b hstate A q.1) hs q.2 T

include hparam in
omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem boundedClass_lipschitz (A T : ℝ≥0) :
    ∃ K : ℝ≥0, LipschitzWith K (boundedClass D b hstate hs A T) := by
  let Kb := driftBound b hstate A
  obtain ⟨α, hα, Cd, Ci, hCd, hCi, hsmall⟩ := exists_contraction_parameters N Kb Ks T
  obtain ⟨C, hC⟩ := hparam
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
  have hbc : ∀ i x, ‖b q.1.1 i x-b r.1.1 i x‖ ≤ (C : ℝ)*‖q.1.1-r.1.1‖ :=
    fun i x => hC q.1.1 r.1.1 i x
  have hnormSource : ‖multiply α T (initialClass (F := F) (P := P) q.2 T-initialClass r.2 T)‖ ≤
      Real.exp (|α| *T) * (dist q r * (initialScale (P := P) T : ℝ)) := by
    have hh := norm_multiply_le α T (initialClass (F := F) (P := P) q.2 T-initialClass r.2 T)
    rw [← initialClass_sub, norm_initialClass] at hh
    rw [← initialClass_sub]
    exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (by simpa only [dist_eq_norm] using
        (show dist q.2 r.2 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_right _ _))
      (initialScale (P := P) T).coe_nonneg) (Real.exp_pos _).le)
  have hθ : ‖q.1.1-r.1.1‖ ≤ dist q r := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using
      (show dist q.1 r.1 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_left _ _)
  have hw := weighted_sourceClass_family_sub_bound D
    (boundedDrift_lipschitz b hstate A q.1) (boundedDrift_lipschitz b hstate A r.1)
    hs α T Cd Ci hd hi hsmall
    (initialClass (F := F) (P := P) q.2 T) (initialClass r.2 T)
    ((C : ℝ)*‖q.1.1-r.1.1‖) (mul_nonneg C.coe_nonneg (norm_nonneg _)) hbc
  change ‖multiply α T (boundedClass D b hstate hs A T q-boundedClass D b hstate hs A T r)‖ ≤ _ at hw
  have hnum : ‖multiply α T (initialClass (F := F) (P := P) q.2 T-initialClass r.2 T)‖ +
      Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*‖q.1.1-r.1.1‖)*(initialScale (P := P) T : ℝ) ≤
      Real.exp (|α| *T)*(dist q r*(initialScale (P := P) T : ℝ)) +
      Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*dist q r)*(initialScale (P := P) T : ℝ) := by
    apply add_le_add hnormSource
    gcongr
  simp only [dist_eq_norm]
  have hu : boundedClass D b hstate hs A T q-boundedClass D b hstate hs A T r =
      multiply (-α) T (multiply α T (boundedClass D b hstate hs A T q-boundedClass D b hstate hs A T r)) :=
    (inverse_multiply α T _).symm
  calc
    _ = ‖multiply (-α) T (multiply α T (boundedClass D b hstate hs A T q-boundedClass D b hstate hs A T r))‖ := congrArg norm hu
    _ ≤ Real.exp (|α| *T) * ‖multiply α T (boundedClass D b hstate hs A T q-boundedClass D b hstate hs A T r)‖ := by
      simpa only [abs_neg] using norm_multiply_le (-α) T (multiply α T (boundedClass D b hstate hs A T q-boundedClass D b hstate hs A T r))
    _ ≤ Real.exp (|α| *T) * ((Real.exp (|α| *T)*(dist q r*(initialScale (P := P) T : ℝ)) +
        Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*dist q r)*(initialScale (P := P) T : ℝ))/(1-Q)) :=
      mul_le_mul_of_nonneg_left (hw.trans ((div_le_div_iff_of_pos_right (sub_pos.mpr hQ)).mpr hnum)) (Real.exp_pos _).le
    _ = L * dist q r := by dsimp only [L]; ring

def globalClass (T : ℝ≥0) (q : Θ × State N) : PredictableStateL2 N F P :=
  GlobalSDE.horizonClass D (hfixed q.1).choose_spec hs q.2 T

omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem globalClass_eq_bounded (A T : ℝ≥0) (θ : Θ) (hθ : ‖θ‖ ≤ A) (x : State N) :
    globalClass D b hfixed hs T (θ,x) = boundedClass D b hstate hs A T (⟨θ,hθ⟩,x) :=
  horizonClass_drift_bound_independent D _ _ _ x T

omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
private theorem continuous_of_bounded_lipschitz {V : Type*} [PseudoMetricSpace V]
    (f : Θ × State N → V)
    (fA : (A : ℝ≥0) → BoundedParameter (Θ := Θ) A × State N → V)
    (hA : ∀ A, ∃ K : ℝ≥0, LipschitzWith K (fA A))
    (he : ∀ (A : ℝ≥0) θ (hθ : ‖θ‖ ≤ A) x, f (θ,x)=fA A (⟨θ,hθ⟩,x)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let A : ℝ≥0 := ‖q.1‖₊+1
  have hqA : ‖q.1‖ ≤ A := by dsimp [A]; simp
  obtain ⟨K,hK⟩ := hA A
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 (ε/((K : ℝ)+1)),lt_min (by norm_num) (div_pos hε (by positivity)),?_⟩
  intro r hr
  have hr1 := hr.trans_le (min_le_left _ _)
  have hθdist : dist r.1 q.1 ≤ dist r q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hrA : ‖r.1‖ ≤ A := by
    have hnorm := norm_le_norm_add_norm_sub q.1 r.1
    rw [← dist_eq_norm,dist_comm q.1 r.1] at hnorm
    change ‖r.1‖ ≤ ‖q.1‖+1
    linarith
  rw [he A r.1 hrA r.2,he A q.1 hqA q.2]
  have hd : dist ((⟨r.1,hrA⟩,r.2) : BoundedParameter (Θ := Θ) A × State N)
      ((⟨q.1,hqA⟩,q.2) : BoundedParameter (Θ := Θ) A × State N) = dist r q := by
    simp only [Prod.dist_eq,Subtype.dist_eq]
  calc
    _ ≤ (K : ℝ)*dist r q := by simpa only [hd] using hK.dist_le_mul (⟨r.1,hrA⟩,r.2) (⟨q.1,hqA⟩,q.2)
    _ ≤ ((K : ℝ)+1)*dist r q := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by
      have hm := (lt_div_iff₀ (by positivity : (0 : ℝ)<(K : ℝ)+1)).mp (hr.trans_le (min_le_right _ _))
      simpa only [mul_comm] using hm

include hstate hparam in
omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem globalClass_continuous (T : ℝ≥0) : Continuous (globalClass D b hfixed hs T) :=
  continuous_of_bounded_lipschitz _ (fun A => boundedClass D b hstate hs A T)
    (fun A => boundedClass_lipschitz D b hstate hparam hs A T)
    (fun A θ hθ x => globalClass_eq_bounded D b hfixed hstate hs A T θ hθ x)

def boundedDriftClass (A T : ℝ≥0) (i : Fin N)
    (q : BoundedParameter (Θ := Θ) A × State N) : PredictableProcessL2 F P :=
  predictableCoefficient (boundedDrift_lipschitz b hstate A q.1 i)
    (boundedClass D b hstate hs A T q) T

include hparam in
omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem boundedDriftClass_lipschitz (A T : ℝ≥0) (i : Fin N) :
    ∃ K : ℝ≥0, LipschitzWith K (boundedDriftClass D b hstate hs A T i) := by
  obtain ⟨K,hK⟩ := boundedClass_lipschitz D b hstate hparam hs A T
  obtain ⟨C,hC⟩ := hparam
  let L : ℝ≥0 := driftBound b hstate A*K+C*initialScale (P := P) T
  refine ⟨L,LipschitzWith.of_dist_le_mul (fun q r => ?_)⟩
  let U := boundedClass D b hstate hs A T q
  let V := boundedClass D b hstate hs A T r
  let middle := predictableCoefficient (boundedDrift_lipschitz b hstate A q.1 i) V T
  have hfirst : dist (boundedDriftClass D b hstate hs A T i q) middle ≤
      (driftBound b hstate A : ℝ)*(K : ℝ)*dist q r := by
    simp only [dist_eq_norm]
    exact (norm_predictableCoefficient_sub_le (boundedDrift_lipschitz b hstate A q.1 i) U V T).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hK.dist_le_mul q r)
        (driftBound b hstate A).coe_nonneg) |>.trans_eq (by ring)
  have hsecond : dist middle (boundedDriftClass D b hstate hs A T i r) ≤
      (C : ℝ)*(initialScale (P := P) T : ℝ)*dist q r := by
    have hh := coefficient_family_sub_norm_bound
      (boundedDrift_lipschitz b hstate A q.1 i) (boundedDrift_lipschitz b hstate A r.1 i)
      V T ((C : ℝ)*‖q.1.1-r.1.1‖) (mul_nonneg C.coe_nonneg (norm_nonneg _))
      (fun x => hC q.1.1 r.1.1 i x)
    have hdist : ‖q.1.1-r.1.1‖ ≤ dist q r := by
      simpa only [Subtype.dist_eq,dist_eq_norm] using
        (show dist q.1 r.1 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_left _ _)
    change dist middle _ ≤ _
    rw [dist_eq_norm]
    calc
      _ ≤ (C : ℝ)*‖q.1.1-r.1.1‖*(initialScale (P := P) T : ℝ) := hh
      _ ≤ (C : ℝ)*dist q r*(initialScale (P := P) T : ℝ) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ dist (boundedDriftClass D b hstate hs A T i q) middle+
        dist middle (boundedDriftClass D b hstate hs A T i r) := dist_triangle _ _ _
    _ ≤ (driftBound b hstate A : ℝ)*K*dist q r+
        (C : ℝ)*(initialScale (P := P) T : ℝ)*dist q r := add_le_add hfirst hsecond
    _ = (L : ℝ)*dist q r := by dsimp [L]; ring

def driftClass (T : ℝ≥0) (i : Fin N) (q : Θ × State N) : PredictableProcessL2 F P :=
  predictableCoefficient ((hfixed q.1).choose_spec i) (globalClass D b hfixed hs T q) T

omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem driftClass_eq_bounded (A T : ℝ≥0) (i : Fin N) (θ : Θ) (hθ : ‖θ‖ ≤ A) (x : State N) :
    driftClass D b hfixed hs T i (θ,x) = boundedDriftClass D b hstate hs A T i (⟨θ,hθ⟩,x) := by
  unfold driftClass boundedDriftClass
  rw [globalClass_eq_bounded D b hfixed hstate hs A T θ hθ x]
  exact predictableCoefficient_bound_independent _ _ _ _

include hstate hparam in
omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem driftClass_continuous (T : ℝ≥0) (i : Fin N) : Continuous (driftClass D b hfixed hs T i) :=
  continuous_of_bounded_lipschitz _ (fun A => boundedDriftClass D b hstate hs A T i)
    (fun A => boundedDriftClass_lipschitz D b hstate hparam hs A T i)
    (fun A θ hθ x => driftClass_eq_bounded D b hfixed hstate hs A T i θ hθ x)

def noiseClass (T : ℝ≥0) (i j : Fin N) (q : Θ × State N) : PredictableProcessL2 F P :=
  predictableCoefficient (hs i j) (globalClass D b hfixed hs T q) T

include hstate hparam in
omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem noiseClass_continuous (T : ℝ≥0) (i j : Fin N) : Continuous (noiseClass D b hfixed hs T i j) := by
  have hc : LipschitzWith Ks
      (fun U : PredictableStateL2 N F P => predictableCoefficient (hs i j) U T) := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simpa only [dist_eq_norm] using norm_predictableCoefficient_sub_le (hs i j) U V T
  exact hc.continuous.comp (globalClass_continuous D b hfixed hstate hparam hs T)

def stateClass (T t : ℝ≥0) (q : Θ × State N) : lpMeas (State N) ℝ (F t) 2 P :=
  FixedCoefficients.stateClass D (hfixed q.1).choose_spec hs T t q.2

include hstate hparam in
omit [SecondCountableTopology Θ] [MeasurableSpace Θ] [BorelSpace Θ] in
theorem stateClass_continuous (T t : ℝ≥0) : Continuous (stateClass D b hfixed hs T t) := by
  change Continuous (fun q : Θ × State N => ∑ i : Fin N, scalarToStateTerminal t i
    (initialTerminal t (q.2 i) + driftTerminalAdapted T t (driftClass D b hfixed hs T i q) +
      ∑ j : Fin N, naturalItoProcessLpMeas (D.filtered j).toIsPreBrownianReal
        (D.coordinateStronglyMeasurable j) (D.filtered j) (noiseClass D b hfixed hs T i j q) t))
  apply continuous_finsetSum Finset.univ
  intro i _
  apply (scalarToStateTerminal_continuous t i).comp
  apply Continuous.add
  · apply Continuous.add
    · apply (initialTerminal_lipschitz t).continuous.comp
      fun_prop
    · exact (driftTerminalAdapted_lipschitz T t).continuous.comp
        (driftClass_continuous D b hfixed hstate hparam hs T i)
  · exact continuous_finsetSum Finset.univ (fun j _ =>
      (itoTerminalAdapted_lipschitz D j t).continuous.comp
        (noiseClass_continuous D b hfixed hstate hparam hs T i j))

include hstate hparam in
theorem exists_joint_terminal_representative (T t : ℝ≥0) :
    ∃ G : (Θ × State N) × Ω → State N, StronglyMeasurable G ∧ ∀ q,
      (fun ω => G (q,ω)) =ᵐ[P]
        GlobalSDE.horizonProcess D (hfixed q.1).choose_spec hs q.2 T t := by
  obtain ⟨G,hG,hGa⟩ := JointLpRepresentative.exists_joint_representative
    (fun q => (stateClass D b hfixed hs T t q : Lp (State N) 2 P))
    ((continuous_subtype_val.comp (stateClass_continuous D b hfixed hstate hparam hs T t)).stronglyMeasurable)
  exact ⟨G,hG,fun q => (hGa q).trans (FixedCoefficients.stateClass_ae D (hfixed q.1).choose_spec hs T t q.2)⟩

def terminalRepresentative (T t : ℝ≥0) : (Θ × State N) × Ω → State N :=
  (exists_joint_terminal_representative D b hfixed hstate hparam hs T t).choose

theorem terminalRepresentative_measurable (T t : ℝ≥0) :
    Measurable (terminalRepresentative D b hfixed hstate hparam hs T t) :=
  (exists_joint_terminal_representative D b hfixed hstate hparam hs T t).choose_spec.1.measurable

def terminalKernel (T t : ℝ≥0) : Kernel (Θ × State N) (State N) :=
  (Kernel.id ×ₖ Kernel.const (Θ × State N) P).map
    (terminalRepresentative D b hfixed hstate hparam hs T t)

theorem terminalKernel_apply (T t : ℝ≥0) (q : Θ × State N) :
    terminalKernel D b hfixed hstate hparam hs T t q =
      P.map (GlobalSDE.horizonProcess D (hfixed q.1).choose_spec hs q.2 T t) := by
  rw [terminalKernel, Kernel.map_apply _ (terminalRepresentative_measurable D b hfixed hstate hparam hs T t),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (terminalRepresentative_measurable D b hfixed hstate hparam hs T t) measurable_prodMk_left]
  exact Measure.map_congr ((exists_joint_terminal_representative D b hfixed hstate hparam hs T t).choose_spec.2 q)

include hstate hparam in
theorem exists_joint_global_process :
    ∃ Y : (Θ × State N) → ℝ≥0 → Ω → State N,
      StronglyMeasurable (fun q : (Θ × State N) × (ℝ≥0 × Ω) => Y q.1 q.2.1 q.2.2) ∧
      ∀ q, ∀ᵐ ω ∂P, ∀ t, Y q t ω = GlobalSDE.process D (hfixed q.1).choose_spec hs q.2 t ω := by
  obtain ⟨Y,hY,_,hYa⟩ := JointAdaptedContinuous.exists_jointAdapted_continuous_version
    (fun t => stateClass D b hfixed hs (GlobalSDE.integerHorizon (Nat.ceil t)) t)
    (fun t => (stateClass_continuous D b hfixed hstate hparam hs _ t).stronglyMeasurable)
    (fun q => GlobalSDE.process D (hfixed q.1).choose_spec hs q.2)
    (fun q => GlobalSDE.process_continuous D (hfixed q.1).choose_spec hs q.2)
    (fun q t => FixedCoefficients.stateClass_ae D (hfixed q.1).choose_spec hs _ t q.2)
  exact ⟨Y,hY,fun q => (hYa q).mono (fun _ h => h.1)⟩

def globalRepresentative : (Θ × State N) → ℝ≥0 → Ω → State N :=
  (exists_joint_global_process D b hfixed hstate hparam hs).choose

theorem globalRepresentative_measurable :
    Measurable (fun z : ((Θ × State N) × ℝ≥0) × Ω =>
      globalRepresentative D b hfixed hstate hparam hs z.1.1 z.1.2 z.2) :=
  (exists_joint_global_process D b hfixed hstate hparam hs).choose_spec.1.measurable.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

def globalKernel : Kernel ((Θ × State N) × ℝ≥0) (State N) :=
  (Kernel.id ×ₖ Kernel.const ((Θ × State N) × ℝ≥0) P).map
    (fun z => globalRepresentative D b hfixed hstate hparam hs z.1.1 z.1.2 z.2)

instance globalKernel_markov : IsMarkovKernel (globalKernel D b hfixed hstate hparam hs) :=
  Kernel.IsMarkovKernel.map _ (globalRepresentative_measurable D b hfixed hstate hparam hs)

theorem globalKernel_apply (q : (Θ × State N) × ℝ≥0) :
    globalKernel D b hfixed hstate hparam hs q =
      P.map (GlobalSDE.process D (hfixed q.1.1).choose_spec hs q.1.2 q.2) := by
  rw [globalKernel, Kernel.map_apply _ (globalRepresentative_measurable D b hfixed hstate hparam hs),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (globalRepresentative_measurable D b hfixed hstate hparam hs) measurable_prodMk_left]
  exact Measure.map_congr
    (((exists_joint_global_process D b hfixed hstate hparam hs).choose_spec.2 q.1).mono (fun _ h => h q.2))

end SlowEquilibration.SphericalDynamics.ParameterFamily

namespace SlowEquilibration.SphericalDynamics
open SphericalAging HardSphereDynamics SphericalModel

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] mixedTransitionKernel

variable {N : ℕ}

/-- The actual mixed diffusion law is a single joint kernel in disorder,
initial state, and time. Its measurable version is constructed from the
actual Picard classes, and every parameter slice retains the literal law. -/
@[irreducible] def disorderTimeTransitionKernel (μ : FiniteMixture) (β : ℝ) :
    Kernel ((Disorder N μ.maxDegree × State N) × ℝ≥0) (State N) :=
  ParameterFamily.globalKernel (NullAugmentation.driver (VectorBrownian.driver N))
    (fun J => cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N))
    (fun J => cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N))
    (fun A => mixed_cutoffDrift_uniform_state_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N) A)
    (mixed_cutoffDrift_disorder_lipschitz μ β (cutoffRadius N) (cutoffRadius_pos N))
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec

instance disorderTimeTransitionKernel_markov (μ : FiniteMixture) (β : ℝ) :
    IsMarkovKernel (disorderTimeTransitionKernel (N := N) μ β) := by
  unfold disorderTimeTransitionKernel
  exact ParameterFamily.globalKernel_markov _ _ _ _ _ _

/-- The joint kernel equals the original fixed-disorder Brownian transition,
for every disorder, initial state, and nonnegative time. -/
theorem disorderTimeTransitionKernel_apply (μ : FiniteMixture) (β : ℝ)
    (q : (Disorder N μ.maxDegree × State N) × ℝ≥0) :
    disorderTimeTransitionKernel μ β q = mixedTransitionKernel μ q.1.1 β q.2 q.1.2 := by
  rw [disorderTimeTransitionKernel, ParameterFamily.globalKernel_apply, mixedTransitionKernel_apply]
  rfl

/-- The actual disorder-and-initial-state transition kernel at fixed time. -/
def disorderTransitionKernel (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    Kernel (Disorder N μ.maxDegree × State N) (State N) :=
  (disorderTimeTransitionKernel μ β).comap (fun q => (q,t))
    (measurable_id.prodMk measurable_const)

instance disorderTransitionKernel_markov (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    IsMarkovKernel (disorderTransitionKernel (N := N) μ β t) := by
  unfold disorderTransitionKernel
  infer_instance

theorem disorderTransitionKernel_apply (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (q : Disorder N μ.maxDegree × State N) :
    disorderTransitionKernel μ β t q = mixedTransitionKernel μ q.1 β t q.2 :=
  disorderTimeTransitionKernel_apply μ β (q,t)

/-- Genuine joint Borel measurability of the actual transition measure. -/
theorem mixedTransitionKernel_joint_time_measurable (μ : FiniteMixture) (β : ℝ) :
    Measurable (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      mixedTransitionKernel μ q.1.1 β q.2 q.1.2) := by
  have he : (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      mixedTransitionKernel μ q.1.1 β q.2 q.1.2) =
      (fun q => disorderTimeTransitionKernel μ β q) :=
    funext (fun q => (disorderTimeTransitionKernel_apply μ β q).symm)
  rw [he]
  exact (disorderTimeTransitionKernel μ β).measurable

/-- At fixed time the actual law is jointly measurable in disorder and state. -/
theorem mixedTransitionKernel_joint_measurable (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    Measurable (fun q : Disorder N μ.maxDegree × State N =>
      mixedTransitionKernel μ q.1 β t q.2) :=
  (mixedTransitionKernel_joint_time_measurable μ β).comp
    (measurable_id.prodMk measurable_const)

/-- Evaluation on any Borel event is jointly measurable in all parameters. -/
theorem mixedTransitionKernel_joint_time_eval_measurable (μ : FiniteMixture) (β : ℝ)
    {A : Set (State N)} (hA : MeasurableSet A) :
    Measurable (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      mixedTransitionKernel μ q.1.1 β q.2 q.1.2 A) :=
  (Measure.measurable_coe hA).comp (mixedTransitionKernel_joint_time_measurable μ β)

theorem mixedTransitionKernel_joint_eval_measurable (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    {A : Set (State N)} (hA : MeasurableSet A) :
    Measurable (fun q : Disorder N μ.maxDegree × State N =>
      mixedTransitionKernel μ q.1 β t q.2 A) :=
  (Measure.measurable_coe hA).comp (mixedTransitionKernel_joint_measurable μ β t)

/-- Parameter-dependent actual diffusion expectations are measurable.
The integrand may depend jointly on disorder, state, time, and endpoint. -/
theorem mixedTransitionKernel_joint_integral_measurable (μ : FiniteMixture) (β : ℝ)
    (f : ((Disorder N μ.maxDegree × State N) × ℝ≥0) × State N → ℝ)
    (hf : Measurable f) :
    Measurable (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      ∫ y, f (q,y) ∂mixedTransitionKernel μ q.1.1 β q.2 q.1.2) := by
  have hm := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := disorderTimeTransitionKernel μ β)
  have he : (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      ∫ y, f (q,y) ∂mixedTransitionKernel μ q.1.1 β q.2 q.1.2) =
      (fun q => ∫ y, f (q,y) ∂disorderTimeTransitionKernel μ β q) := by
    funext q
    exact congrArg (fun ν : Measure (State N) => ∫ y, f (q,y) ∂ν)
      (disorderTimeTransitionKernel_apply μ β q).symm
  rw [he]
  exact hm.measurable

/-- Nonnegative endpoint integrals are jointly measurable, including
parameter-dependent indicators used for disorder probability events. -/
theorem mixedTransitionKernel_joint_lintegral_measurable (μ : FiniteMixture) (β : ℝ)
    (f : ((Disorder N μ.maxDegree × State N) × ℝ≥0) × State N → ℝ≥0∞)
    (hf : Measurable f) :
    Measurable (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      ∫⁻ y, f (q,y) ∂mixedTransitionKernel μ q.1.1 β q.2 q.1.2) := by
  have hm := hf.lintegral_kernel_prod_right' (κ := disorderTimeTransitionKernel μ β)
  have he : (fun q : (Disorder N μ.maxDegree × State N) × ℝ≥0 =>
      ∫⁻ y, f (q,y) ∂mixedTransitionKernel μ q.1.1 β q.2 q.1.2) =
      (fun q => ∫⁻ y, f (q,y) ∂disorderTimeTransitionKernel μ β q) := by
    funext q
    exact congrArg (fun ν : Measure (State N) => ∫⁻ y, f (q,y) ∂ν)
      (disorderTimeTransitionKernel_apply μ β q).symm
  rw [he]
  exact hm

end SlowEquilibration.SphericalDynamics
