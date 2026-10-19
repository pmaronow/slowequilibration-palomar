module

public import SphericalAging.HamiltonianCoefficientDependence
public import SphericalAging.PredictableTerminalOperators
public import SphericalAging.JointAdaptedContinuous

public section

/-! Joint adapted continuous paths for the actual cutoff Hamiltonian SDE.
Parameter measurability is proved from the constructed Picard classes and
actual terminal integration operators, then the past-grid construction
preserves every deterministic parameter's genuine solution on a common
all-time almost-everywhere event.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianJointProcess
open HardSphereDynamics LocalSDE HamiltonianPicardDependence GlobalHamiltonianParameter
open HamiltonianCoefficientDependence PredictableTerminalOperators JointAdaptedContinuous
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The actual canonical finite-horizon cutoff Hamiltonian solution. -/
@[expose] def process (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) : ℝ≥0 → Ω → State N :=
  GlobalSDE.horizonProcess D
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
    (noise_family_lipschitz N R hR) q.2 T

lemma process_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) :
    ∀ᵐ ω ∂P, Continuous (fun t => process D β R hR T q t ω) :=
  GlobalSDE.horizonProcess_continuous D _ _ q.2 T

/-- Genuine scalar terminal class assembled from the actual coefficient
classes and integration operators. -/
@[expose] def scalarClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T t : ℝ≥0)
    (i : Fin N) (q : FiniteModel.Disorder N p × State N) : lpMeas ℝ ℝ (F t) 2 P :=
  initialTerminal t (q.2 i)+driftTerminalAdapted T t (driftClass D β R hR T i q)+
    ∑ j : Fin N, naturalItoProcessLpMeas (D.filtered j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) (noiseClass D β R hR T i j q) t

lemma scalarClass_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (T t : ℝ≥0) (i : Fin N) : Continuous (scalarClass (p := p) D β R hR T t i) := by
  apply Continuous.add
  · apply Continuous.add
    · apply (initialTerminal_lipschitz t).continuous.comp
      fun_prop
    · exact (driftTerminalAdapted_lipschitz T t).continuous.comp (driftClass_continuous D β R hR T i)
  · exact continuous_finsetSum Finset.univ (fun j _ =>
      (itoTerminalAdapted_lipschitz D j t).continuous.comp (noiseClass_continuous D β R hR T i j))

/-- The actual finite-dimensional terminal state class in L²(F_t). -/
@[expose] def stateClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T t : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) : lpMeas (State N) ℝ (F t) 2 P :=
  ∑ i : Fin N, scalarToStateTerminal t i (scalarClass D β R hR T t i q)

lemma stateClass_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T t : ℝ≥0) :
    Continuous (stateClass (p := p) D β R hR T t) :=
  continuous_finsetSum Finset.univ (fun i _ =>
    (scalarToStateTerminal_continuous t i).comp (scalarClass_continuous D β R hR T t i))

lemma scalarClass_ae (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T t : ℝ≥0)
    (i : Fin N) (q : FiniteModel.Disorder N p × State N) :
    (scalarClass D β R hR T t i q : Lp ℝ 2 P) =ᵐ[P]
      coordinateVersion D
        (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
        (noise_family_lipschitz N R hR) q.2 T (globalClass D β R hR T q) i t := by
  let A := initialTerminal (F := F) (P := P) t (q.2 i)
  let B := driftTerminalAdapted (F := F) (P := P) T t (driftClass D β R hR T i q)
  let C := fun j : Fin N => naturalItoProcessLpMeas (D.filtered j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j) (noiseClass D β R hR T i j q) t
  have hsum : ((∑ j, C j : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P) =ᵐ[P]
      (fun ω => ∑ j, (C j : RandomL2 P) ω) := by
    simpa only [Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ (fun j => (C j : RandomL2 P))
  have hi : ∀ᵐ ω ∂P, ∀ j : Fin N, (C j : RandomL2 P) ω=
      SphericalAging.PredictableItoTime.itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (noiseClass D β R hR T i j q) t ω :=
    ae_all_iff.mpr (fun j => SphericalAging.PredictableItoTime.itoVersion_ae_eq
      (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t)
  filter_upwards [Lp.coeFn_add ((A+B : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P)
      ((∑ j, C j : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P),
    Lp.coeFn_add (A : RandomL2 P) (B : RandomL2 P),
    Lp.coeFn_const 2 P (q.2 i),
    (SphericalAging.PredictableDriftTime.driftVersion_memLp (driftClass D β R hR T i q) T t).coeFn_toLp,
    hsum,hi] with ω hadd hab ha hb hc hnoise
  change (((A+B+(∑ j, C j) : lpMeas ℝ ℝ (F t) 2 P)) : RandomL2 P) ω = _
  simp only [Submodule.coe_add] at hadd hab ⊢
  rw [hadd,Pi.add_apply,hab,Pi.add_apply]
  change ((Lp.const 2 P) (q.2 i) : Ω → ℝ) ω+
    (((SphericalAging.PredictableDriftTime.driftVersion_memLp (driftClass D β R hR T i q) T t).toLp _) : Ω → ℝ) ω+
      ((∑ j, C j : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P) ω = _
  rw [ha,hb,hc]
  simp only [hnoise]
  rfl

lemma stateClass_ae (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T t : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) :
    (stateClass D β R hR T t q : Lp (State N) 2 P) =ᵐ[P] process D β R hR T q t := by
  have hs : (stateClass D β R hR T t q : Lp (State N) 2 P) =ᵐ[P]
      (fun ω => ∑ i, (scalarToStateTerminal t i (scalarClass D β R hR T t i q) : Lp (State N) 2 P) ω) := by
    simpa only [stateClass,Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (scalarToStateTerminal t i (scalarClass D β R hR T t i q) : Lp (State N) 2 P))
  have hi : ∀ᵐ ω ∂P, ∀ i : Fin N,
      (scalarToStateTerminal t i (scalarClass D β R hR T t i q) : Lp (State N) 2 P) ω =
        (scalarClass D β R hR T t i q : Lp ℝ 2 P) ω • basisVector i :=
    ae_all_iff.mpr (fun i => (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp _)
  have hsc := ae_all_iff.mpr (fun i => scalarClass_ae D β R hR T t i q)
  filter_upwards [hs,hi,hsc] with ω hs hi hsc
  rw [hs]
  simp only [hi,hsc]
  rfl

/-- Actual joint solution paths on the full disorder × initial-state space.
Every deterministic slice agrees at all times with the genuine Picard SDE
solution; adaptation uses the actual full driving filtration. -/
theorem exists_joint_adapted_process (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0) :
    ∃ Y : (FiniteModel.Disorder N p × State N) → ℝ≥0 → Ω → State N,
      StronglyMeasurable (fun q : (FiniteModel.Disorder N p × State N) × (ℝ≥0 × Ω) => Y q.1 q.2.1 q.2.2) ∧
      (∀ t, StronglyMeasurable[(inferInstance : MeasurableSpace (FiniteModel.Disorder N p × State N)).prod (F t)]
        (fun q : (FiniteModel.Disorder N p × State N) × Ω => Y q.1 t q.2)) ∧
      ∀ q, ∀ᵐ ω ∂P, (∀ t, Y q t ω=process D β R hR T q t ω) ∧ Continuous (fun t => Y q t ω) :=
  exists_jointAdapted_continuous_version (fun t => stateClass D β R hR T t)
    (fun t => (stateClass_continuous D β R hR T t).stronglyMeasurable)
    (process D β R hR T) (process_continuous D β R hR T) (fun q t => stateClass_ae D β R hR T t q)

/-- The actual all-time cutoff Hamiltonian solution for each parameter. -/
@[expose] def globalProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (q : FiniteModel.Disorder N p × State N) : ℝ≥0 → Ω → State N :=
  GlobalSDE.process D
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) (⟨q.1,by simp⟩))
    (noise_family_lipschitz N R hR) q.2

lemma globalProcess_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (q : FiniteModel.Disorder N p × State N) :
    ∀ᵐ ω ∂P, Continuous (fun t => globalProcess D β R hR q t ω) :=
  GlobalSDE.process_continuous D _ _ q.2

/-- A genuine jointly adapted all-time solution family for unrestricted
finite disorder and initial state, identified with the actual SDE process
at every time on each deterministic parameter slice. -/
theorem exists_joint_adapted_global_process (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) :
    ∃ Y : (FiniteModel.Disorder N p × State N) → ℝ≥0 → Ω → State N,
      StronglyMeasurable (fun q : (FiniteModel.Disorder N p × State N) × (ℝ≥0 × Ω) => Y q.1 q.2.1 q.2.2) ∧
      (∀ t, StronglyMeasurable[(inferInstance : MeasurableSpace (FiniteModel.Disorder N p × State N)).prod (F t)]
        (fun q : (FiniteModel.Disorder N p × State N) × Ω => Y q.1 t q.2)) ∧
      ∀ q, ∀ᵐ ω ∂P, (∀ t, Y q t ω=globalProcess D β R hR q t ω) ∧ Continuous (fun t => Y q t ω) := by
  apply exists_jointAdapted_continuous_version
    (fun t => stateClass D β R hR (GlobalSDE.integerHorizon (Nat.ceil t)) t)
    (fun t => (stateClass_continuous D β R hR _ t).stronglyMeasurable)
    (globalProcess D β R hR) (globalProcess_continuous D β R hR)
  intro q t
  exact stateClass_ae D β R hR _ t q

end SphericalAging.HamiltonianJointProcess
