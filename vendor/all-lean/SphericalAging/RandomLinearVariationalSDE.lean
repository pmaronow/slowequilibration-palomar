module

public import SphericalAging.RandomInitialSDE
public import SphericalAging.LinearStrongUniqueness
public import SphericalAging.TerminalStateRepresentation

public section

/-! Genuine bounded predictable matrix SDEs with square-integrable random
initial data known at time zero. The predictable source and continuous
solution are constructed, and the equation uses actual full-filtration
Itô operators. This is the random-initial input for two-time response. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.RandomLinearVariationalSDE
open HardSphereDynamics LocalSDE PredictableDriftTime PredictableItoTime
open PredictableLinearCoefficient LinearVariationalSDE TerminalStateRepresentation
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

@[expose] def IsStrongSolutionOn
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (D : BrownianDriver N P F) (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyAdapted F X ∧ (∀ᵐ omega ∂P, Continuous (fun t => X t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
    (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (a i).value (s,omega) (X s omega)) T) ∧
    (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma i j).value (s,omega) (X s omega)) T) ∧
    ∀ t, t ≤ T → ∀ i, ∀ᵐ omega ∂P, X t omega i = Z0 omega i +
      (∫ s in (0 : ℝ)..(t : ℝ), (a i).value (s.toNNReal,omega) (X s.toNNReal omega)) +
      (driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) : Ω → ℝ) omega

@[expose] def version (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (T : ℝ≥0) (Q : PredictableStateL2 N F P)
    (t : ℝ≥0) (omega : Ω) : State N :=
  Z0 omega + LinearVariationalSDE.version D a sigma 0 T Q t omega

lemma version_stronglyAdapted (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (T : ℝ≥0) (Q : PredictableStateL2 N F P) :
    StronglyAdapted F (version D a sigma Z0 T Q) := fun t =>
  (hZ0.mono (F.mono bot_le)).add (LinearVariationalSDE.version_stronglyAdapted D a sigma 0 T Q t)

lemma version_continuous (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (T : ℝ≥0) (Q : PredictableStateL2 N F P) :
    ∀ᵐ omega ∂P, Continuous (fun t => version D a sigma Z0 T Q t omega) :=
  (LinearVariationalSDE.version_ae_continuous D a sigma 0 T Q).mono
    (fun _ h => continuous_const.add h)

lemma version_apply (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (T : ℝ≥0) (Q : PredictableStateL2 N F P)
    (t : ℝ≥0) (omega : Ω) (i : Fin N) :
    version D a sigma Z0 T Q t omega i = Z0 omega i + driftVersion (apply (a i) Q) T t omega +
      ∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (apply (sigma i j) Q) t omega := by
  simp only [version,PiLp.add_apply,LinearVariationalSDE.version_apply,
    LinearVariationalSDE.coordinateVersion,PiLp.zero_apply,zero_add]
  ring

lemma version_timeCut (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P)
    (hQ : Q = RandomInitialSDE.initialClass Z0 hZ0 hmem T + finiteDriftPicardMap a T Q + finiteNoisePicardMap D sigma T Q) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => version D a sigma Z0 T Q q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hadd := Lp.coeFn_add
    ((RandomInitialSDE.initialClass Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
      (finiteDriftPicardMap a T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (finiteNoisePicardMap D sigma T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  have hadd' := Lp.coeFn_add
    (RandomInitialSDE.initialClass Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (finiteDriftPicardMap a T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  filter_upwards [hadd,hadd',RandomInitialSDE.initialClass_coeFn Z0 hZ0 hmem T,
    finiteDriftPicardMap_coeFn a T Q,finiteNoisePicardMap_coeFn D sigma T Q] with q hsum hsum' h0 ha hs
  conv_rhs => rw [hQ]
  change _ = (((RandomInitialSDE.initialClass Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
    (finiteDriftPicardMap a T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) +
    (finiteNoisePicardMap D sigma T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) q
  rw [hsum,Pi.add_apply,hsum',Pi.add_apply,h0,ha,hs]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),
      ht,ite_eq_left,version,LinearVariationalSDE.version,LinearVariationalSDE.coordinateVersion,
      PiLp.zero_apply,zero_add,add_smul,Finset.sum_add_distrib]
    abel
  · simp [ht]

lemma strongSolution_of_fixedPoint (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P)
    (hQ : Q = RandomInitialSDE.initialClass Z0 hZ0 hmem T + finiteDriftPicardMap a T Q + finiteNoisePicardMap D sigma T Q) :
    IsStrongSolutionOn a sigma D Z0 (version D a sigma Z0 T Q) T := by
  have hcut := version_timeCut D a sigma Z0 hZ0 hmem T Q hQ
  refine ⟨version_stronglyAdapted D a sigma Z0 hZ0 T Q,version_continuous D a sigma Z0 T Q,
    (fun i => apply (a i) Q),(fun i j => apply (sigma i j) Q),
    (fun i => apply_eq_actual hcut (a i)),(fun i j => apply_eq_actual hcut (sigma i j)),?_⟩
  intro t ht i
  filter_upwards [driftVersion_eq_actual hcut (a i),driverIto_ae_eq_versions D (fun j => apply (sigma i j) Q) t]
    with omega hd hn
  rw [version_apply,hn]
  simp only [hd t ht]

@[expose] def responseClass (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    PredictableStateL2 N F P := sourceClass D a sigma T (RandomInitialSDE.initialClass Z0 hZ0 hmem T)

@[expose] def process (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) : ℝ≥0 → Ω → State N :=
  version D a sigma Z0 T (responseClass D a sigma Z0 hZ0 hmem T)

lemma process_timeCut (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => process D a sigma Z0 hZ0 hmem T q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (responseClass D a sigma Z0 hZ0 hmem T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  version_timeCut D a sigma Z0 hZ0 hmem T _ (sourceClass_fixedPoint D a sigma T _)

lemma process_strongSolution (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    IsStrongSolutionOn a sigma D Z0 (process D a sigma Z0 hZ0 hmem T) T :=
  strongSolution_of_fixedPoint D a sigma Z0 hZ0 hmem T _ (sourceClass_fixedPoint D a sigma T _)

lemma exists_strongSolution_on (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    ∃ X,IsStrongSolutionOn a sigma D Z0 X T :=
  ⟨_,process_strongSolution D a sigma Z0 hZ0 hmem T⟩


@[expose] def terminalClass (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T t : ℝ≥0) : Lp (State N) 2 P :=
  hmem.toLp Z0 + TerminalStateRepresentation.terminalClass D 0
    (fun i => apply (a i) (responseClass D a sigma Z0 hZ0 hmem T))
    (fun i j => apply (sigma i j) (responseClass D a sigma Z0 hZ0 hmem T)) T t

lemma terminalClass_ae (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T t : ℝ≥0) : terminalClass D a sigma Z0 hZ0 hmem T t =ᵐ[P]
      process D a sigma Z0 hZ0 hmem T t := by
  filter_upwards [hmem.coeFn_toLp,
    linear_terminalClass_ae D a sigma 0 T t (responseClass D a sigma Z0 hZ0 hmem T),
    Lp.coeFn_add (hmem.toLp Z0) (TerminalStateRepresentation.terminalClass D 0
      (fun i => apply (a i) (responseClass D a sigma Z0 hZ0 hmem T))
      (fun i j => apply (sigma i j) (responseClass D a sigma Z0 hZ0 hmem T)) T t)]
      with omega h0 hY hadd
  change ((hmem.toLp Z0+TerminalStateRepresentation.terminalClass D 0
    (fun i => apply (a i) (responseClass D a sigma Z0 hZ0 hmem T))
    (fun i j => apply (sigma i j) (responseClass D a sigma Z0 hZ0 hmem T)) T t : Lp (State N) 2 P) :
      Ω → State N) omega = _
  rw [hadd,Pi.add_apply,h0,hY]
  rfl

lemma process_memLp (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (T t : ℝ≥0) : MemLp (process D a sigma Z0 hZ0 hmem T t) 2 P :=
  (Lp.memLp (terminalClass D a sigma Z0 hZ0 hmem T t)).ae_eq
    (terminalClass_ae D a sigma Z0 hZ0 hmem T t)

lemma strongSolution_class_equation
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D Z0 X T) :
    ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (a i).value (s,omega) (X s omega)) T) ∧
      (∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma i j).value (s,omega) (X s omega)) T) ∧
      ∀ t,t ≤ T → ∀ i,∀ᵐ omega ∂P,
        X t omega i=Z0 omega i+driftVersion (A i) T t omega+VectorIto.vectorProcess D (U i) t omega := by
  obtain ⟨_,_,A,U,hA,hU,heq⟩ := h
  refine ⟨A,U,hA,hU,?_⟩
  intro t ht i
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (a i).value (s,omega) (X s omega)) T (A i) (hA i)
  have hn := VectorIto.vectorProcessLp_ae_eq D (U i) t
  have hh := heq t ht i
  have hnoise : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) =
      VectorIto.vectorProcessLp D (U i) t := CutoffSphere.driverItoMap_eq_vectorIto D _
  rw [hnoise] at hh
  filter_upwards [hh,hd,hn] with omega h hd hn
  rw [← hd t ht,hn] at h
  exact h

lemma difference_strongSolution
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : IsStrongSolutionOn a sigma D Z0 X T)
    (hY : IsStrongSolutionOn a sigma D Z0 Y T) :
    LinearVariationalSDE.IsStrongSolutionOn a sigma D 0 (fun t omega => X t omega-Y t omega) T := by
  obtain ⟨AX,UX,hAX,hUX,hXe⟩ := strongSolution_class_equation hX
  obtain ⟨AY,UY,hAY,hUY,hYe⟩ := strongSolution_class_equation hY
  let A := fun i => AX i-AY i
  let U := fun i j => UX i j-UY i j
  have hA : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (a i).value (s,omega) (X s omega-Y s omega)) T := by
    intro i
    filter_upwards [hAX i,hAY i,Lp.coeFn_sub (AX i : TimeProcessL2 P) (AY i)] with q hX hY hsub
    simp only [A,Submodule.coe_sub]
    rw [hsub,Pi.sub_apply,hX,hY]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T <;>
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,map_sub,sub_self]
  have hU : ∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (sigma i j).value (s,omega) (X s omega-Y s omega)) T := by
    intro i j
    filter_upwards [hUX i j,hUY i j,Lp.coeFn_sub (UX i j : TimeProcessL2 P) (UY i j)] with q hX hY hsub
    simp only [U,Submodule.coe_sub]
    rw [hsub,Pi.sub_apply,hX,hY]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T <;>
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,map_sub,sub_self]
  refine ⟨(fun t => (hX.1 t).sub (hY.1 t)),?_,A,U,hA,hU,?_⟩
  · filter_upwards [hX.2.1,hY.2.1] with omega hX hY
    exact hX.sub hY
  · intro t ht i
    have hn : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) =
        VectorIto.vectorProcessLp D (UX i) t-VectorIto.vectorProcessLp D (UY i) t := by
      rw [CutoffSphere.driverItoMap_eq_vectorIto]
      exact StaticSDEOperators.vectorProcessLp_sub D _ _ t
    have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
      (fun s omega => (a i).value (s,omega) (X s omega-Y s omega)) T (A i) (hA i)
    filter_upwards [hXe t ht i,hYe t ht i,driftVersion_sub_ae (AX i) (AY i) T,hd,
      VectorIto.vectorProcessLp_ae_eq D (UX i) t,VectorIto.vectorProcessLp_ae_eq D (UY i) t,
      Lp.coeFn_sub (VectorIto.vectorProcessLp D (UX i) t) (VectorIto.vectorProcessLp D (UY i) t)]
      with omega hX hY hsub hd hnX hnY hnsub
    change (X t omega-Y t omega) i = _
    simp only [PiLp.sub_apply,PiLp.zero_apply,zero_add]
    rw [← hd t ht,hsub t,hn,hnsub,Pi.sub_apply,hnX,hnY,hX,hY]
    ring

lemma pathwise_uniqueness
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : IsStrongSolutionOn a sigma D Z0 X T)
    (hY : IsStrongSolutionOn a sigma D Z0 Y T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → X t omega=Y t omega :=
  (LinearStrongUniqueness.linear_zero_of_strongSolution (difference_strongSolution hX hY) hnull).mono
    (fun _ h t ht => sub_eq_zero.mp (h t ht))

end SphericalAging.RandomLinearVariationalSDE
