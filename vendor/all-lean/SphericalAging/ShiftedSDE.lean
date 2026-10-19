module

public import SphericalAging.ShiftedItoProcess
public import SphericalAging.RandomInitialSDE
public import SphericalAging.CutoffSphere

public section

/-! Genuine restart of the original strong SDE at deterministic waiting
time. Both drift and Itô operators are identified with their translated
original operators; the restarted path is the original future path and
its initial state is the actual state at the waiting time. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedSDE
open HardSphereDynamics LocalSDE RandomInitialSDE VectorIto ShiftedPredictable TimeShiftMeasure ShiftedItoProcess
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The literal future part of the original state path. -/
@[expose] def stateShift (X : ℝ≥0 → Ω → State N) (s : ℝ≥0) (t : ℝ≥0) (omega : Ω) : State N := X (s+t) omega

lemma stateShift_adapted (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X) (s : ℝ≥0) :
    StronglyAdapted (ShiftedBrownian.filtration F s) (stateShift X s) := fun t => hXa (s+t)

lemma stateShift_continuous (X : ℝ≥0 → Ω → State N)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega)) (s : ℝ≥0) :
    ∀ᵐ omega ∂P,Continuous (fun t => stateShift X s t omega) :=
  hXc.mono (fun _ hc => hc.comp (continuous_const.add continuous_id))

lemma timeCut_shift_ae (H : ℝ≥0 → Ω → ℝ) (s T : ℝ≥0) :
    FourPapersCommon.continuousAdaptedTimeCut (fun t omega => H (s+t) omega) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => FourPapersCommon.continuousAdaptedTimeCut H (s+T) (shift s q)) := by
  have hpos : ∀ᵐ q : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P,0 < q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (ae_iff.mpr (by simp))
  filter_upwards [hpos] with q hpos
  have he : s+q.1 ∈ Ioc 0 (s+T) ↔ q.1 ∈ Ioc 0 T := by
    simp only [mem_Ioc]
    exact and_congr (iff_of_true ((zero_le : 0 ≤ s).trans_lt (lt_add_of_pos_right s hpos)) hpos)
      (add_le_add_iff_left s)
  simp only [FourPapersCommon.continuousAdaptedTimeCut,shift,he]

lemma timeCut_shift_memLp (H : ℝ≥0 → Ω → ℝ) (s T : ℝ≥0)
    (hm : MemLp (FourPapersCommon.continuousAdaptedTimeCut H (s+T)) 2 (nonnegativeLebesgueMeasure.prod P)) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun t omega => H (s+t) omega) T) 2
      (nonnegativeLebesgueMeasure.prod P) :=
  (((hm.mono_measure (map_shift_le s)).comp_of_map (shift_measurable s).aemeasurable).ae_eq
    (timeCut_shift_ae H s T).symm)

lemma coefficientPredictableActual_shift {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    {g : State N → ℝ} (hg : Continuous g) (s t : ℝ≥0)
    (hm : MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun r omega => g (X r omega)) (s+t))
      2 (nonnegativeLebesgueMeasure.prod P)) :
    coefficientPredictableActual (stateShift_adapted X hXa s) (stateShift_continuous X hXc s) hg t
      (timeCut_shift_memLp (fun r omega => g (X r omega)) s t hm)=
        predictableShift s (coefficientPredictableActual hXa hXc hg (s+t) hm) := by
  apply Subtype.ext
  apply Lp.ext
  have hU := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp hm.coeFn_toLp
  filter_upwards [(timeCut_shift_memLp (fun r omega => g (X r omega)) s t hm).coeFn_toLp,
    predictableShift_coe s (coefficientPredictableActual hXa hXc hg (s+t) hm),hU,
    timeCut_shift_ae (fun r omega => g (X r omega)) s t] with q hL hR hU hcut
  dsimp only [Function.comp_def] at hU
  change (coefficientPredictableActual hXa hXc hg (s+t) hm : ℝ≥0 × Ω → ℝ) (shift s q)=_ at hU
  exact hL.trans (hcut.trans (hU.symm.trans hR.symm))

lemma drift_shift (X : ℝ≥0 → Ω → State N) {g : State N → ℝ} (hg : Continuous g)
    (s t : ℝ≥0) (omega : Ω) :
    (∫ r in (s : ℝ)..((s+t : ℝ≥0) : ℝ),g (X r.toNNReal omega))=
      ∫ r in (0 : ℝ)..(t : ℝ),g (stateShift X s r.toNNReal omega) := by
  have he := intervalIntegral.integral_comp_add_left
    (f := fun r : ℝ => g (X r.toNNReal omega)) (a := (0 : ℝ)) (b := (t : ℝ)) (s : ℝ)
  simp only [add_zero,NNReal.coe_add] at he ⊢
  rw [← he]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le t.coe_nonneg] at hr
  dsimp only
  rw [Real.toNNReal_add s.coe_nonneg hr.1,Real.toNNReal_coe]
  rfl

/-- The original actual strong SDE restarts after `s` with the true
random initial state `X_s`, driven by the proved centered future Brownian
coordinates in the full filtration `F(s+t)`. -/
theorem strongSolution_timeShift
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,Continuous (b i)) (hsigma : ∀ i j,Continuous (sigma i j))
    (D : BrownianDriver N P F) (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N)
    (s T : ℝ≥0) (hsol : IsStrongSolutionOn b sigma hsigma D Z0 X (s+T)) :
    IsStrongSolutionOn b sigma hsigma (ShiftedBrownian.driver D s) (X s) (stateShift X s) T := by
  rcases hsol with ⟨hXa,hXc,hbmem,hsmem,heq⟩
  let hYa := stateShift_adapted X hXa s
  let hYc := stateShift_continuous X hXc s
  let hbnew := fun i => timeCut_shift_memLp (fun r omega => b i (X r omega)) s T (hbmem i)
  let hsnew := fun i j t (ht : t ≤ T) => timeCut_shift_memLp
    (fun r omega => sigma i j (X r omega)) s t (hsmem i j (s+t) (add_le_add le_rfl ht))
  refine ⟨hYa,hYc,hbnew,hsnew,?_⟩
  intro t ht i
  let U := fun j => coefficientPredictableActual hXa hXc (hsigma i j) (s+T) (hsmem i j (s+T) le_rfl)
  have hOld (r : ℝ≥0) (hr : r ≤ s+T) :
      driverItoMap D (fun j => coefficientPredictableActual hXa hXc (hsigma i j) r (hsmem i j r hr))=
        vectorProcessLp D U r := by
    rw [CutoffSphere.driverItoMap_eq_vectorIto]
    unfold vectorProcessLp
    congr 1
    funext j
    exact (CutoffSphere.coefficientPredictableActual_timeRestrict hXa hXc (hsigma i j)
      (s+T) r hr _ _).symm
  have hNew : driverItoMap (ShiftedBrownian.driver D s) (fun j =>
      coefficientPredictableActual hYa hYc (hsigma i j) t (hsnew i j t ht))=
        vectorProcessLp (ShiftedBrownian.driver D s) (fun j => predictableShift s (U j)) t := by
    rw [CutoffSphere.driverItoMap_eq_vectorIto]
    unfold vectorProcessLp
    congr 1
    funext j
    rw [predictableShift_timeRestrict]
    rw [CutoffSphere.coefficientPredictableActual_timeRestrict hXa hXc (hsigma i j)
      (s+T) (s+t) (add_le_add le_rfl ht) _ (hsmem i j (s+t) (add_le_add le_rfl ht))]
    exact coefficientPredictableActual_shift hXa hXc (hsigma i j) s t _
  rw [hNew,vectorProcessLp_timeShift]
  have h0 := heq s (le_add_right le_rfl) i
  have h1 := heq (s+t) (add_le_add le_rfl ht) i
  rw [hOld s (le_add_right le_rfl)] at h0
  rw [hOld (s+t) (add_le_add le_rfl ht)] at h1
  filter_upwards [h0,h1,Lp.coeFn_sub (vectorProcessLp D U (s+t)) (vectorProcessLp D U s),hXc]
    with omega h0 h1 hsub hc
  rw [hsub,Pi.sub_apply]
  have hcont : Continuous (fun r : ℝ => b i (X r.toNNReal omega)) :=
    (hb i).comp (hc.comp continuous_real_toNNReal)
  have hAdd := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (hcont.intervalIntegrable (0 : ℝ) s) (hcont.intervalIntegrable (s : ℝ) (s+t))
  have hdshift := drift_shift X (hb i) s t omega
  simp only [NNReal.coe_add] at hdshift h1
  rw [hdshift] at hAdd
  change X (s+t) omega i=X s omega i+_+_
  linarith

end SphericalAging.ShiftedSDE
