module

public import SphericalAging.ShiftedSDE
public import SphericalAging.AnnealedSDECore

public section

/-! Deterministic waiting-time restart for the literal random-coefficient
hard-sphere semantics. The same random disorder and actual future path
are retained; full-filtered stochastic integrals are genuinely identified. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedRandomSDE
open HardSphereDynamics VectorIto ShiftedSDE ShiftedPredictable TimeShiftMeasure ShiftedItoProcess AnnealedSDECore
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- A true random-coefficient strong solution restarts at the actual
waiting-time state. No independence of that state and the disorder is
required, and no stochastic operator equality is an input. -/
theorem randomStrongSolution_timeShift
    (D : BrownianDriver N P F)
    (b : Ω → Fin N → State N → ℝ) (sigma : Ω → Fin N → Fin N → State N → ℝ)
    (hb : ∀ omega i,Continuous (b omega i)) (Z0 : Ω → State N)
    (X : ℝ≥0 → Ω → State N) (s T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D b sigma Z0 X (s+T)) :
    IsRandomStrongSolutionOn (ShiftedBrownian.driver D s) b sigma (X s) (stateShift X s) T := by
  rcases hsol with ⟨hZ0,hXa,hXc,A,U,hA,hU,heq⟩
  refine ⟨ShiftedBrownian.initial_stronglyMeasurable X hXa s,stateShift_adapted X hXa s,
    stateShift_continuous X hXc s,fun i => predictableShift s (A i),
    fun i j => predictableShift s (U i j),?_,?_,?_⟩
  · intro i
    have he := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp (hA i)
    exact (predictableShift_coe s (A i)).trans (he.trans
      (timeCut_shift_ae (fun r omega => b omega i (X r omega)) s T).symm)
  · intro i j
    have he := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp (hU i j)
    exact (predictableShift_coe s (U i j)).trans (he.trans
      (timeCut_shift_ae (fun r omega => sigma omega i j (X r omega)) s T).symm)
  · intro t ht i
    rw [vectorProcessLp_timeShift]
    filter_upwards [heq s (le_add_right le_rfl) i,heq (s+t) (add_le_add le_rfl ht) i,
      Lp.coeFn_sub (vectorProcessLp D (U i) (s+t)) (vectorProcessLp D (U i) s),hXc]
      with omega h0 h1 hsub hc
    rw [hsub,Pi.sub_apply]
    have hcont : Continuous (fun r : ℝ => b omega i (X r.toNNReal omega)) :=
      (hb omega i).comp (hc.comp continuous_real_toNNReal)
    have hAdd := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
      (hcont.intervalIntegrable (0 : ℝ) s) (hcont.intervalIntegrable (s : ℝ) (s+t))
    have hdshift := drift_shift X (hb omega i) s t omega
    simp only [NNReal.coe_add] at hdshift h1
    rw [hdshift] at hAdd
    change X (s+t) omega i=X s omega i+_+_
    linarith

/-- Waiting-time sphere initial states have genuine L² integrability,
derived from the original common sphere path event. -/
lemma waiting_state_memLp (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hsphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega)) (s : ℝ≥0) : MemLp (X s) 2 P := by
  apply MemLp.of_bound ((hXa s).mono (F.le s)).aestronglyMeasurable (N+1 : ℝ)
  filter_upwards [hsphere] with omega hsp
  have hsq := (onSphere_iff_norm_sq _).mp (hsp s)
  nlinarith [norm_nonneg (X s omega),Nat.cast_nonneg (α := ℝ) N,sq_nonneg (N : ℝ)]

lemma waiting_state_onSphere (X : ℝ≥0 → Ω → State N)
    (hsphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega)) (s : ℝ≥0) :
    ∀ᵐ omega ∂P,OnSphere (X s omega) := hsphere.mono (fun _ h => h s)

/-- A common all-time sphere event persists under literal path restart. -/
lemma stateShift_onSphere (X : ℝ≥0 → Ω → State N)
    (hsphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega)) (s : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,OnSphere (stateShift X s t omega) := hsphere.mono (fun _ h t => h (s+t))

end SphericalAging.ShiftedRandomSDE
