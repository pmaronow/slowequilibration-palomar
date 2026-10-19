module

public import SphericalAging.AnnealedPhysicalSDE
public import SphericalAging.AnnealedModelLaw

public section

/-! Genuine all-time annealed hard-sphere dynamics. Actual finite-horizon
integral solutions are shown compatible by their proved parameter sections,
then glued on the countable integer horizons. The result satisfies the
actual random-disorder untruncated matrix SDE on every horizon, and remains
on the physical sphere on one common probability-one event at all times.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedGlobalSDE
open HardSphereDynamics AnnealedCutoffProcess AnnealedSDECore
open IndependentBackgroundDriver
set_option maxHeartbeats 1200000
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {ρ : Measure (Parameter N p)} [IsProbabilityMeasure ρ]

/-- Genuine common-path compatibility of annealed integral solutions. -/
theorem process_compatible_pair (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (S T : ℝ≥0) :
    ∀ᵐ ω ∂ρ.prod P, ∀ t, t ≤ S → t ≤ T →
      process D β R hR hJ S t ω=process D β R hR hJ T t ω := by
  have hfixed (t : ℝ≥0) (ht : t ≤ min S T) : process D β R hR hJ S t =ᵐ[ρ.prod P]
      process D β R hR hJ T t := by
    have hs := (process_stronglyAdapted D β R hR hJ S t).mono
      ((filtration (Parameter N p) F).le t)
    have hT := (process_stronglyAdapted D β R hR hJ T t).mono
      ((filtration (Parameter N p) F).le t)
    apply (Measure.ae_prod_iff_ae_ae (hs.measurableSet_eq_fun hT)).mpr
    filter_upwards [process_slice_global D β R hR hJ S,process_slice_global D β R hR hJ T]
      with q hS hT
    filter_upwards [hS,hT] with ω hS hT
    exact (hS t (ht.trans (min_le_left _ _))).trans (hT t (ht.trans (min_le_right _ _))).symm
  have hcommon := StrongUniqueness.continuous_state_processes_ae_eq_of_fixedTime_on
    (process_continuous D β R hR hJ S) (process_continuous D β R hR hJ T) hfixed
  filter_upwards [hcommon] with ω hω
  intro t htS htT
  exact hω t (le_min htS htT)

@[expose] def globalProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (t : ℝ≥0)
    (ω : Parameter N p × Ω) : State N :=
  process D β R hR hJ (GlobalSDE.integerHorizon (Nat.ceil t)) t ω

theorem globalProcess_stronglyAdapted (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) :
    StronglyAdapted (filtration (Parameter N p) F) (globalProcess D β R hR hJ) :=
  fun t => process_stronglyAdapted D β R hR hJ _ t

theorem globalProcess_eq_horizon (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) (T : ℝ≥0) :
    ∀ᵐ ω ∂ρ.prod P, ∀ t, t ≤ T → globalProcess D β R hR hJ t ω=process D β R hR hJ T t ω := by
  filter_upwards [ae_all_iff.mpr (fun n : ℕ => process_compatible_pair D β R hR hJ
    (GlobalSDE.integerHorizon n) T)] with ω hω
  intro t ht
  exact hω (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t) ht

theorem globalProcess_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => globalProcess D β R hR hJ t ω) := by
  have heq := ae_all_iff.mpr (fun n : ℕ => globalProcess_eq_horizon D β R hR hJ (GlobalSDE.integerHorizon n))
  have hcts := ae_all_iff.mpr (fun n : ℕ => process_continuous D β R hR hJ (GlobalSDE.integerHorizon n))
  filter_upwards [heq,hcts] with ω heq hcts
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have htn : t < GlobalSDE.integerHorizon n := hn.trans_le (by simp [GlobalSDE.integerHorizon])
  have hlocal : (fun s => globalProcess D β R hR hJ s ω) =ᶠ[𝓝 t]
      (fun s => process D β R hR hJ (GlobalSDE.integerHorizon n) s ω) := by
    filter_upwards [eventually_lt_nhds htn] with s hs
    exact heq n s hs.le
  exact (continuousAt_congr hlocal).mpr (hcts n).continuousAt

/-- Equality on a common horizon path event preserves every actual random
coefficient class and real drift integral in the genuine strong equation. -/
theorem IsRandomStrongSolutionOn.path_congr
    {D : BrownianDriver N P F} {b : Ω → Fin N → State N → ℝ}
    {sigma : Ω → Fin N → Fin N → State N → ℝ} {Z₀ : Ω → State N}
    {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hX : IsRandomStrongSolutionOn D b sigma Z₀ X T)
    (hYa : StronglyAdapted F Y) (hYc : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hYX : ∀ᵐ ω ∂P, ∀ t, t ≤ T → Y t ω=X t ω) :
    IsRandomStrongSolutionOn D b sigma Z₀ Y T := by
  rcases hX with ⟨h0,hXa,hXc,A,U,hA,hU,heq⟩
  have hpath := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hYX
  have hcoeval (g : Ω → State N → ℝ) : FourPapersCommon.continuousAdaptedTimeCut
      (fun t ω => g ω (X t ω)) T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t ω => g ω (Y t ω)) T := by
    filter_upwards [hpath] with z hz
    by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht,hz z.1 ht.2]
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right ht]
  refine ⟨h0,hYa,hYc,A,U,(fun i => (hA i).trans (hcoeval (fun ω x => b ω i x))),
    (fun i j => (hU i j).trans (hcoeval (fun ω x => sigma ω i j x))),?_⟩
  intro t ht i
  filter_upwards [heq t ht i,hYX] with ω heq hYX
  have hd : (∫ s in (0 : ℝ)..(t : ℝ), b ω i (Y s.toNNReal ω)) =
      ∫ s in (0 : ℝ)..(t : ℝ), b ω i (X s.toNNReal ω) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ≤ (t : ℝ) := (show s ∈ Icc (0 : ℝ) (t : ℝ) from by
      simpa only [uIcc_of_le t.coe_nonneg] using hs).2
    have hsNN : s.toNNReal ≤ t := by simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hst
    dsimp only
    rw [hYX s.toNNReal (hsNN.trans ht)]
  rw [hYX t ht,hd]
  exact heq

/-- Genuine all-time annealed physical solution, including one common
probability-one sphere event for every nonnegative time. -/
theorem globalProcess_physical (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ)
    (hinitial : ∀ᵐ q ∂ρ, OnSphere q.2) :
    (∀ T, IsRandomStrongSolutionOn (driver (ρ := ρ) (NullAugmentation.driver D))
      (fun ω i x => hamiltonianDrift β ω.1.1 x i) (fun _ i j x => noiseColumn x j i)
      (fun ω => ω.1.2) (globalProcess (NullAugmentation.driver D) β R hR hJ) T) ∧
    (∀ᵐ ω ∂ρ.prod P, ∀ t, OnSphere (globalProcess (NullAugmentation.driver D) β R hR hJ t ω)) := by
  let D' := NullAugmentation.driver D
  have hfinite := fun T => AnnealedPhysicalSDE.process_strongSolution hN D β R hR hNR hJ hinitial T
  refine ⟨fun T => ?_,?_⟩
  · exact IsRandomStrongSolutionOn.path_congr (hfinite T).1
      (globalProcess_stronglyAdapted D' β R hR hJ) (globalProcess_continuous D' β R hR hJ)
      (globalProcess_eq_horizon D' β R hR hJ T)
  · have heq := ae_all_iff.mpr (fun n : ℕ => globalProcess_eq_horizon D' β R hR hJ (GlobalSDE.integerHorizon n))
    have hs := ae_all_iff.mpr (fun n : ℕ => (hfinite (GlobalSDE.integerHorizon n)).2)
    filter_upwards [heq,hs] with ω heq hs
    intro t
    rw [heq (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)]
    exact hs (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

/-- Concrete actual Gaussian-disorder, normalized-surface-initial, and
independent Wiener-path model. Existence and all-time sphere preservation
require no Brownian-driver, coefficient-class or SDE existence premise. -/
theorem exists_on_actual_model {N p : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    ∃ X : ℝ≥0 → (Parameter N p × VectorBrownian.Space N) → State N,
      StronglyAdapted (AnnealedModelLaw.filtration N p) X ∧
      (∀ᵐ ω ∂AnnealedModelLaw.law N p, Continuous (fun t => X t ω)) ∧
      (∀ T, IsRandomStrongSolutionOn (AnnealedModelLaw.driver N p)
        (fun ω i x => hamiltonianDrift β ω.1.1 x i) (fun _ i j x => noiseColumn x j i)
        (fun ω => ω.1.2) X T) ∧
      (∀ᵐ ω ∂AnnealedModelLaw.law N p, ∀ t, OnSphere (X t ω)) := by
  let R : ℝ≥0 := N+1
  have hR : 0 < (R : ℝ) := by simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; positivity
  have hNR : (N : ℝ) < (R : ℝ)^2 := by
    simp only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    nlinarith [sq_nonneg (N : ℝ),Nat.cast_nonneg (α := ℝ) N]
  let hJ := AnnealedModelLaw.parameter_disorder_memLp N p
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := globalProcess D β R hR hJ
  have hp := globalProcess_physical (by omega : N ≠ 0) (VectorBrownian.driver N) β R hR hNR hJ
    (AnnealedModelLaw.parameter_initial_onSphere hN p)
  exact ⟨X,globalProcess_stronglyAdapted D β R hR hJ,globalProcess_continuous D β R hR hJ,hp⟩

end SphericalAging.AnnealedGlobalSDE
