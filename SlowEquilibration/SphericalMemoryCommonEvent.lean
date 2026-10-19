-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMemoryAssembly
public import SlowEquilibration.SphericalGibbsAllDimensions

@[expose] public section

/-! # One Borel disorder event for all five actual memory conclusions

The event is the intersection of the literal cap/core/collar partition-test
event and the literal replica-tail event. Its failure probability is reduced
to actual field pressure, actual joint Gibbs-reference partition tests and
actual replica-tail probabilities. No headline conclusion appears among the
inputs of this probability reduction.
-/

namespace SlowEquilibration.SphericalMemoryAssembly
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalBarycenter SphericalQuantitativeTrap
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def replicaTailEvent (μ : FiniteMixture) (β ε r : ℝ) : Set (Disorder N μ.maxDegree) :=
  {D | ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real (replicaOverlapEvent ε) ≤
    Real.exp (-r*N)}

theorem replicaTailEvent_measurable (μ : FiniteMixture) (β ε r : ℝ) :
    MeasurableSet (replicaTailEvent (N := N) μ β ε r) := by
  let k := allDimensionGibbsKernel (N := N) (mixtureCoefficients μ) β
  have hm : Measurable (fun D : Disorder N μ.maxDegree =>
      ((k ×ₖ k) D).real (replicaOverlapEvent ε)) :=
    ((k ×ₖ k).measurable_coe (replicaOverlapEvent_measurable ε)).ennreal_toReal
  have he : (fun D : Disorder N μ.maxDegree => ((k ×ₖ k) D).real (replicaOverlapEvent ε)) =
      fun D => ((mixtureGibbsLaw μ β D).prod (mixtureGibbsLaw μ β D)).real (replicaOverlapEvent ε) := by
    funext D
    rw [Kernel.prod_apply]
    simp only [k,allDimensionGibbsKernel_apply]
    rfl
  rw [he] at hm
  exact measurableSet_le hm measurable_const

def commonMemoryEvent (μ : FiniteMixture) (β F J G δ q₁ q₂ q w a ε r : ℝ) :
    Set (Disorder N μ.maxDegree) :=
  goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a*N)) ∩
    replicaTailEvent μ β ε r

theorem commonMemoryEvent_measurable (hN : 1 ≤ N) (μ : FiniteMixture)
    (β F J G δ q₁ q₂ q w a ε r : ℝ) :
    MeasurableSet (commonMemoryEvent (N := N) μ β F J G δ q₁ q₂ q w a ε r) :=
  (goodCapCoreCollarEvent_measurable hN (mixtureCoefficients μ) β F J G δ q₁ q₂ q w _).inter
    (replicaTailEvent_measurable μ β ε r)

/-- The one-event failure bound retains precisely the genuine remaining
quantitative inputs: pressure, joint cap/core/collar tests and replica mass. -/
theorem commonMemoryEvent_failure_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (β F J G δ q₁ q₂ q w a ε r : ℝ) :
    (disorderLaw N μ.maxDegree).real
      (commonMemoryEvent μ β F J G δ q₁ q₂ q w a ε r)ᶜ ≤
      (disorderLaw N μ.maxDegree).real
        {D | δ < |Real.log (partition N β (fieldOfMixture μ D))/(N : ℝ)-F|}+
      (gibbsReferenceLaw (N := N) (mixtureCoefficients μ) β).real
        (capCoreCollarBadEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w)*Real.exp (a*N)+
      (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ := by
  rw [commonMemoryEvent,compl_inter]
  exact (measureReal_union_le _ _).trans
    (add_le_add (source_good_event_failure_le hN (mixtureCoefficients μ)
      β F J G δ q₁ q₂ q w a) le_rfl)

theorem MemoryConclusions.weaken_errors {hN : 2 ≤ N} {μ : FiniteMixture} {β : ℝ}
    {D : Disorder N μ.maxDegree} {b κ γ a c C a' C' : ℝ}
    (hm : MemoryConclusions hN μ β D b κ γ a c C)
    (hC : 0 ≤ C) (ha' : a'≤a) (hC' : C≤C') :
    MemoryConclusions hN μ β D b κ γ a' c C' := by
  have he : C*Real.exp (-a*N)≤C'*Real.exp (-a'*N) := by
    apply (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ha') (by positivity))) hC).trans
    exact mul_le_mul_of_nonneg_right hC' (Real.exp_pos _).le
  obtain ⟨X,hXm,hXs,hMass,hTV⟩ := hm.typicalStartingPoints
  refine ⟨hm.eigenvalue,hm.spinProjection,hm.connectedCorrelation,⟨X,hXm,hXs,?_,?_⟩,
    hm.stationaryInformation⟩
  · exact (sub_le_sub_left he 1).trans hMass
  · intro x hx t ht
    exact (sub_le_sub_left he 1).trans (hTV x hx t ht)

/-- A simultaneous exponentially likely Borel event is obtained from
actual pressure, actual Gibbs-reference tests and actual replica failures.
The same positive a and C serve disorder probability and Gibbs-typical TV.
The probabilities are explicit intermediate obligations, not substitutes
for eigenvalue, spin, trapping or information assertions. -/
theorem constructed_memory_common_event (μ : FiniteMixture) (β F J G δ q₁ q₂ q w a ε b r : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hgap : 4*δ < G) (ha : 0 < a)
    (hq₁ : q₁ ∈ Ioo (0 : ℝ) 1) (hq : q₁ < q₂) (hcore : q₂≤q-w)
    (hε : 0 ≤ ε) (hb : 0 ≤ b) (hr : 0 < r)
    (hmargin : Real.sqrt b + Real.sqrt ε < q₁)
    (hεcap : ε ≤ (q₁/4)^2/2) (hδr : 4*δ < r/4)
    (CP CJ CR sP sJ sR : ℝ) (hCP : 0 ≤ CP) (hCJ : 0 ≤ CJ) (hCR : 0 ≤ CR)
    (hsP : 0 < sP) (hsJ : a < sJ) (hsR : 0 < sR)
    (hPressure : ∀ᶠ N : ℕ in atTop, (disorderLaw N μ.maxDegree).real
      {D | δ < |Real.log (partition N β (fieldOfMixture μ D))/(N : ℝ)-F|} ≤ CP*Real.exp (-sP*N))
    (hJoint : ∀ᶠ N : ℕ in atTop,
      (gibbsReferenceLaw (N := N) (mixtureCoefficients μ) β).real
        (capCoreCollarBadEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w) ≤ CJ*Real.exp (-sJ*N))
    (hReplica : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ ≤ CR*Real.exp (-sR*N)) :
    ∃ κ γ aM cM CM : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < aM ∧ 0 < cM ∧ 0 < CM ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ CM*Real.exp (-aM*N) ∧
        ∀ D ∈ Ω, ∀ hN : 2 ≤ N, MemoryConclusions hN μ β D b κ γ aM cM CM := by
  obtain ⟨κ,γ,a₀,cM,C₀,hκ,hγ,ha₀,hcM,hC₀,hMemory⟩ :=
    constructed_memory_eventually μ β J G δ q₁ q₂ a ε b r
      hJ hδ hgap ha hq₁ hq hε hb hr hmargin hεcap hδr
  let s := min sP (min (sJ-a) sR)
  let aM := min a₀ s
  let CM := max C₀ (CP+CJ+CR)
  have hs : 0 < s := lt_min hsP (lt_min (sub_pos.mpr hsJ) hsR)
  have hAM : 0 < aM := lt_min ha₀ hs
  have hCM : 0 < CM := hC₀.trans_le (le_max_left _ _)
  refine ⟨κ,γ,aM,cM,CM,hκ,hγ,hAM,hcM,hCM,?_⟩
  filter_upwards [hMemory,hPressure,hJoint,hReplica,eventually_ge_atTop (2 : ℕ)]
    with N hMemory hPressure hJoint hReplica hN
  refine ⟨commonMemoryEvent μ β F J G δ q₁ q₂ q w a ε r,
    commonMemoryEvent_measurable (by omega) μ β F J G δ q₁ q₂ q w a ε r,?_,?_⟩
  · have hfail := commonMemoryEvent_failure_le (show 1 ≤ N by omega) μ β F J G δ q₁ q₂ q w a ε r
    have hAM₀ : aM ≤ sP := (min_le_right _ _).trans (min_le_left _ _)
    have hAM₁ : aM ≤ sJ-a := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    have hAM₂ : aM ≤ sR := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    have hExp (z : ℝ) (hz : aM≤z) : Real.exp (-z*N)≤Real.exp (-aM*N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) (by positivity))
    apply hfail.trans
    calc
      _ ≤ CP*Real.exp (-sP*N)+(CJ*Real.exp (-sJ*N))*Real.exp (a*N)+CR*Real.exp (-sR*N) :=
        add_le_add (add_le_add hPressure
          (mul_le_mul_of_nonneg_right hJoint (Real.exp_pos _).le)) hReplica
      _ = CP*Real.exp (-sP*N)+CJ*Real.exp (-(sJ-a)*N)+CR*Real.exp (-sR*N) := by
        rw [mul_assoc,← Real.exp_add]
        congr 3
        ring_nf
      _ ≤ (CP+CJ+CR)*Real.exp (-aM*N) := by
        have hsum := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hExp sP hAM₀) hCP)
          (mul_le_mul_of_nonneg_left (hExp (sJ-a) hAM₁) hCJ))
          (mul_le_mul_of_nonneg_left (hExp sR hAM₂) hCR)
        convert hsum using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · intro D hD hN'
    exact (hMemory hN' F q w D hcore hD.1 hD.2).weaken_errors hC₀.le
      (min_le_left _ _) (le_max_left _ _)

/-- Interface for the internally proved good-reference probability
theorems. Both hypotheses are literal actual finite-volume event failures,
so the final mixture theorem can consume those proved providers directly. -/
theorem constructed_memory_common_event_of_failure_bounds
    (μ : FiniteMixture) (β F J G δ q₁ q₂ q w a ε b r : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hgap : 4*δ < G) (ha : 0 < a)
    (hq₁ : q₁ ∈ Ioo (0 : ℝ) 1) (hq : q₁ < q₂) (hcore : q₂≤q-w)
    (hε : 0 ≤ ε) (hb : 0 ≤ b) (hr : 0 < r)
    (hmargin : Real.sqrt b + Real.sqrt ε < q₁)
    (hεcap : ε ≤ (q₁/4)^2/2) (hδr : 4*δ < r/4)
    (CG CR sG sR : ℝ) (hCG : 0 ≤ CG) (hCR : 0 ≤ CR) (hsG : 0 < sG) (hsR : 0 < sR)
    (hGood : ∀ᶠ N : ℕ in atTop, (disorderLaw N μ.maxDegree).real
      (goodCapCoreCollarEvent (mixtureCoefficients μ) β F J G δ q₁ q₂ q w (Real.exp (-a*N)))ᶜ ≤
        CG*Real.exp (-sG*N))
    (hReplica : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real (replicaTailEvent μ β ε r)ᶜ ≤ CR*Real.exp (-sR*N)) :
    ∃ κ γ aM cM CM : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < aM ∧ 0 < cM ∧ 0 < CM ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ CM*Real.exp (-aM*N) ∧
        ∀ D ∈ Ω, ∀ hN : 2 ≤ N, MemoryConclusions hN μ β D b κ γ aM cM CM := by
  obtain ⟨κ,γ,a₀,cM,C₀,hκ,hγ,ha₀,hcM,hC₀,hMemory⟩ :=
    constructed_memory_eventually μ β J G δ q₁ q₂ a ε b r
      hJ hδ hgap ha hq₁ hq hε hb hr hmargin hεcap hδr
  let aM := min a₀ (min sG sR)
  let CM := max C₀ (CG+CR)
  have hAM : 0 < aM := lt_min ha₀ (lt_min hsG hsR)
  have hCM : 0 < CM := hC₀.trans_le (le_max_left _ _)
  refine ⟨κ,γ,aM,cM,CM,hκ,hγ,hAM,hcM,hCM,?_⟩
  filter_upwards [hMemory,hGood,hReplica,eventually_ge_atTop (2 : ℕ)]
    with N hMemory hGood hReplica hN
  refine ⟨commonMemoryEvent μ β F J G δ q₁ q₂ q w a ε r,
    commonMemoryEvent_measurable (by omega) μ β F J G δ q₁ q₂ q w a ε r,?_,?_⟩
  · rw [commonMemoryEvent,compl_inter]
    have hAMG : aM ≤ sG := (min_le_right _ _).trans (min_le_left _ _)
    have hAMR : aM ≤ sR := (min_le_right _ _).trans (min_le_right _ _)
    have hExp (z : ℝ) (hz : aM≤z) : Real.exp (-z*N)≤Real.exp (-aM*N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz) (by positivity))
    apply (measureReal_union_le _ _).trans
    calc
      _ ≤ CG*Real.exp (-sG*N)+CR*Real.exp (-sR*N) := add_le_add hGood hReplica
      _ ≤ (CG+CR)*Real.exp (-aM*N) := by
        have hsum := add_le_add (mul_le_mul_of_nonneg_left (hExp sG hAMG) hCG)
          (mul_le_mul_of_nonneg_left (hExp sR hAMR) hCR)
        convert hsum using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · intro D hD hN'
    exact (hMemory hN' F q w D hcore hD.1 hD.2).weaken_errors hC₀.le
      (min_le_left _ _) (le_max_left _ _)

end
end SlowEquilibration.SphericalMemoryAssembly
