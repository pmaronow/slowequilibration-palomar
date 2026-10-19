-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureActualHitComparison
public import SlowEquilibration.ConditionedEntrancePureJointCapHit
public import SlowEquilibration.ConditionedEntranceSourceJointCapHitProbability
public import SlowEquilibration.SphericalSmoothCapHitDriftCongruence

/-! Jointly measurable proper-pure source cap-hit probability indexed by
the physical conditioned axis and the uniform spherical start. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging HardSphereDynamics
open SphericalSmoothParameter SphericalSmoothTensorStationarity
open SphericalSmoothCapHitDriftCongruence
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 650000

theorem pure_axisJointHamiltonian_contDiff {N : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (e : ℝ) :
    ContDiff ℝ 2 (fun z : Vector N × Vector N =>
      pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2) := by
  have hMap : ContDiff ℝ 2 (fun z : Vector N × Vector N =>
      ((J,(z.1,(e,(0 : ℝ)))),z.2)) := by fun_prop
  exact (pureSourceJointHamiltonian_contDiff p hp c hc Q α χ hχ).comp hMap

theorem pure_axisJointGradient_contDiff {N : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (e : ℝ) :
    ContDiff ℝ 1 (jointSpatialGradient (fun z : Vector N × Vector N =>
      pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2)) :=
  jointSpatialGradient_contDiff _
    (pure_axisJointHamiltonian_contDiff p hp c hc Q α χ hχ J e)

def pureAxisCapHitProbability {N : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (T : ℝ≥0) (u x : Vector N) : ℝ :=
  let g := jointSpatialGradient (fun z : Vector N × Vector N =>
    pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2)
  capHitProbability β g (pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e)
    T (α/2) (u,(u,x))

theorem pureAxisCapHitProbability_measurable {N : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (T : ℝ≥0) :
    Measurable (fun z : Vector N × Vector N =>
      pureAxisCapHitProbability p hp c hc Q J β α χ hχ e T z.1 z.2) := by
  unfold pureAxisCapHitProbability
  exact (capHitProbability_measurable β _
    (pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e)
    T (α/2)).comp (by fun_prop)

theorem pureAxisCapHitProbability_mem_unit {N : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (T : ℝ≥0) (u x : Vector N) :
    pureAxisCapHitProbability p hp c hc Q J β α χ hχ e T u x ∈ Set.Icc 0 1 := by
  unfold pureAxisCapHitProbability
  exact capHitProbability_mem_unit β _
    (pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e)
    T (α/2) (u,(u,x))

theorem pureAxisCapHitProbability_eq_actual {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (T : ℝ≥0) (u : Vector N) (x : Vector N) :
    let D := SmoothKilledGeneral.FieldData.ofPure hN
      p hp c hc Q J u e α χ hχ
    pureAxisCapHitProbability p hp c hc Q J β α χ hχ e T u x =
      (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0, t ≤ T ∧ α/2 ≤
        |SphericalOverlapExponential.overlapValue u
          (SmoothKilledGeneral.process D β x t ω)|} := by
  dsimp only
  let D := SmoothKilledGeneral.FieldData.ofPure hN p hp c hc Q J u e α χ hχ
  let g := jointSpatialGradient (fun z : Vector N × Vector N =>
    pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2)
  let hg := pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e
  have hgEq : (fun y => g (u,y)) =
      smoothGradient D.hamiltonian D.hamiltonian_contDiff := by
    funext y
    change gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) y =
      gradient D.hamiltonian y
    rw [SmoothKilledGeneral.FieldData.ofPure_hamiltonian hN
      p hp c hc Q J u e α χ hχ]
  have hActual := capHitProbability_eq_actual β g hg T (α/2) (u,(u,x))
  change capHitProbability β g hg T (α/2) (u,(u,x)) =
    (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0,t ≤ T ∧
      α/2 ≤ |SphericalOverlapExponential.overlapValue u
        (SmoothKilledGeneral.process D β x t ω)|}
  rw [hActual]
  apply measureReal_congr
  filter_upwards [SmoothKilledGeneral.process_ae_actual D β x] with ω he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · simpa only [hgEq,SphericalOverlapExponential.overlapValue_eq,
      SphericalModel.overlap,he t] using hh
  · simpa only [hgEq,SphericalOverlapExponential.overlapValue_eq,
      SphericalModel.overlap,he t] using hh

/-- The one-axis uniform-start source probability is the integral of the
jointly measurable two-variable cap-hit kernel. -/
theorem pureSourceCapHitProbability_eq_axisIntegral {N : ℕ}
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (T : ℝ≥0) (u : Vector N) :
    pureSourceCapHitProbability p hp c hc Q α χ hχ β T
      (J,(u,(e,0))) =
    ∫ x : Vector N, pureAxisCapHitProbability p hp c hc Q J β α χ hχ e T u x
      ∂sphereLaw N := by
  let g₁ := jointSpatialGradient (pureSourceJointHamiltonian
    (N:=N) p hp c hc Q α χ)
  let g₂ := jointSpatialGradient (fun z : Vector N × Vector N =>
    pureSourceSmoothCutoffField p hp c hc Q J z.1 e α χ z.2)
  have hgrad (y : Vector N) : g₁ ((J,(u,(e,0))),y) = g₂ (u,y) := by
    change gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) y =
      gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) y
    rfl
  change uniformCapHitProbability β g₁
    (pureSourceJointSpatialGradient_contDiff p hp c hc Q α χ hχ)
    T (α/2) (u,(J,(u,(e,0)))) =
    uniformCapHitProbability β g₂
      (pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e)
      T (α/2) (u,u)
  exact uniformCapHitProbability_eq_of_fixed_drift_eq β g₁
    (pureSourceJointSpatialGradient_contDiff p hp c hc Q α χ hχ)
    g₂ (pure_axisJointGradient_contDiff p hp c hc Q α χ hχ J e)
    T (α/2) u (J,(u,(e,0))) u hgrad

end SlowEquilibration.ConditionedEntrance
