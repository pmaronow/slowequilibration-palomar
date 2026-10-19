-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureJointCapHit
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralField
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralSemigroup

/-! The jointly measurable one-start source cutoff probability is exactly
the physical Brownian cap-hit probability on spherical axes. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalSmoothTensorStationarity
open SphericalSmoothParameter SphericalOverlapExponential
open SphericalAging HardSphereDynamics SmoothKilledGeneral
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000

def pureSourceCapHitFibre {N : ℕ} (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ) (α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0)
    (z : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N) : ℝ :=
  capHitProbability β
    (jointSpatialGradient (pureSourceJointHamiltonian d hd c hc Q α χ))
    (pureSourceJointSpatialGradient_contDiff d hd c hc Q α χ hχ)
    H (α/2) (z.1.2.1,(z.1,z.2))

theorem pureSourceCapHitFibre_measurable {N : ℕ} (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) :
    Measurable (pureSourceCapHitFibre (N:=N) d hd c hc Q α χ hχ β H) := by
  unfold pureSourceCapHitFibre
  exact (capHitProbability_measurable β _ _ H (α/2)).comp
    (measurable_fst.snd.fst.prodMk (measurable_fst.prodMk measurable_snd))

theorem pureSourceCapHitProbability_eq_integral_fibre {N : ℕ}
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ) (α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0)
    (p : SourceParameters N (FiniteMixture.pure d hd c hc)) :
    pureSourceCapHitProbability d hd c hc Q α χ hχ β H p =
      ∫ x, pureSourceCapHitFibre d hd c hc Q α χ hχ β H (p,x) ∂sphereLaw N := rfl

theorem pureSourceCapHitFibre_mem_unit {N : ℕ} (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (z : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N) :
    pureSourceCapHitFibre d hd c hc Q α χ hχ β H z ∈ Set.Icc 0 1 :=
  capHitProbability_mem_unit β _ _ H (α/2) _

-- The stated positivity and sphere hypotheses are not needed for this identity.
set_option linter.unusedVariables false in
theorem pureSourceCapHitFibre_eq_actual {N : ℕ} (hN : 1 ≤ N)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (p : SourceParameters N (FiniteMixture.pure d hd c hc))
    (hp : OnSphere p.2.1) (x : Vector N) :
    let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
    pureSourceCapHitFibre d hd c hc Q α χ hχ β H (p,x) =
      (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
        α/2 ≤ |overlapValue p.2.1 (SmoothKilledGeneral.process D β x t ω)|} := by
  dsimp only
  let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
  let g := jointSpatialGradient (pureSourceJointHamiltonian (N:=N) d hd c hc Q α χ)
  let hg := pureSourceJointSpatialGradient_contDiff (N:=N) d hd c hc Q α χ hχ
  have hgEq : (fun y => g (p,y)) = smoothGradient D.hamiltonian D.hamiltonian_contDiff := by
    funext y
    change gradient (pureSourceSmoothCutoffField d hd c hc Q p.1 p.2.1 p.2.2.1 α χ) y =
      gradient D.hamiltonian y
    rw [FieldData.ofPure_hamiltonian hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ]
  have hActual := capHitProbability_eq_actual β g hg H (α/2) (p.2.1,(p,x))
  change capHitProbability β g hg H (α/2) (p.2.1,(p,x)) =
    (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      α/2 ≤ |overlapValue p.2.1 (SmoothKilledGeneral.process D β x t ω)|}
  rw [hActual]
  apply measureReal_congr
  filter_upwards [SmoothKilledGeneral.process_ae_actual D β x] with ω he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · simpa only [hgEq,SphericalOverlapExponential.overlapValue_eq,
      SphericalModel.overlap,he t] using hh
  · simpa only [hgEq,SphericalOverlapExponential.overlapValue_eq,
      SphericalModel.overlap,he t] using hh

end SlowEquilibration.ConditionedEntrance
