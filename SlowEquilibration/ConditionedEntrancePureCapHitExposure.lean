-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureAxisCapHit
public import SlowEquilibration.ConditionedEntrancePhysicalHittingBound

/-! Finite-horizon exposure of the genuine proper-pure cutoff cap hit to
physical discounted cap-killing mass. The gradient constant is explicit data
so the subsequent tensor-regularity estimate can close it. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalAging HardSphereDynamics
open SphericalOverlapExponential SphericalSmoothTensorStationarity
open PhysicalHitting FeynmanKac
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem pure_axis_cap_hit_exposure_le_physical_firing {N : ℕ}
    (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (β α : ℝ) (hβ : 0 ≤ β) (hα : 0 < α)
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (e : ℝ) (u x : Vector N) (hu : OnSphere u) (hx : OnSphere x)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ y, OnSphere y →
      ‖gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) y‖ ≤
        C*Real.sqrt (N : ℝ))
    (θ : ℝ) (hθ : 0 ≤ θ) (H T : ℝ≥0) (hT : 0 < T)
    (hshort : 4*(1+β*C)*(T:ℝ) ≤ α/12) :
    let D := SmoothKilledGeneral.FieldData.ofPure hN
      p hp c hc Q J u e α χ hχ
    exposureFactor θ H T *
      (pureAxisCapHitProbability p hp c hc Q J β α χ hχ e H u x -
        (gridSize H T : ℝ) *
          (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T:ℝ))))) ≤
      ∫ ω, finiteDiscountedMass (capKilling α u)
        (SmoothKilledGeneral.process D β x) θ (H+T) ω
        ∂VectorBrownian.law N := by
  dsimp only
  let D := SmoothKilledGeneral.FieldData.ofPure hN p hp c hc Q J u e α χ hχ
  let g := smoothGradient D.hamiltonian D.hamiltonian_contDiff
  let hg := smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff
  let κ := capKilling α u
  have hgrad' : ∀ y, OnSphere y → ‖g y‖ ≤ C*Real.sqrt (N : ℝ) := by
    intro y hy
    change ‖gradient D.hamiltonian y‖ ≤ _
    rw [SmoothKilledGeneral.FieldData.ofPure_hamiltonian hN
      p hp c hc Q J u e α χ hχ]
    exact hgrad y hy
  have hPhysical := joint_physical_hitting_discounted_mass
    (by omega : N ≠ 0) hβ hC g hg hgrad' u x hu hx hα κ
    (capKilling_contDiff α u).continuous (capKilling_nonneg α u)
    (capKilling_le_one hα u)
    (fun y hy => (capKilling_one hα u y hy).ge)
    hθ H T hT hshort
  have hPath : ∀ᵐ ω ∂VectorBrownian.law N, ∀ t,
      SmoothKilledGeneral.process D β x t ω =
        jointPhysicalProcess β g hg x t ω := by
    filter_upwards [SmoothKilledGeneral.process_ae_actual D β x,
      jointPhysicalProcess_ae_actual β g hg x] with ω hD hJ
    intro t
    exact (hD t).trans (hJ t).symm
  have hEvent :
      (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0,t ≤ H ∧
        α/2 ≤ |overlapValue u (SmoothKilledGeneral.process D β x t ω)|} =
      (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0,t ≤ H ∧
        α/2 ≤ |overlapValue u (jointPhysicalProcess β g hg x t ω)|} := by
    apply measureReal_congr
    filter_upwards [hPath] with ω hω
    apply propext
    simp only [hω]
  have hMass :
      (∫ ω,finiteDiscountedMass κ (jointPhysicalProcess β g hg x) θ (H+T) ω
        ∂VectorBrownian.law N) =
      ∫ ω,finiteDiscountedMass κ (SmoothKilledGeneral.process D β x) θ (H+T) ω
        ∂VectorBrownian.law N := by
    apply integral_congr_ae
    filter_upwards [hPath] with ω hω
    unfold finiteDiscountedMass survival occupation
    simp_rw [← hω]
  have hActual := pureAxisCapHitProbability_eq_actual hN p hp c hc Q J
    β α χ hχ e H u x
  rw [hActual,hEvent]
  calc
    _ ≤ ∫ ω,finiteDiscountedMass κ (jointPhysicalProcess β g hg x) θ (H+T) ω
        ∂VectorBrownian.law N := by simpa only [mul_assoc] using hPhysical
    _ = _ := hMass

end SlowEquilibration.ConditionedEntrance
