-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.EntranceSmoothCutoffTensorApproximation

/-! Actual physical Gibbs stationarity for the nonpolynomial entrance
cutoff Hamiltonian. Its concrete ordered-tensor C¹ approximants, field
bounds, and Brownian drift convergence are proved before this consumer. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open EntranceSmoothCutoffCalculus EntranceSmoothCutoffTensorApproximation
open SphericalSmoothTensorStationarity
open scoped NNReal RealInnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem smoothCutoffField_gibbs_invariant (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (Q : ℝ) (u G v₁ v₂ : Vector N)
    (Hq Kq h k : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (t : ℝ≥0) :
    smoothTransitionKernel (smoothCutoffField μ J Q u G v₁ v₂ Hq Kq h k χ)
      (smoothCutoffField_contDiff hN μ J Q u G v₁ v₂ Hq Kq h k χ hχ) β t ∘ₘ
      gibbsLaw N β (smoothCutoffField μ J Q u G v₁ v₂ Hq Kq h k χ)=
        gibbsLaw N β (smoothCutoffField μ J Q u G v₁ v₂ Hq Kq h k χ) := by
  obtain ⟨ν,K,M,δ,hM,hfield,hδ,hgrad,hlim⟩ :=
    exists_actual_tensor_approximants hN μ J Q u G v₁ v₂ Hq Kq h k χ hχ
  exact smoothTransitionKernel_gibbs_invariant hN _ _ ν K M hM hfield δ hδ hgrad hlim β t

/-- The actual source Hamiltonian with the two prescribed linear cutoff
arguments, attached to the same sampled center value, radial jet, and
tangential gradient as the Gaussian-regression posterior. -/
def sourceSmoothCutoffField (μ : FiniteMixture) (Q : ℝ) (_hQ : 0 < Q)
    (_hnp : μ.minDegree < μ.maxDegree) (J : Disorder N μ.maxDegree)
    (u : Vector N) (h k α : ℝ) (χ : ℝ → ℝ) : Vector N → ℝ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let G := surfaceGradient (field c J) u
  smoothCutoffField μ J Q u G (((N : ℝ)*α)⁻¹ • u) (((N : ℝ)*α)⁻¹ • G)
    (field c J u) (jet c 1 u (fun _ => u) J) h k χ

theorem sourceSmoothCutoffField_eq (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (J : Disorder N μ.maxDegree)
    (u : Vector N) (h k α : ℝ) (χ : ℝ → ℝ) (x : Vector N) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let G := surfaceGradient (field c J) u
    sourceSmoothCutoffField μ Q hQ hnp J u h k α χ x=
      fieldOfMixture μ J x+χ (overlap x u/α)*χ (inner ℝ G x/((N : ℝ)*α))*
        sourceRegressionCorrection μ Q hQ hnp J u h k x := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let G := surfaceGradient (field c J) u
  have hr : inner ℝ (((N : ℝ)*α)⁻¹ • u) x=overlap x u/α := by
    rw [real_inner_smul_left]
    have hc : inner ℝ u x=inner ℝ x u := real_inner_comm _ _
    rw [hc]
    unfold overlap
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hs : inner ℝ (((N : ℝ)*α)⁻¹ • G) x=inner ℝ G x/((N : ℝ)*α) := by
    rw [real_inner_smul_left]
    exact (div_eq_inv_mul _ _).symm
  change fieldOfMixture μ J x+
    χ (inner ℝ (((N : ℝ)*α)⁻¹ • u) x)*χ (inner ℝ (((N : ℝ)*α)⁻¹ • G) x)*
      regressionCorrection μ Q u G (field c J u) (jet c 1 u (fun _ => u) J) h k x=_
  rw [hr,hs]
  rfl

theorem sourceSmoothCutoffField_contDiff (hN : 1 ≤ N) (μ : FiniteMixture) (Q : ℝ)
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (J : Disorder N μ.maxDegree)
    (u : Vector N) (h k α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (sourceSmoothCutoffField μ Q hQ hnp J u h k α χ) :=
  smoothCutoffField_contDiff hN μ J Q _ _ _ _ _ _ h k χ hχ

/-- The genuine Brownian source cutoff diffusion preserves its literal
normalized Gibbs law. All source observations are the actual posterior
regression fields; no stationarity or approximation premise appears. -/
theorem sourceSmoothCutoffField_gibbs_invariant (hN : 1 ≤ N) (μ : FiniteMixture) (Q : ℝ)
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (J : Disorder N μ.maxDegree)
    (u : Vector N) (h k α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (t : ℝ≥0) :
    smoothTransitionKernel (sourceSmoothCutoffField μ Q hQ hnp J u h k α χ)
      (sourceSmoothCutoffField_contDiff hN μ Q hQ hnp J u h k α χ hχ) β t ∘ₘ
      gibbsLaw N β (sourceSmoothCutoffField μ Q hQ hnp J u h k α χ)=
        gibbsLaw N β (sourceSmoothCutoffField μ Q hQ hnp J u h k α χ) :=
  smoothCutoffField_gibbs_invariant hN μ J Q _ _ _ _ _ _ h k χ hχ β t

end SlowEquilibration.ConditionedEntrance
