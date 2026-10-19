-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalPureSourceCorrection
public import SlowEquilibration.SphericalAtomSmoothCutoffStationarity

/-! Literal proper-pure source correction as a true two-atom homogeneous
bank, and its actual smooth cutoff diffusion with genuine Gibbs stationarity.
The construction uses the scalar value posterior and actual center gradient;
no singular score inverse or nonpure source representation is used. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open TensorPolynomial SphericalAtomSmoothCutoffApproximation SphericalSmoothTensorStationarity
open scoped BigOperators NNReal RealInnerProductSpace
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem pureMixture_maxDegree (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) :
    (FiniteMixture.pure p hp c hc).maxDegree=p := by
  simp only [FiniteMixture.maxDegree,FiniteMixture.pure,Finsupp.support_single p hc.ne',Finset.max'_singleton]

def pureCorrectionAtom (p : ℕ) (hp : 2 ≤ p) (Q : ℝ) (u G : Vector N)
    (Hq e : ℝ) (i : Bool) : Atom N p :=
  if i then
    twoLinearAtom ((N : ℝ)⁻¹ • u) G (p-1) 1 (by omega) (by omega) (-((Real.sqrt Q)^p)⁻¹)
  else
    twoLinearAtom ((N : ℝ)⁻¹ • u) G p 0 (by simpa using hp) (by simp)
      (((Real.sqrt Q)^p)⁻¹*((N : ℝ)*e-Hq))

theorem pureRegressionCorrection_atom_sum (p : ℕ) (hp : 2 ≤ p) (Q : ℝ) (u G : Vector N)
    (Hq e : ℝ) (x : Vector N) :
    (∑ i : Bool,(pureCorrectionAtom p hp Q u G Hq e i).value x)=
      pureRegressionCorrection p Q u G Hq e x := by
  have hr : inner ℝ ((N : ℝ)⁻¹ • u) x=overlap x u := by
    have hc : inner ℝ u x=inner ℝ x u := real_inner_comm _ _
    rw [real_inner_smul_left,hc]
    exact (div_eq_inv_mul _ _).symm
  simp only [Fintype.sum_bool,pureCorrectionAtom,ite_true,Bool.coe_false,ite_false,
    twoLinearAtom_value,hr,pow_one,pow_zero,mul_one,pureRegressionCorrection]
  ring

def pureSourceCorrectionAtom (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) (e : ℝ) : Bool→Atom N p :=
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  pureCorrectionAtom p hp Q u (surfaceGradient (field cQ J) u) (field cQ J u) e

theorem pureSourceRegressionCorrection_atom_sum (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree) (u : Vector N) (e : ℝ) (x : Vector N) :
    (∑ i : Bool,(pureSourceCorrectionAtom p hp c hc Q J u e i).value x)=
      pureSourceRegressionCorrection p hp c hc Q J u e x :=
  pureRegressionCorrection_atom_sum p hp Q u _ _ e x

/-- The actual proper pure smooth source Hamiltonian, retaining the
original disorder, observed value and actual tangent gradient. -/
def pureSourceSmoothCutoffField (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (χ : ℝ→ℝ) (x : Vector N) : ℝ :=
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let G := surfaceGradient (field cQ J) u
  fieldOfMixture μ J x+χ (overlap x u/α)*χ (inner ℝ G x/((N : ℝ)*α))*
    pureSourceRegressionCorrection p hp c hc Q J u e x

theorem pureSourceSmoothCutoffField_eq_atom (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (χ : ℝ→ℝ) :
    let μ := FiniteMixture.pure p hp c hc
    let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
    pureSourceSmoothCutoffField p hp c hc Q J u e α χ=
      atomSmoothCutoffField μ J (pureSourceCorrectionAtom p hp c hc Q J u e)
        (((N : ℝ)*α)⁻¹ • u) (((N : ℝ)*α)⁻¹ • G) χ := by
  dsimp only
  funext x
  let μ := FiniteMixture.pure p hp c hc
  let G := surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u
  have hr : inner ℝ (((N : ℝ)*α)⁻¹ • u) x=overlap x u/α := by
    have hc' : inner ℝ u x=inner ℝ x u := real_inner_comm _ _
    rw [real_inner_smul_left,hc']
    unfold overlap
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hs : inner ℝ (((N : ℝ)*α)⁻¹ • G) x=inner ℝ G x/((N : ℝ)*α) := by
    rw [real_inner_smul_left]
    exact (div_eq_inv_mul _ _).symm
  unfold atomSmoothCutoffField EntranceSmoothCutoffCalculus.cutoffCorrection atomCorrection
  rw [pureSourceRegressionCorrection_atom_sum,hr,hs]
  rfl

theorem pureSourceSmoothCutoffField_contDiff (hN : 1 ≤ N) (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) := by
  rw [pureSourceSmoothCutoffField_eq_atom]
  exact atomSmoothCutoffField_contDiff hN hp _ J _ _ _ χ hχ

theorem pureSourceSmoothCutoffField_gibbs_invariant (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (u : Vector N) (e α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (t : ℝ≥0) :
    smoothTransitionKernel (pureSourceSmoothCutoffField p hp c hc Q J u e α χ)
      (pureSourceSmoothCutoffField_contDiff hN p hp c hc Q J u e α χ hχ) β t ∘ₘ
      gibbsLaw N β (pureSourceSmoothCutoffField p hp c hc Q J u e α χ)=
        gibbsLaw N β (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) := by
  have H := atomSmoothCutoffField_gibbs_invariant hN hp _ J
    (pureMixture_maxDegree p hp c hc).le (pureSourceCorrectionAtom p hp c hc Q J u e)
    (((N : ℝ)*α)⁻¹ • u)
    (((N : ℝ)*α)⁻¹ • surfaceGradient
      (field (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) J) u)
    χ hχ β t
  simpa only [← pureSourceSmoothCutoffField_eq_atom p hp c hc Q J u e α χ] using H

/-- With unit cutoff, the source Hamiltonian is exactly the original
field of the genuine proper scalar-value posterior, for every Gaussian seed. -/
theorem pureSourceSmoothCutoffField_one_eq_actual_posterior (n : ℕ)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) (e α : ℝ)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree) (x : Vector (n+1)) :
    pureSourceSmoothCutoffField p hp c hc Q (unpackDisorder g) u e α (fun _ => 1) x=
      fieldOfMixture (FiniteMixture.pure p hp c hc)
        (unpackDisorder
          (SphericalPosteriorMaps.valuePosterior n (FiniteMixture.pure p hp c hc) Q u e g)) x := by
  rw [SphericalCriticalLatitude.actual_purePosterior_original_field n p hp c hc hQ u hu]
  simp only [pureSourceSmoothCutoffField,one_mul]

end SlowEquilibration.ConditionedEntrance
