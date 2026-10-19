-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCenteredGlobalMaximumTail
public import SlowEquilibration.SourcePureRetainedCountProbability
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The proper-pure global maximum and literal retained count use the
same original disorder field. This file provides their deterministic
lower-tail implication and the dimension-shifted upper tail. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet SphericalForm
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 650000

theorem sourcePure_retained_centered_window_zero_of_max_below
    (n : ℕ) (μ : FiniteMixture) (Q E δ L : ℝ) (m : ℕ → ℝ)
    (κ C ε η G : ℝ) (J : Disorder (n+3) μ.maxDegree)
    (hmax : sourceSphereMaximum (n+1) μ Q J < m (n+1)-L) :
    sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
      κ C ε η E G J = 0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨y,hy,_hcrit,hupper,heq⟩ := sourceSphereMaximum_attained (n+1) μ Q J
  have hempty :
      {u : Vector (n+3) | ‖u‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field c J) u=0 ∧
        actualValue c J u ∈ sourcePureCenteredNormalizedWindow n m E δ (-L) L} = ∅ := by
    ext u
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨hu,_hcrit,hw⟩
    have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
    have hlow : m (n+1)-L ≤ field c J u := by
      change ((n+3 : ℕ) : ℝ)*actualValue c J u ∈
        Icc (m (n+1)+(-L)) (m (n+1)+L) ∩
          Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)) at hw
      have hval := hw.1.1
      change m (n+1)+(-L) ≤ (n+3 : ℕ)*(field c J u/(n+3 : ℕ)) at hval
      have hfield : ((n+3 : ℕ) : ℝ)*(field c J u/(n+3 : ℕ))=field c J u := by
        field_simp
      rw [hfield] at hval
      simpa only [sub_eq_add_neg] using hval
    have hle : field c J u ≤ sourceSphereMaximum (n+1) μ Q J := by
      rw [heq]
      exact hupper hu
    exact (not_le_of_gt hmax) (hlow.trans hle)
  unfold sourceRetainedValueWindowCount actualValueWindowCount
  change (∑' u : {u : Vector (n+3) | ‖u‖^2=(n+3 : ℕ) ∧
    surfaceGradient (field c J) u=0 ∧
    actualValue c J u ∈ sourcePureCenteredNormalizedWindow n m E δ (-L) L},
    sourceSelectionMark c κ C ε η E G J u) = 0
  rw [hempty]
  exact tsum_empty

theorem sourcePure_centered_global_maximum_limsup_shift
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ,
      Filter.limsup (fun n : ℕ =>
        (disorderLaw (n+3) (FiniteMixture.pure p hp a ha).maxDegree).real
          {J | m (n+1)+L ≤ sourceSphereMaximum (n+1)
            (FiniteMixture.pure p hp a ha) Q J}) atTop ≤
        A*Real.exp (-(β*x)*L) := by
  obtain ⟨A,hA,hUpper⟩ :=
    sourcePure_centered_global_maximum_limsup p hp a ha h m hM hcenter
  refine ⟨A,hA,?_⟩
  intro L
  let f : ℕ → ℝ := fun n =>
    (disorderLaw (n+2) (FiniteMixture.pure p hp a ha).maxDegree).real
      {J | m n+L ≤ sourceSphereMaximum n (FiniteMixture.pure p hp a ha) Q J}
  have heq : Filter.limsup (fun n => f (n+1)) atTop = Filter.limsup f atTop := by
    rw [← Function.comp_def,limsup_comp,map_add_atTop_eq_nat]
  simpa only [f] using (heq.le.trans (hUpper L))

end SlowEquilibration.PairConditionalDeterminantMoments
