-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxGlobalDensityEnvelope
public import SlowEquilibration.ExpectedTailAbsoluteEnvelope

/-! The actual truncated proper-pure local-maximum count intensity has a
global upper-tail envelope in physical energy. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 400000

theorem sourcePure_truncatedLocalMax_tail_global_upper
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ} (hlr : l < r) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) H ≤
      C/(β*x)*Real.exp (-(β*x)*(H-(n+2 : ℕ)*E))/Real.sqrt (n+2 : ℕ) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  obtain ⟨C,hC,hGlobal⟩ := sourcePure_truncatedLocalMax_global_upper
    p hp a ha h hg hLeft hRight
  refine ⟨C,hC,?_⟩
  filter_upwards [hGlobal,
    pureTruncatedLocalMaxDensity_integrable_eventually
      p hp a ha h hlr hg hLeft hRight] with n hn hi
  intro H
  let A : ℝ := C*Real.exp (-(β*x)*(H-(n+2 : ℕ)*E))/Real.sqrt (n+2 : ℕ)
  have henv : ∀ v : ℝ, 0 ≤ v → f n (H+v) ≤ A*Real.exp (-(β*x)*v) := by
    intro v _
    calc
      f n (H+v) ≤
          C*Real.exp (-(β*x)*((H+v)-(n+2 : ℕ)*E))/Real.sqrt (n+2 : ℕ) := hn _
      _ = A*Real.exp (-(β*x)*v) := by
        rw [show -(β*x)*((H+v)-(n+2 : ℕ)*E) =
          -(β*x)*(H-(n+2 : ℕ)*E)+(-(β*x)*v) by ring,Real.exp_add]
        dsimp [A]
        ring
  have ht := tail_upper_of_absolute_exponential_envelope hi hc henv
  change tail (f n) H ≤ A/(β*x) at ht
  dsimp [A] at ht
  convert ht using 1
  ring

end SlowEquilibration.SphericalMarkedWindows
