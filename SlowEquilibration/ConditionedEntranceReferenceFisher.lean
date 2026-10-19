-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceReferenceResolvent
public import SlowEquilibration.SphericalResolventFisher
public import SlowEquilibration.SphericalUniformStartEntropy

/-! The source reference resolvent and its actual Fisher estimate for the
literal original uniform sphere start. No resolvent/test/entropy premise. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def referenceInitialVector (D : SourceData N) (β : ℝ) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    (fun x => 1+uniformInitialDensity N β D.hamiltonian x)
    (continuous_const.add (uniformInitialDensity_continuous β D.hamiltonian D.hamiltonian_contDiff.continuous))

theorem referenceInitialVector_ae (D : SourceData N) (β : ℝ) :
    referenceInitialVector D β=ᵐ[gibbsLaw N β D.hamiltonian]
      fun x => 1+uniformInitialDensity N β D.hamiltonian x :=
  gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    _ (continuous_const.add (uniformInitialDensity_continuous β D.hamiltonian D.hamiltonian_contDiff.continuous))

theorem referenceInitialVector_bounds (D : SourceData N) (β : ℝ) (hβ : 0 ≤ β)
    (B : ℝ) (hB : ∀ x,OnSphere x → |D.hamiltonian x| ≤ B) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
      1 ≤ referenceInitialVector D β x ∧ referenceInitialVector D β x ≤ 1+Real.exp (2*β*B) := by
  filter_upwards [referenceInitialVector_ae D β,gibbsLaw_support D.dimension_ge_one β D.hamiltonian]
    with x hx hs
  rw [hx]
  have hp := uniformInitialDensity_pos D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous x
  have hb := uniformInitialDensity_le D.dimension_ge_one β hβ D.hamiltonian
    D.hamiltonian_contDiff.continuous B hB x ((onSphere_iff_norm_sq x).mpr hs)
  constructor <;> linarith

theorem referenceInitialVector_mass (D : SourceData N) (β : ℝ) :
    (∫ x,referenceInitialVector D β x ∂gibbsLaw N β D.hamiltonian)=2 := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  rw [integral_congr_ae (referenceInitialVector_ae D β)]
  rw [integral_add (integrable_const (1 : ℝ))
    (integrable_gibbs_of_continuous D.dimension_ge_one β D.hamiltonian_contDiff.continuous
      (uniformInitialDensity_continuous β D.hamiltonian D.hamiltonian_contDiff.continuous))]
  simp only [integral_const,probReal_univ,one_smul,
    uniformInitialDensity_integral D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous]
  norm_num

theorem referenceInitialVector_entropy_integrable (D : SourceData N) (β : ℝ) :
    Integrable (fun x => referenceInitialVector D β x*Real.log (referenceInitialVector D β x))
      (gibbsLaw N β D.hamiltonian) := by
  let F := fun x => 1+uniformInitialDensity N β D.hamiltonian x
  have hF : Continuous F := continuous_const.add
    (uniformInitialDensity_continuous β D.hamiltonian D.hamiltonian_contDiff.continuous)
  have hFp (x : Vector N) : 0 < F x := by
    dsimp [F]
    linarith [uniformInitialDensity_pos D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous x]
  apply (integrable_gibbs_of_continuous D.dimension_ge_one β D.hamiltonian_contDiff.continuous
    (hF.mul (hF.log (fun x => (hFp x).ne')))).congr
  exact (referenceInitialVector_ae D β).symm.mono (fun _ hx => congrArg (fun r : ℝ => r*Real.log r) hx)

theorem referenceInitialVector_entropy_le (D : SourceData N) (β : ℝ) (hβ : 0 ≤ β)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x,OnSphere x → |D.hamiltonian x| ≤ B) :
    (∫ x,referenceInitialVector D β x*Real.log (referenceInitialVector D β x)
      ∂gibbsLaw N β D.hamiltonian) ≤ 2*Real.log 2+4*β*B := by
  have he : (∫ x,referenceInitialVector D β x*Real.log (referenceInitialVector D β x)
      ∂gibbsLaw N β D.hamiltonian)=
      ∫ x,(1+uniformInitialDensity N β D.hamiltonian x)*Real.log (1+uniformInitialDensity N β D.hamiltonian x)
        ∂gibbsLaw N β D.hamiltonian :=
    integral_congr_ae ((referenceInitialVector_ae D β).mono (fun _ hx => congrArg (fun r : ℝ => r*Real.log r) hx))
  rw [he]
  exact uniformInitialDensity_entropy_le D.dimension_ge_one β hβ D.hamiltonian
    D.hamiltonian_contDiff.continuous B hB0 hB

/-- The actual physical reference resolvent at any positive source rate
has the completed spherical Fisher bound with only linear initial entropy.
The original uniform initial density, conservativeness and log test are
all constructed from the actual sphere and its actual generator. -/
theorem referenceRate_initial_fisher_bound (D : SourceData N) (β : ℝ) (hβ : 0 ≤ β)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x,OnSphere x → |D.hamiltonian x| ≤ B)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=
        referenceRate D β θ (referenceInitialVector D β) ∧
      0 ≤ sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u ∧
      sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u ≤
        (θ : ℝ)*(2*Real.log 2+4*β*B) := by
  let F₀ := referenceInitialVector D β
  let F := referenceRate D β θ F₀
  have hbound := referenceRate_bounds D β θ hθ F₀ 1 (1+Real.exp (2*β*B))
    (referenceInitialVector_bounds D β hβ B hB)
  obtain ⟨hd,hgen⟩ := referenceRate_generator D β θ hθ F₀
  obtain ⟨u,hu,hJ⟩ := sphericalGenerator_fisher_bound D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous ⟨F,hd⟩ F₀ (θ : ℝ) (1+Real.exp (2*β*B)) θ.coe_nonneg
    (by linarith [Real.exp_pos (2*β*B)]) ((referenceInitialVector_bounds D β hβ B hB).mono (fun _ hx => by linarith [hx.1]))
    hbound (referenceInitialVector_entropy_integrable D β) (referenceRate_mass D β θ hθ F₀).symm hgen
  refine ⟨u,hu,?_,?_⟩
  · apply sphericalFisher_nonnegative
    have hup : u.val.fst=F := hu
    rw [hup]
    exact hbound.mono (fun _ hx => hx.1)
  · exact hJ.trans (mul_le_mul_of_nonneg_left
      (referenceInitialVector_entropy_le D β hβ B hB0 hB) θ.coe_nonneg)

end SlowEquilibration.ConditionedEntrance.SmoothKilled
