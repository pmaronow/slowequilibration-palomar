-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceCutoffSphere
public import SlowEquilibration.EntranceLatitudeSourceRadialSphereMoments
public import SlowEquilibration.EntranceSmallCapAbsorption

/-! Actual smooth source cutoff weighted square moments on the uniform
sphere, with constants and cutoff scale fixed before dimension. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance PairConditionalDeterminantMoments
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sourceCutoffMomentScale (μ : FiniteMixture) (Q M ζ : ℝ) : ℝ :=
  smallCapAbsorptionRadius (sourceLatitudeMomentConstant μ Q M ζ)/2

theorem sourceCutoffMomentScale_pos (μ : FiniteMixture) (Q M ζ : ℝ) :
    0<sourceCutoffMomentScale μ Q M ζ := by
  unfold sourceCutoffMomentScale
  exact div_pos (smallCapAbsorptionRadius_pos (sourceLatitudeMomentConstant_pos μ Q M ζ)) (by norm_num)

def sourceAxisCutoff {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (x u : Vector N) : ℝ :=
  χ (overlap x u/α)*χ (inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) x/((N : ℝ)*α))

theorem sourceAxisCutoff_continuous {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : Continuous χ) (x : Vector N) :
    Continuous (sourceAxisCutoff μ Q J α χ x) := by
  have hG : Continuous (fun u : Vector N => surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) :=
    surfaceGradient_continuous ((field_contDiff (centerCoefficients (mixtureCoefficients μ) Q) J).of_le (by simp))
  exact (hχ.comp (((continuous_const.inner continuous_id).div_const _).div_const α)).mul
    (hχ.comp ((hG.inner continuous_const).div_const _))

theorem sourceAxisCutoff_abs_le_one {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ∀ s,|χ s|≤1) (x u : Vector N) :
    |sourceAxisCutoff μ Q J α χ x u|≤1 := by
  unfold sourceAxisCutoff
  rw [abs_mul]
  exact (mul_le_mul (hχ _) (hχ _) (abs_nonneg _) (by norm_num : (0 : ℝ)≤1)).trans_eq (by norm_num)

theorem sourceAxisCutoff_zero {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) {α : ℝ} (hα : 0<α) (χ : ℝ→ℝ)
    (hχ : ∀ s,2< |s| → χ s=0) (x u : Vector N) (hr : 2*α< |overlap x u|) :
    sourceAxisCutoff μ Q J α χ x u=0 := by
  unfold sourceAxisCutoff
  rw [hχ (overlap x u/α) (by rw [abs_div,abs_of_pos hα];exact (lt_div_iff₀ hα).mpr hr),zero_mul]

/-- Genuine source envelope plus the actual cutoff and true overlap moments
imply the uniform N^(2-d) weighted square rate. The model and scale precede N. -/
theorem source_cutoff_quadratic_moment_eventually_bounded (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q M ζ : ℝ} (hQ : 0≤Q) (hM : 0≤M) (hζ : 0≤ζ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree),J∈originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (α : ℝ),0<α → α≤ sourceCutoffMomentScale μ Q M ζ →
      ∀ (χ : ℝ→ℝ),Continuous χ → (∀ s,|χ s|≤1) → (∀ s,2< |s| → χ s=0) →
      ∀ (F : Vector (n+1)→ℝ),Continuous F →
      (∀ u,‖u‖^2=((n+1 : ℕ) : ℝ) → |F u|≤ sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|overlap x u|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|)) →
      Integrable (fun u => (sourceAxisCutoff μ Q J α χ x u*F u)^2*
        Real.exp (ζ*|sourceAxisCutoff μ Q J α χ x u*F u|)) (sphereLaw (n+1)) ∧
      (∫ u,(sourceAxisCutoff μ Q J α χ x u*F u)^2*
        Real.exp (ζ*|sourceAxisCutoff μ Q J α χ x u*F u|) ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  obtain ⟨C,hC,hMom⟩ := sourceLatitudeQuadraticPower_sphere_eventually_bounded μ
  refine ⟨sourceLatitudeQuadraticConstant μ Q M ζ*C,
    mul_pos (sourceLatitudeQuadraticConstant_pos μ Q M ζ) hC,?_⟩
  filter_upwards [hMom,eventually_ge_atTop 2] with n hMom hn
  intro J hJ x hx α hα hαsmall χ hχ hχb hχ0 F hF hFb
  let ρ := smallCapAbsorptionRadius (sourceLatitudeMomentConstant μ Q M ζ)
  have h := source_cutoff_sphere_square_exp_abs_le (ρ := ρ) hn μ hQ hM hζ J hJ x hx F
    (fun u => sourceAxisCutoff μ Q J α χ x u*F u) hF
    ((sourceAxisCutoff_continuous μ Q J α χ hχ x).mul hF) hFb ?_ ?_ ?_
  · refine ⟨h.1,?_⟩
    apply h.2.trans
    have hh := mul_le_mul_of_nonneg_left (hMom x hx).2
      (sourceLatitudeQuadraticConstant_pos μ Q M ζ).le
    exact hh.trans_eq (by ring)
  · intro u _hu
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (sourceAxisCutoff_abs_le_one μ Q J α χ hχb x u) (abs_nonneg _)).trans_eq (one_mul _)
  · intro u hu
    rw [sourceAxisCutoff_zero μ Q J hα χ hχ0 x u (by
      have hα2 : 2*α≤ρ := by change α≤ρ/2 at hαsmall;linarith
      exact hα2.trans_lt hu),zero_mul]
  · intro r hr
    exact smallCapAbsorption (sourceLatitudeMomentConstant_pos μ Q M ζ) (n+1) μ.minDegree
      (by omega) hd r hr

end
end SlowEquilibration.EntranceLatitudeTangentObservable
