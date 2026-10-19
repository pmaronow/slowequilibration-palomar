-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceCutoffEnergyBound
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceGradient

/-! Sharp alpha-to-minimum-degree energy difference for the actual source
cutoff Hamiltonian on the original ordered-tensor regularity event. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging HardSphereDynamics
open Set
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {N : ℕ}

def physicalCutoffEnergyConstant (μ : FiniteMixture) (Q h k B R : ℝ) : ℝ :=
  cutoffEnergyConstant μ Q (markConstant μ Q h k) B R

theorem physicalCutoffEnergyConstant_nonneg (μ : FiniteMixture) (Q h k B R : ℝ)
    (hR : 0 ≤ R) : 0 ≤ physicalCutoffEnergyConstant μ Q h k B R :=
  cutoffEnergyConstant_nonneg μ Q _ B R (markConstant_nonneg μ Q h k) hR

theorem regular_source_cutoff_energy_difference (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) (x : Vector N) (hx : OnSphere x)
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s,|D.cutoff s| ≤ B) (hχR : ∀ s,R < |s| → D.cutoff s=0) :
    |D.hamiltonian x-fieldOfMixture D.mixture D.disorder x| ≤
      physicalCutoffEnergyConstant D.mixture D.Q D.energyMark D.radialMark B R*
        (N : ℝ)*D.cutoffScale^D.mixture.minDegree := by
  let μ := D.mixture
  let c := centerCoefficients (mixtureCoefficients μ) D.Q
  let G := surfaceGradient (field c D.disorder) D.axis
  let Hq := field c D.disorder D.axis
  let Kq := jet c 1 D.axis (fun _ => D.axis) D.disorder
  let M := markConstant μ D.Q D.energyMark D.radialMark
  let K := centerConstant μ D.Q
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by have := D.dimension_ge_one;omega)
  have hK : 0 ≤ K := (centerConstant_pos μ D.Q).le
  have hM : 0 ≤ M := markConstant_nonneg μ D.Q D.energyMark D.radialMark
  obtain ⟨hH,hRad,_hG⟩ := regular_center_observations D hJ
  change |Hq| ≤ K*(N : ℝ) at hH
  change |Kq| ≤ K*(N : ℝ) at hRad
  have he : |(N : ℝ)*D.energyMark-Hq| ≤ M*(N : ℝ) := by
    calc
      _ ≤ |(N : ℝ)*D.energyMark|+|Hq| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((N : ℝ)*D.energyMark) 0 Hq
      _ ≤ (N : ℝ)*|D.energyMark|+K*(N : ℝ) := by
        rw [abs_mul,abs_of_pos hNr]
        exact add_le_add le_rfl hH
      _ ≤ _ := by dsimp [M,markConstant,K];nlinarith [abs_nonneg D.radialMark]
  have hk : |(N : ℝ)*D.radialMark-Kq| ≤ M*(N : ℝ) := by
    calc
      _ ≤ |(N : ℝ)*D.radialMark|+|Kq| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((N : ℝ)*D.radialMark) 0 Kq
      _ ≤ (N : ℝ)*|D.radialMark|+K*(N : ℝ) := by
        rw [abs_mul,abs_of_pos hNr]
        exact add_le_add le_rfl hRad
      _ ≤ _ := by dsimp [M,markConstant,K];nlinarith [abs_nonneg D.energyMark]
  have hr : |overlap x D.axis| ≤ 1 := by
    have hxnorm := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
    have hunorm := LandscapeDerivatives.sphere_norm D.axis
      ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere)
    rw [overlap,abs_div,abs_of_pos hNr]
    apply (div_le_one hNr).mpr
    calc
      _ ≤ ‖x‖*‖D.axis‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [hxnorm,hunorm,Real.mul_self_sqrt (Nat.cast_nonneg N)]
  have H := cutoff_regression_energy_bound μ D.Q (N : ℝ) M R D.cutoffScale
    (overlap x D.axis) (inner ℝ G x) ((N : ℝ)*D.energyMark-Hq)
    ((N : ℝ)*D.radialMark-Kq) hNr hM hR D.cutoffScale_pos hr he hk
    D.cutoff hB hχB hχR
  rw [SmoothKilled.SourceData.hamiltonian,sourceSmoothCutoffField_eq]
  rw [add_sub_cancel_left]
  exact H

def uniformCutoffEnergyConstant (μ : FiniteMixture) (Q hbar kbar B R : ℝ) : ℝ :=
  cutoffEnergyConstant μ Q (hbar+kbar+3*centerConstant μ Q) B R

theorem physicalCutoffEnergyConstant_le_uniform (μ : FiniteMixture)
    (Q h k hbar kbar B R : ℝ) (hR : 0 ≤ R)
    (hh : |h| ≤ hbar) (hk : |k| ≤ kbar) :
    physicalCutoffEnergyConstant μ Q h k B R ≤
      uniformCutoffEnergyConstant μ Q hbar kbar B R := by
  have hcoef : 0 ≤ B^2*regressionOrderConstant μ Q*R^μ.minDegree := by
    have hc := (regressionOrderConstant_pos μ Q).le
    positivity
  have hM : markConstant μ Q h k+1 ≤ hbar+kbar+3*centerConstant μ Q+1 := by
    unfold markConstant
    linarith
  have H := mul_le_mul_of_nonneg_left hM hcoef
  unfold physicalCutoffEnergyConstant uniformCutoffEnergyConstant cutoffEnergyConstant
  nlinarith only [H]

theorem regular_source_cutoff_energy_difference_uniform_marks (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) (x : Vector N) (hx : OnSphere x)
    {hbar kbar B R : ℝ} (hh : |D.energyMark| ≤ hbar) (hk : |D.radialMark| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s,|D.cutoff s| ≤ B) (hχR : ∀ s,R < |s| → D.cutoff s=0) :
    |D.hamiltonian x-fieldOfMixture D.mixture D.disorder x| ≤
      uniformCutoffEnergyConstant D.mixture D.Q hbar kbar B R*
        (N : ℝ)*D.cutoffScale^D.mixture.minDegree := by
  have H := regular_source_cutoff_energy_difference D hJ x hx hB hR hχB hχR
  have HC := physicalCutoffEnergyConstant_le_uniform D.mixture D.Q D.energyMark
    D.radialMark hbar kbar B R hR hh hk
  exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (Nat.cast_nonneg N)) (pow_nonneg D.cutoffScale_pos.le _))

theorem regular_source_cutoff_weight_uniform_bound (D : SmoothKilled.SourceData N)
    (hJ : D.disorder ∈ regularDisorder) (x : Vector N) (hx : OnSphere x)
    {β hbar kbar B R : ℝ} (hβ : 0 ≤ β)
    (hh : |D.energyMark| ≤ hbar) (hk : |D.radialMark| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s,|D.cutoff s| ≤ B) (hχR : ∀ s,R < |s| → D.cutoff s=0) :
    Real.exp (β*(D.hamiltonian x-fieldOfMixture D.mixture D.disorder x)) ≤
      Real.exp (β*uniformCutoffEnergyConstant D.mixture D.Q hbar kbar B R*
        (N : ℝ)*D.cutoffScale^D.mixture.minDegree) := by
  have H := (le_abs_self (D.hamiltonian x-fieldOfMixture D.mixture D.disorder x)).trans
    (regular_source_cutoff_energy_difference_uniform_marks D hJ x hx hh hk hB hR hχB hχR)
  exact Real.exp_le_exp.mpr (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H hβ)

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
