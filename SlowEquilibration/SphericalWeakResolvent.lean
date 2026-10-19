module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalSobolev
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# The actual spherical Gibbs closed form and weak resolvent

The form is defined on the proved injective smooth-gradient graph closure.
The resolvent is constructed by the Hilbert adjoint of its actual L²
inclusion. Compactness is a separate theorem still to be supplied from the
actual spherical Rellich embedding; it is not assumed in these definitions.
-/

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology ContDiff

/-- A genuine smooth function in the actual energy completion. -/
def smoothEnergyToGraph {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : smoothCore N →ₗ[ℝ] sphericalSobolevGraph hN β H hH :=
  (smoothGradientGraphLinear hN β H hH).codRestrict _ (fun f =>
    Submodule.le_topologicalClosure (LinearMap.range (smoothGradientGraphLinear hN β H hH))
      ⟨f, rfl⟩)

/-- Inclusion of the actual energy completion into actual spherical Gibbs L². -/
def sphericalEnergyL2Map {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : sphericalSobolevGraph hN β H hH →L[ℝ] Lp ℝ 2 (gibbsLaw N β H) :=
  (WithLp.fstL 2 ℝ _ _).comp (sphericalSobolevGraph hN β H hH).subtypeL

/-- The completed actual normalized rotation gradient. -/
def sphericalEnergyGradientMap {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : sphericalSobolevGraph hN β H hH →L[ℝ]
      PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) :=
  (WithLp.sndL 2 ℝ _ _).comp (sphericalSobolevGraph hN β H hH).subtypeL

theorem sphericalEnergyL2Map_apply_norm_le {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u : sphericalSobolevGraph hN β H hH) :
    ‖sphericalEnergyL2Map hN β H hH u‖ ≤ ‖u‖ := WithLp.norm_fst_le _ u.val

theorem sphericalEnergyL2Map_norm_le {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : ‖sphericalEnergyL2Map hN β H hH‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using sphericalEnergyL2Map_apply_norm_le hN β H hH u

theorem sphericalEnergyL2Map_injective {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) :
    Function.Injective (sphericalEnergyL2Map hN β H hH.continuous) :=
  sphericalSobolevGraph_injective hN β H hH

theorem sphericalEnergyL2Map_dense {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : DenseRange (sphericalEnergyL2Map hN β H hH) := by
  apply (gibbsToL2_smooth_dense hN β H hH).mono
  rintro u ⟨f, rfl⟩
  exact ⟨smoothEnergyToGraph hN β H hH ⟨f.val, f.property⟩, rfl⟩

/-- The actual closed Dirichlet pairing in the actual energy completion. -/
def sphericalCompletedDirichlet {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u v : sphericalSobolevGraph hN β H hH) : ℝ :=
  inner ℝ (sphericalEnergyGradientMap hN β H hH u) (sphericalEnergyGradientMap hN β H hH v)

theorem sphericalCompletedDirichlet_add_L2 {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u v : sphericalSobolevGraph hN β H hH) :
    sphericalCompletedDirichlet hN β H hH u v +
      inner ℝ (sphericalEnergyL2Map hN β H hH u) (sphericalEnergyL2Map hN β H hH v) =
      inner ℝ u v := by
  change inner ℝ u.val.snd v.val.snd + inner ℝ u.val.fst v.val.fst = inner ℝ u.val v.val
  rw [WithLp.prod_inner_apply]
  exact add_comm _ _

theorem sphericalCompletedDirichlet_nonneg {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u : sphericalSobolevGraph hN β H hH) :
    0 ≤ sphericalCompletedDirichlet hN β H hH u u := by
  rw [sphericalCompletedDirichlet, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem sphericalCompletedDirichlet_smooth_energy {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : smoothCore N) :
    sphericalCompletedDirichlet hN β H hH
      (smoothEnergyToGraph hN β H hH f) (smoothEnergyToGraph hN β H hH f) =
      dirichletEnergy N β H f := by
  change inner ℝ (normalizedRotationGradientL2 hN β H hH f ((smoothCore_contDiff f).of_le (by simp)))
    (normalizedRotationGradientL2 hN β H hH f ((smoothCore_contDiff f).of_le (by simp))) = _
  rw [real_inner_self_eq_norm_sq, dirichletEnergy_eq_normalizedRotationGradientL2_norm]

/-- The actual weak solution operator for the actual closed form `E+L²`. -/
def sphericalWeakSolution {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    Lp ℝ 2 (gibbsLaw N β H) →L[ℝ] sphericalSobolevGraph hN β H hH :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := sphericalSobolevGraph hN β H hH)
      (F := Lp ℝ 2 (gibbsLaw N β H)) (sphericalEnergyL2Map hN β H hH)

set_option maxHeartbeats 500000 in
theorem sphericalWeakSolution_spec {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H))
    (v : sphericalSobolevGraph hN β H hH) :
    sphericalCompletedDirichlet hN β H hH (sphericalWeakSolution hN β H hH f) v +
      inner ℝ (sphericalEnergyL2Map hN β H hH (sphericalWeakSolution hN β H hH f))
        (sphericalEnergyL2Map hN β H hH v) =
      inner ℝ f (sphericalEnergyL2Map hN β H hH v) := by
  have h := ContinuousLinearMap.adjoint_inner_left (𝕜 := ℝ) (E := sphericalSobolevGraph hN β H hH)
    (F := Lp ℝ 2 (gibbsLaw N β H)) (sphericalEnergyL2Map hN β H hH) v f
  exact (sphericalCompletedDirichlet_add_L2 hN β H hH
    (sphericalWeakSolution hN β H hH f) v).trans h

theorem sphericalWeakSolution_unique {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H))
    (u : sphericalSobolevGraph hN β H hH)
    (hu : ∀ v, sphericalCompletedDirichlet hN β H hH u v +
      inner ℝ (sphericalEnergyL2Map hN β H hH u) (sphericalEnergyL2Map hN β H hH v) =
        inner ℝ f (sphericalEnergyL2Map hN β H hH v)) :
    u = sphericalWeakSolution hN β H hH f := by
  apply ext_inner_right ℝ
  intro v
  rw [← sphericalCompletedDirichlet_add_L2 hN β H hH u v,
    ← sphericalCompletedDirichlet_add_L2 hN β H hH (sphericalWeakSolution hN β H hH f) v]
  exact (hu v).trans (sphericalWeakSolution_spec hN β H hH f v).symm

theorem sphericalWeakSolution_eq_zero_iff {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    sphericalWeakSolution hN β H hH f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact (sphericalEnergyL2Map_dense hN β H hH).induction_on
      (p := fun v => inner ℝ f v = 0) f
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      (fun u => by
        rw [← ContinuousLinearMap.adjoint_inner_left (𝕜 := ℝ) (E := sphericalSobolevGraph hN β H hH)
      (F := Lp ℝ 2 (gibbsLaw N β H)) (sphericalEnergyL2Map hN β H hH) u f]
        change inner ℝ (sphericalWeakSolution hN β H hH f) u = 0
        rw [hf, inner_zero_left])
  · rintro rfl
    exact map_zero _

/-- The actual L² weak resolvent `(1+A)⁻¹`, constructed by Riesz duality
for the actual completed gradient form. -/
def sphericalL2Resolvent {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    Lp ℝ 2 (gibbsLaw N β H) →L[ℝ] Lp ℝ 2 (gibbsLaw N β H) :=
  (sphericalEnergyL2Map hN β H hH).comp (sphericalWeakSolution hN β H hH)

theorem sphericalL2Resolvent_inner {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f g : Lp ℝ 2 (gibbsLaw N β H)) :
    inner ℝ (sphericalL2Resolvent hN β H hH f) g =
      inner ℝ (sphericalWeakSolution hN β H hH f) (sphericalWeakSolution hN β H hH g) :=
  (ContinuousLinearMap.adjoint_inner_right (𝕜 := ℝ) (E := sphericalSobolevGraph hN β H hH)
      (F := Lp ℝ 2 (gibbsLaw N β H)) (sphericalEnergyL2Map hN β H hH)
    (sphericalWeakSolution hN β H hH f) g).symm

theorem sphericalL2Resolvent_symmetric {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : (sphericalL2Resolvent hN β H hH).IsSymmetric := by
  intro f g
  change inner ℝ (sphericalL2Resolvent hN β H hH f) g = inner ℝ f (sphericalL2Resolvent hN β H hH g)
  calc
    _ = inner ℝ (sphericalWeakSolution hN β H hH f)
      (sphericalWeakSolution hN β H hH g) := sphericalL2Resolvent_inner hN β H hH f g
    _ = inner ℝ (sphericalWeakSolution hN β H hH g)
      (sphericalWeakSolution hN β H hH f) := real_inner_comm _ _
    _ = inner ℝ (sphericalL2Resolvent hN β H hH g) f :=
      (sphericalL2Resolvent_inner hN β H hH g f).symm
    _ = _ := real_inner_comm _ _

theorem sphericalL2Resolvent_positive {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H)) (hf : f ≠ 0) :
    0 < inner ℝ (sphericalL2Resolvent hN β H hH f) f := by
  rw [sphericalL2Resolvent_inner, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h => hf ((sphericalWeakSolution_eq_zero_iff hN β H hH f).mp h)))

theorem sphericalL2Resolvent_injective {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : Function.Injective (sphericalL2Resolvent hN β H hH) := by
  apply (ContinuousLinearMap.self_comp_adjoint_injective_iff (𝕜 := ℝ)
      (E := sphericalSobolevGraph hN β H hH) (F := Lp ℝ 2 (gibbsLaw N β H))
    (sphericalEnergyL2Map hN β H hH)).mpr
  apply (LinearMap.ker_eq_bot).mp
  ext f
  exact sphericalWeakSolution_eq_zero_iff hN β H hH f

theorem sphericalL2Resolvent_norm_le {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : ‖sphericalL2Resolvent hN β H hH‖ ≤ 1 := by
  have ha : ‖sphericalWeakSolution hN β H hH‖ = ‖sphericalEnergyL2Map hN β H hH‖ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := sphericalSobolevGraph hN β H hH)
      (F := Lp ℝ 2 (gibbsLaw N β H))).norm_map (sphericalEnergyL2Map hN β H hH)
  have hh := ContinuousLinearMap.opNorm_comp_le (sphericalEnergyL2Map hN β H hH)
    (sphericalWeakSolution hN β H hH)
  rw [ha] at hh
  apply hh.trans
  nlinarith [sphericalEnergyL2Map_norm_le hN β H hH, norm_nonneg (sphericalEnergyL2Map hN β H hH)]

end
end SlowEquilibration.SphericalForm
