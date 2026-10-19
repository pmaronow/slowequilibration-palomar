-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairObservationTargets
public import SlowEquilibration.PureConditionedHessian

/-! Every physical pair target has literal support under the actual
full-coefficient posterior, including the proper pure radial relation. -/
@[expose] public section
namespace SlowEquilibration.PairObservationTargets
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity PureConditionedHessian
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma sqrt_normalized_eq_physical {N : ℕ} (hN : 0 < N) {z h : ℝ}
    (hz : (Real.sqrt (N:ℝ))⁻¹*z=Real.sqrt (N:ℝ)*h) : z=(N:ℝ)*h := by
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have hd : z/Real.sqrt (N:ℝ)=Real.sqrt (N:ℝ)*h := by simpa only [div_eq_mul_inv,mul_comm] using hz
  have he:=(div_eq_iff hs).mp hd
  calc
    z=(Real.sqrt (N:ℝ)*h)*Real.sqrt (N:ℝ) := he
    _=Real.sqrt (N:ℝ)^2*h := by ring
    _=(N:ℝ)*h := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

theorem mixed_pair_first_scores_ae {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (x y : Vector N) (e f : Fin m → Vector N)
    (hA : Surjective (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f)))
    (h1 k1 h2 k2 : ℝ) :
    ∀ᵐ J ∂coefficientKernel (pairHilbert (singleMixedObservation c x e) (singleMixedObservation c y f))
      (mixedPairTarget N m h1 k1 h2 k2),
      jet c 0 x (fun i => Fin.elim0 i) J=(N:ℝ)*h1 ∧
      jet c 1 x (fun _ => x) J=(N:ℝ)*k1 := by
  filter_upwards [coefficientKernel_observation_ae _ hA (mixedPairTarget N m h1 k1 h2 k2)] with J hJ
  have hh:=congrArg (fun w => w.fst.fst (0:Fin 2)) hJ
  have hk:=congrArg (fun w => w.fst.fst (1:Fin 2)) hJ
  change (Real.sqrt (N:ℝ))⁻¹*scoreCLM c x (euclideanDisorder J) 0=Real.sqrt (N:ℝ)*h1 at hh
  change (Real.sqrt (N:ℝ))⁻¹*scoreCLM c x (euclideanDisorder J) 1=Real.sqrt (N:ℝ)*k1 at hk
  rw [scoreCLM_apply_zero,unpack_euclideanDisorder] at hh
  rw [scoreCLM_apply_one,unpack_euclideanDisorder] at hk
  exact ⟨sqrt_normalized_eq_physical hN hh,sqrt_normalized_eq_physical hN hk⟩

theorem value_pair_first_value_ae {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (x y : Vector N) (e f : Fin m → Vector N)
    (hA : Surjective (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f)))
    (h1 h2 : ℝ) :
    ∀ᵐ J ∂coefficientKernel (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))
      (valuePairTarget N m h1 h2),jet c 0 x (fun i => Fin.elim0 i) J=(N:ℝ)*h1 := by
  filter_upwards [coefficientKernel_observation_ae _ hA (valuePairTarget N m h1 h2)] with J hJ
  have hh:=congrArg (fun w => w.fst.fst) hJ
  change (Real.sqrt (N:ℝ))⁻¹*flatJetCLM c 0 x (fun i => Fin.elim0 i) (euclideanDisorder J)=Real.sqrt (N:ℝ)*h1 at hh
  rw [flatJetCLM_apply,unpack_euclideanDisorder] at hh
  exact sqrt_normalized_eq_physical hN hh

/-- Proper pure conditioning recovers the exact K=pH relation without
conditioning on an impossible separate radial coordinate. -/
theorem pure_pair_first_radial_ae {N m : ℕ} (hN : 0 < N) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q : ℝ) (x y : Vector N) (e f : Fin m → Vector N)
    (h1 h2 : ℝ)
    (hA : Surjective (pairHilbert
      (singleValueObservation (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q) x e)
      (singleValueObservation (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q) y f))) :
    let c:=centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
    ∀ᵐ J ∂coefficientKernel (pairHilbert (singleValueObservation c x e) (singleValueObservation c y f))
      (valuePairTarget N m h1 h2),jet c 1 x (fun _ => x) J=(N:ℝ)*((p:ℝ)*h1) := by
  dsimp only
  filter_upwards [value_pair_first_value_ae hN _ x y e f hA h1 h2] with J hJ
  rw [pure_radial_jet p hp alpha halpha Q J x,hJ]
  ring

end
end SlowEquilibration.PairObservationTargets
