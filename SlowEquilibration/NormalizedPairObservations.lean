-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairRegression
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Actual two-point observations normalized by sqrt N on the extensive
score coordinates. Their Hilbert product carries the true L² norm. -/

@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped Topology BigOperators RealInnerProductSpace
open SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

abbrev MixedObservationSpace (m : ℕ) :=
  WithLp 2 (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin m))

/-- Actual score/tangent observation, with only the extensive scores divided
by sqrt N; the frame coordinates retain their genuine normalization. -/
def singleMixedObservation {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] MixedObservationSpace m :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin m))).symm.toContinuousLinearMap.comp
    (((Real.sqrt (N:ℝ))⁻¹ • scoreCLM c x).prod (gradientCLM c x e))

@[simp] lemma singleMixedObservation_score {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P) :
    (singleMixedObservation c x e g).fst=(Real.sqrt (N:ℝ))⁻¹ • scoreCLM c x g := rfl

@[simp] lemma singleMixedObservation_gradient {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P) :
    (singleMixedObservation c x e g).snd=gradientCLM c x e g := rfl

/-- Literal vector reconstructed from the actual orthonormal tangent frame. -/
def frameSum {N m : ℕ} (e : Fin m → Vector N) (v : EuclideanSpace ℝ (Fin m)) : Vector N :=
  ∑ i,v i • e i

lemma frameSum_norm {N m : ℕ} (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (v : EuclideanSpace ℝ (Fin m)) : ‖frameSum e v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
  unfold frameSum
  rw [he.inner_sum]
  simp only [conj_trivial,PiLp.inner_apply,RCLike.inner_apply]

lemma frameSum_tangent {N m : ℕ} (x : Vector N) (e : Fin m → Vector N)
    (htan : ∀ i,inner ℝ (e i) x=0) (v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (frameSum e v) x=0 := by
  unfold frameSum
  simp only [sum_inner,real_inner_smul_left,htan,mul_zero,Finset.sum_const_zero]

lemma jet_one_frameSum {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : EuclideanSpace ℝ (Fin m)) (J : Disorder N P) :
    jet c 1 x (fun _ => frameSum e v) J=∑ i,v i*jet c 1 x (fun _ => e i) J := by
  simp only [jet,iteratedFDeriv_one_apply,frameSum,map_sum,map_smul,smul_eq_mul]

/-- A Hilbert dual observation is the literal normalized score combination
and the actual directional derivative in its reconstructed tangent vector. -/
lemma singleMixedObservation_inner_actual {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : MixedObservationSpace m) (J : Disorder N P) :
    inner ℝ v (singleMixedObservation c x e (euclideanDisorder J))=
      (v.fst 0/Real.sqrt (N:ℝ))*jet c 0 x (fun i => Fin.elim0 i) J+
      (v.fst 1/Real.sqrt (N:ℝ))*jet c 1 x (fun _ => x) J+
      jet c 1 x (fun _ => frameSum e v.snd) J := by
  rw [WithLp.prod_inner_apply]
  change inner ℝ v.fst ((Real.sqrt (N:ℝ))⁻¹ • scoreCLM c x (euclideanDisorder J))+
    inner ℝ v.snd (gradientCLM c x e (euclideanDisorder J))=_
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.smul_apply,smul_eq_mul,
    gradientCLM_apply,unpack_euclideanDisorder]
  rw [Fin.sum_univ_two,scoreCLM_apply_zero,scoreCLM_apply_one,
    unpack_euclideanDisorder,jet_one_frameSum]
  simp only [mul_comm]
  ring

/-- Equality of actual scalar coefficient maps, not merely equality a.e. -/
lemma singleMixedObservation_dual {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : MixedObservationSpace m) :
    (innerSL ℝ v).comp (singleMixedObservation c x e)=
      (v.fst 0/Real.sqrt (N:ℝ)) • flatJetCLM c 0 x (fun i => Fin.elim0 i)+
      (v.fst 1/Real.sqrt (N:ℝ)) • flatJetCLM c 1 x (fun _ => x)+
      flatJetCLM c 1 x (fun _ => frameSum e v.snd) := by
  ext g
  have h:=singleMixedObservation_inner_actual c x e v (unpackDisorder g)
  have hg : euclideanDisorder (unpackDisorder g)=g := rfl
  rw [hg] at h
  simpa only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    add_apply,smul_apply,smul_eq_mul,flatJetCLM_apply] using h

abbrev ValueObservationSpace (m : ℕ) := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))

/-- Proper value-only observation, omitting the redundant pure radial score. -/
def singleValueObservation {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ] ValueObservationSpace m :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ (Fin m))).symm.toContinuousLinearMap.comp
    (((Real.sqrt (N:ℝ))⁻¹ • flatJetCLM c 0 x (fun i => Fin.elim0 i)).prod (gradientCLM c x e))

lemma singleValueObservation_inner_actual {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : ValueObservationSpace m) (J : Disorder N P) :
    inner ℝ v (singleValueObservation c x e (euclideanDisorder J))=
      (v.fst/Real.sqrt (N:ℝ))*jet c 0 x (fun i => Fin.elim0 i) J+
      jet c 1 x (fun _ => frameSum e v.snd) J := by
  rw [WithLp.prod_inner_apply]
  change inner ℝ v.fst ((Real.sqrt (N:ℝ))⁻¹ * flatJetCLM c 0 x (fun i => Fin.elim0 i) (euclideanDisorder J))+
    inner ℝ v.snd (gradientCLM c x e (euclideanDisorder J))=_
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,flatJetCLM_apply,
    gradientCLM_apply,unpack_euclideanDisorder,jet_one_frameSum]
  simp only [mul_comm]
  ring

lemma singleValueObservation_dual {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (v : ValueObservationSpace m) :
    (innerSL ℝ v).comp (singleValueObservation c x e)=
      (v.fst/Real.sqrt (N:ℝ)) • flatJetCLM c 0 x (fun i => Fin.elim0 i)+
      flatJetCLM c 1 x (fun _ => frameSum e v.snd) := by
  ext g
  have h:=singleValueObservation_inner_actual c x e v (unpackDisorder g)
  have hg : euclideanDisorder (unpackDisorder g)=g := rfl
  rw [hg] at h
  simpa only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    add_apply,smul_apply,smul_eq_mul,flatJetCLM_apply] using h

end
end SlowEquilibration.NormalizedPairObservations
