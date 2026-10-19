module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalHistoryTransition
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! # Actual finite-dimensional path rotation covariance

Induction removes the last observed time. The conditional next-state law
is the proved physical SDE history transition, and its actual kernel has
the proved orthogonal covariance.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalStationarySDE
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

def restrictPath (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) (I : Finset ℝ≥0) (ω : VectorBrownian.Space N) : I → Vector N :=
  fun i => mixedProcess μ J β x i.1 ω

lemma restrictPath_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) (I : Finset ℝ≥0) : Measurable (restrictPath μ J β x I) :=
  Measurable.of_eval fun i => mixedProcess_measurable μ J β x i.1

def rotateCoordinates (U : Vector N ≃ₗᵢ[ℝ] Vector N) (I : Finset ℝ≥0) (v : I → Vector N) :
    I → Vector N := fun i => U (v i)

lemma rotateCoordinates_measurable (U : Vector N ≃ₗᵢ[ℝ] Vector N) (I : Finset ℝ≥0) :
    Measurable (rotateCoordinates U I) :=
  Measurable.of_eval fun i => U.continuous.measurable.comp (measurable_pi_apply i)

def appendCoordinate (I : Finset ℝ≥0) (a : ℝ≥0) (q : (I → Vector N) × Vector N) :
    ↥(insert a I) → Vector N := fun i =>
  if hi : i.1=a then q.2 else q.1 ⟨i.1,Finset.mem_of_mem_insert_of_ne i.2 hi⟩

lemma appendCoordinate_measurable (I : Finset ℝ≥0) (a : ℝ≥0) :
    Measurable (appendCoordinate (N := N) I a) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.1=a
  · simpa [appendCoordinate,hi] using (measurable_snd :
      Measurable (fun q : (I → Vector N) × Vector N => q.2))
  · simpa [appendCoordinate,hi,Function.comp_def] using
      ((measurable_pi_apply (⟨i.1,Finset.mem_of_mem_insert_of_ne i.2 hi⟩ : I)).comp measurable_fst)

lemma appendCoordinate_actual (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : Vector N) (I : Finset ℝ≥0) (a : ℝ≥0) (ω : VectorBrownian.Space N) :
    appendCoordinate I a (restrictPath μ J β x I ω,mixedProcess μ J β x a ω)=
      restrictPath μ J β x (insert a I) ω := by
  funext i
  by_cases hi : i.1=a <;> simp [appendCoordinate,restrictPath,hi]

lemma appendCoordinate_rotation (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (I : Finset ℝ≥0) (a : ℝ≥0) (q : (I → Vector N) × Vector N) :
    appendCoordinate I a (rotateCoordinates U I q.1,U q.2)=
      rotateCoordinates U (insert a I) (appendCoordinate I a q) := by
  funext i
  by_cases hi : i.1=a <;> simp [appendCoordinate,rotateCoordinates,hi]

/-- Every actual finite-dimensional diffusion law rotates with its field
and initial state. This includes arbitrary, repeated and unordered choices
of observed times, since each finite set is treated intrinsically. -/
theorem finitePathLaw_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (x : Vector N) (hx : OnSphere x) (I : Finset ℝ≥0) :
    ((VectorBrownian.law N).map (restrictPath μ J β x I)).map (rotateCoordinates U I) =
      (VectorBrownian.law N).map (restrictPath μ (rotatedDisorder U J) β (U x) I) := by
  classical
  induction I using Finset.induction_on_max with
  | empty =>
      rw [Measure.map_map (rotateCoordinates_measurable U ∅) (restrictPath_measurable μ J β x ∅)]
      apply Measure.map_congr
      exact .of_forall fun ω => by funext i; exact (Finset.notMem_empty i.1 i.2).elim
  | @insert a I hbefore ih =>
      rcases I.eq_empty_or_nonempty with hI | hI
      · subst I
        let lift : Vector N → ↥(insert a (∅ : Finset ℝ≥0)) → Vector N := fun v _ => v
        have hlift : Measurable lift := Measurable.of_eval fun _ => measurable_id
        have hk := mixedTransitionKernel_rotation hN μ J β U a x hx
        rw [mixedTransitionKernel_apply,mixedTransitionKernel_apply,mixedTransitionLaw,mixedTransitionLaw] at hk
        have he := congrArg (fun M : Measure (Vector N) => M.map lift) hk
        rw [Measure.map_map hlift U.continuous.measurable,
          Measure.map_map (hlift.comp U.continuous.measurable) (mixedProcess_measurable μ J β x a),
          Measure.map_map hlift (mixedProcess_measurable μ (rotatedDisorder U J) β (U x) a)] at he
        rw [Measure.map_map (rotateCoordinates_measurable U (insert a ∅)) (restrictPath_measurable μ J β x (insert a ∅))]
        convert he using 1 <;> congr 1 <;> funext ω i
        all_goals
          have hi : i.1=a := by simpa only [Finset.mem_insert,Finset.notMem_empty,or_false] using i.2
          simp [rotateCoordinates,restrictPath,lift,Function.comp_def,hi]
      · let s : ℝ≥0 := I.max' hI
        let point : (I → Vector N) → Vector N := fun v => v ⟨s,I.max'_mem hI⟩
        have hpoint : Measurable point := measurable_pi_apply _
        have hsa : s<a := hbefore s (I.max'_mem hI)
        have hZ (D : Disorder N μ.maxDegree) (y : Vector N) :
            Measurable[NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s]
              (restrictPath μ D β y I) := by
          refine @Measurable.of_eval (VectorBrownian.Space N) I (fun _ => Vector N)
            (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) s)
            (fun _ => inferInstance) (restrictPath μ D β y I) ?_
          intro i
          exact ((GlobalSDE.process_stronglyAdapted
            (NullAugmentation.driver (VectorBrownian.driver N))
            (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ D) _ (cutoffRadius_pos N)).choose_spec
            (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec y i.1).mono
              ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).mono
                (I.le_max' i.1 i.2))).measurable
        have hrec := history_nextState_law μ J β x s (a-s) (restrictPath μ J β x I) (hZ J x)
          point hpoint (.of_forall fun _ => rfl)
        have hrecR := history_nextState_law μ (rotatedDisorder U J) β (U x) s (a-s)
          (restrictPath μ (rotatedDisorder U J) β (U x) I) (hZ _ _) point hpoint (.of_forall fun _ => rfl)
        rw [add_tsub_cancel_of_le hsa.le] at hrec hrecR
        let ρ := (VectorBrownian.law N).map (restrictPath μ J β x I)
        haveI : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
        have hsupport : ∀ᵐ v ∂ρ, OnSphere (point v) := by
          apply (ae_map_iff (restrictPath_measurable μ J β x I).aemeasurable
            ((sphere_measurableSet N).preimage hpoint)).mpr
          exact (mixedProcess_onSphere (by omega) μ J β x hx).mono fun _ h => h s
        have hpairs := compProd_map_prodMap ρ
          ((mixedTransitionKernel μ J β (a-s)).comap point hpoint)
          ((mixedTransitionKernel μ (rotatedDisorder U J) β (a-s)).comap point hpoint)
          (rotateCoordinates U I) (rotateCoordinates_measurable U I) U U.continuous.measurable (by
            filter_upwards [hsupport] with v hv
            simp only [Kernel.comap_apply]
            exact mixedTransitionKernel_rotation hN μ J β U (a-s) (point v) hv)
        change ((ρ ⊗ₘ (mixedTransitionKernel μ J β (a-s)).comap point hpoint).map
            (Prod.map (rotateCoordinates U I) U)) =
          ρ.map (rotateCoordinates U I) ⊗ₘ (mixedTransitionKernel μ (rotatedDisorder U J) β (a-s)).comap point hpoint at hpairs
        dsimp [ρ] at hpairs
        rw [ih,← hrec,← hrecR] at hpairs
        have hpairM (D : Disorder N μ.maxDegree) (y : Vector N) :
            Measurable (fun ω => (restrictPath μ D β y I ω,mixedProcess μ D β y a ω)) :=
          (restrictPath_measurable μ D β y I).prodMk (mixedProcess_measurable μ D β y a)
        have hprodM := (rotateCoordinates_measurable U I).prodMap U.continuous.measurable
        have happend := appendCoordinate_measurable (N := N) I a
        have hleft : (VectorBrownian.law N).map (restrictPath μ J β x (insert a I)) =
            ((VectorBrownian.law N).map (fun ω => (restrictPath μ J β x I ω,mixedProcess μ J β x a ω))).map (appendCoordinate I a) := by
          rw [Measure.map_map happend (hpairM J x)]
          congr 1
          funext ω
          exact (appendCoordinate_actual μ J β x I a ω).symm
        have hright : (VectorBrownian.law N).map (restrictPath μ (rotatedDisorder U J) β (U x) (insert a I)) =
            ((VectorBrownian.law N).map (fun ω => (restrictPath μ (rotatedDisorder U J) β (U x) I ω,
              mixedProcess μ (rotatedDisorder U J) β (U x) a ω))).map (appendCoordinate I a) := by
          rw [Measure.map_map happend (hpairM _ _)]
          congr 1
          funext ω
          exact (appendCoordinate_actual μ (rotatedDisorder U J) β (U x) I a ω).symm
        rw [hleft,hright,Measure.map_map (rotateCoordinates_measurable U (insert a I)) happend]
        have hcomm : rotateCoordinates U (insert a I) ∘ appendCoordinate I a =
            appendCoordinate I a ∘ Prod.map (rotateCoordinates U I) U := by
          funext q
          exact (appendCoordinate_rotation U I a q).symm
        rw [hcomm,← Measure.map_map happend hprodM,hpairs]

end
end SlowEquilibration.SphericalRotationCovariance
