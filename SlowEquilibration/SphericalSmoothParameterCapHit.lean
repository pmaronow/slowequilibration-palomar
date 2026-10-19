-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothParameterProcess
public import SlowEquilibration.SphericalParisiContinuousMaximum
public import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine jointly Borel finite-horizon cap-hit probabilities for the
actual parameterized spherical Brownian dynamics. -/
@[expose] public section
namespace SlowEquilibration.SphericalSmoothParameter
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalRotationCovariance SphericalParisiContinuousMaximum
open SphericalAging HardSphereDynamics
open scoped Topology NNReal ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
variable {N : ℕ}

def overlapPath (T : ℝ≥0) (z : Vector N×ContinuousPath N T) : C(PathTime T,ℝ) :=
  ⟨fun t=>|overlap z.1 (z.2 t)|,
    (((continuous_const.inner z.2.continuous).div_const (N:ℝ)).abs)⟩

theorem overlapPath_continuous (T : ℝ≥0) : Continuous (overlapPath (N:=N) T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have he : Continuous (fun z : (Vector N×ContinuousPath N T)×PathTime T=>z.1.2 z.2) :=
    continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
  exact ((continuous_fst.fst.inner he).div_const (N:ℝ)).abs

def pathMaximumOverlap (T : ℝ≥0) (z : Vector N×ContinuousPath N T) : ℝ := maximum (overlapPath T z)

theorem pathMaximumOverlap_continuous (T : ℝ≥0) : Continuous (pathMaximumOverlap (N:=N) T) :=
  maximum_continuous.comp (overlapPath_continuous T)

theorem pathMaximumOverlap_ge_iff (T : ℝ≥0) (α : ℝ) (u : Vector N) (p : ContinuousPath N T) :
    α ≤ pathMaximumOverlap T (u,p) ↔ ∃ t : PathTime T,α ≤ |overlap u (p t)| := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := maximum_attained (overlapPath T (u,p))
    change α ≤ maximum (overlapPath T (u,p)) at h
    rw [ht] at h
    exact ⟨t,h⟩
  · rintro ⟨t,h⟩
    exact h.trans (le_maximum (overlapPath T (u,p)) t)

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [FiniteDimensional ℝ Θ] [MeasurableSpace Θ] [BorelSpace Θ]

def capHitProbability (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g)
    (T : ℝ≥0) (α : ℝ) (q : Vector N×(Θ×Vector N)) : ℝ :=
  (VectorBrownian.law N).real {ω | α ≤ pathMaximumOverlap T (q.1,jointContinuousPath β g hg T (q.2,ω))}

theorem capHitProbability_measurable (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (α : ℝ) : Measurable (capHitProbability β g hg T α) := by
  have hm : Measurable (fun z : (Vector N×(Θ×Vector N))×VectorBrownian.Space N=>
      pathMaximumOverlap T (z.1.1,jointContinuousPath β g hg T (z.1.2,z.2))) :=
    (pathMaximumOverlap_continuous T).measurable.comp (measurable_fst.fst.prodMk
      ((jointContinuousPath_measurable β g hg T).comp (measurable_fst.snd.prodMk measurable_snd)))
  exact (measurable_measure_prodMk_left (ν:=VectorBrownian.law N)
    (measurableSet_le measurable_const hm)).ennreal_toReal

theorem capHitProbability_mem_unit (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (α : ℝ) (q : Vector N×(Θ×Vector N)) :
    capHitProbability β g hg T α q ∈ Icc 0 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩

/-- Exact finite-horizon hit probability of the original constructed
Brownian solution, with no hitting or measurability premise. -/
theorem capHitProbability_eq_actual (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (α : ℝ) (q : Vector N×(Θ×Vector N)) :
    capHitProbability β g hg T α q = (VectorBrownian.law N).real
      {ω | ∃ t : ℝ≥0,t ≤ T ∧ α ≤ |overlap q.1 (SphericalC1Dynamics.process β
        (fun y=>g (q.2.1,y)) (hg.comp (contDiff_const.prodMk contDiff_id)) q.2.2 t ω)|} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [jointContinuousPath_ae_actual β g hg T q.2] with ω he
  apply propext
  rw [pathMaximumOverlap_ge_iff]
  constructor
  · rintro ⟨t,hh⟩
    refine ⟨t.1,t.2.2,?_⟩
    simpa only [he] using hh
  · rintro ⟨t,ht,hh⟩
    refine ⟨⟨t,⟨zero_le,ht⟩⟩,?_⟩
    simpa only [he] using hh

def uniformCapHitProbability (β : ℝ) (g : Θ×Vector N→Vector N) (hg : ContDiff ℝ 1 g)
    (T : ℝ≥0) (α : ℝ) (q : Vector N×Θ) : ℝ :=
  ∫ x : Vector N,capHitProbability β g hg T α (q.1,(q.2,x)) ∂sphereLaw N

theorem uniformCapHitProbability_measurable (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (α : ℝ) :
    Measurable (uniformCapHitProbability β g hg T α) := by
  have hm : Measurable (fun z : (Vector N×Θ)×Vector N=>capHitProbability β g hg T α (z.1.1,(z.1.2,z.2))) :=
    (capHitProbability_measurable β g hg T α).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem uniformCapHitProbability_eq_actual (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (α : ℝ) (q : Vector N×Θ) :
    uniformCapHitProbability β g hg T α q =
      ∫ x : Vector N,(VectorBrownian.law N).real {ω | ∃ t : ℝ≥0,t ≤ T ∧ α ≤
        |overlap q.1 (SphericalC1Dynamics.process β (fun y=>g (q.2,y))
          (hg.comp (contDiff_const.prodMk contDiff_id)) x t ω)|} ∂sphereLaw N := by
  unfold uniformCapHitProbability
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>capHitProbability_eq_actual β g hg T α (q.1,(q.2,x)))

theorem uniformCapHitProbability_mem_unit (β : ℝ) (g : Θ×Vector N→Vector N)
    (hg : ContDiff ℝ 1 g) (T : ℝ≥0) (α : ℝ) (q : Vector N×Θ) :
    uniformCapHitProbability β g hg T α q ∈ Icc 0 1 := by
  refine ⟨integral_nonneg (fun x=>(capHitProbability_mem_unit β g hg T α (q.1,(q.2,x))).1),?_⟩
  have hi : Integrable (fun x : Vector N=>capHitProbability β g hg T α (q.1,(q.2,x))) (sphereLaw N) :=
    Integrable.of_bound ((capHitProbability_measurable β g hg T α).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1
      (ae_of_all _ (fun x=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (capHitProbability_mem_unit β g hg T α (q.1,(q.2,x))).1]
        exact (capHitProbability_mem_unit β g hg T α (q.1,(q.2,x))).2))
  exact (integral_mono hi (integrable_const 1)
    (fun x=>(capHitProbability_mem_unit β g hg T α (q.1,(q.2,x))).2)).trans_eq (by simp)

end
end SlowEquilibration.SphericalSmoothParameter
