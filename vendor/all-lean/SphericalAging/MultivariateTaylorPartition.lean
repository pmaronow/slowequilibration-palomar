module

public import SphericalAging.MultivariateTaylor
public import SphericalAging.VectorItoFormula

public section

/-! Genuine multivariate C² Taylor partition closure. The only quadratic
input is the sum of the actual coordinate quadratic variations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MultivariateTaylorPartition
open HardSphereDynamics LocalSDE MultivariateTaylor
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*}

/-- A finite-dimensional continuous path has uniformly vanishing partition
increments in the genuine state norm. -/
lemma state_increments_tendsto (g : ℝ≥0 → State N) (t : ℝ≥0)
    (hg : ContinuousOn g (Icc 0 t)) : ∀ δ : ℝ,0<δ → ∀ᶠ n in atTop,
      ∀ i ∈ Finset.range (n+1),
        ‖g (uniformPartitionTime t (n+1) (i+1))-g (uniformPartitionTime t (n+1) i)‖<δ := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  intro δ hδ
  obtain ⟨η,hη,hm⟩ := (Metric.uniformContinuousOn_iff (α := ℝ≥0) (β := State N)).mp huc δ hδ
  have hdivNN : Tendsto (fun n : ℕ => t/((n+1 : ℕ) : ℝ≥0)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Tendsto (fun n : ℕ => ((t/((n+1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨m,hm'⟩ := Metric.tendsto_atTop.mp hdiv η hη
  filter_upwards [eventually_ge_atTop m] with n hn
  intro i hi
  have hip : i+1≤n+1 := Finset.mem_range.mp hi
  have hti := uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) ((Nat.le_add_right i 1).trans hip)
  have hti' := uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) hip
  have hmesh : ((t/((n+1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)<η := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (NNReal.coe_nonneg _)] using hm' n hn
  have hdist : dist (uniformPartitionTime t (n+1) (i+1)) (uniformPartitionTime t (n+1) i)<η := by
    rw [dist_uniformPartitionTime_succ_eq t (Nat.zero_lt_succ n) i]
    exact hmesh
  simpa only [dist_eq_norm] using hm _ hti' _ hti hdist

@[expose] def normQuadraticApprox (X : ℝ≥0 → Ω → State N) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,‖X (uniformPartitionTime t n (i+1)) ω-X (uniformPartitionTime t n i) ω‖^2

@[expose] def remainderApprox (f : State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,remainder f (X (uniformPartitionTime t n i) ω)
    (X (uniformPartitionTime t n (i+1)) ω)

lemma remainder_continuous {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun q : State N × State N => remainder f q.1 q.2) := by
  have hD := hf.continuous_fderiv (by norm_num)
  have hH := hessian_continuous hf
  unfold remainder
  fun_prop

/-- C² Taylor error is uniformly little-o along each actual continuous
state path, with its compact path range derived rather than assumed. -/
lemma remainder_eventually_bound {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (g : ℝ≥0 → State N) (t : ℝ≥0) (hg : ContinuousOn g (Icc 0 t)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,∀ i ∈ Finset.range (n+1),
      ‖remainder f (g (uniformPartitionTime t (n+1) i)) (g (uniformPartitionTime t (n+1) (i+1)))‖ ≤
        ε*‖g (uniformPartitionTime t (n+1) (i+1))-g (uniformPartitionTime t (n+1) i)‖^2 := by
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  intro ε hε
  obtain ⟨δ,hδ,hδbound⟩ := uniform_remainder_closedBall hf R ε hε
  filter_upwards [state_increments_tendsto g t hg δ hδ] with n hn
  intro i hi
  have hip : i+1≤n+1 := Finset.mem_range.mp hi
  apply hδbound _ _ _ _ (hn i hi)
  · simpa only [Metric.mem_closedBall,dist_zero_right] using
      hR _ (uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) ((Nat.le_add_right i 1).trans hip))
  · simpa only [Metric.mem_closedBall,dist_zero_right] using
      hR _ (uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) hip)

lemma remainder_subseq_tendsto_zero {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (X : ℝ≥0 → Ω → State N) (t : ℝ≥0) (ω : Ω) (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (q : ℝ)
    (hpath : ContinuousOn (fun s => X s ω) (Icc 0 t))
    (hq : Tendsto (fun n => normQuadraticApprox X t (k n+1) ω) atTop (𝓝 q)) :
    Tendsto (fun n => remainderApprox f X t (k n+1) ω) atTop (𝓝 0) := by
  let C : ℝ := |q|+1
  have hC : 0<C := by dsimp only [C];positivity
  have hqbound : ∀ᶠ n in atTop,normQuadraticApprox X t (k n+1) ω≤C := by
    filter_upwards [hq.eventually (Metric.ball_mem_nhds q zero_lt_one)] with n hn
    simp only [Metric.mem_ball,Real.dist_eq] at hn
    dsimp only [C]
    linarith [(abs_lt.mp hn).2,le_abs_self q]
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε/(2*C)
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hqbound.and
    (hk.eventually (remainder_eventually_bound hf (fun s => X s ω) t hpath δ hδ)))
  refine ⟨m,fun n hn => ?_⟩
  obtain ⟨hq',hr⟩ := hm n hn
  rw [dist_eq_norm,sub_zero]
  calc
    ‖remainderApprox f X t (k n+1) ω‖ ≤ ∑ i ∈ Finset.range (k n+1),
      ‖remainder f (X (uniformPartitionTime t (k n+1) i) ω)
        (X (uniformPartitionTime t (k n+1) (i+1)) ω)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k n+1),δ*
      ‖X (uniformPartitionTime t (k n+1) (i+1)) ω-X (uniformPartitionTime t (k n+1) i) ω‖^2 :=
        Finset.sum_le_sum (fun i hi => hr i hi)
    _ = δ*normQuadraticApprox X t (k n+1) ω := by rw [← Finset.mul_sum];rfl
    _ ≤ δ*C := mul_le_mul_of_nonneg_left hq' hδ.le
    _ = ε/2 := by dsimp only [δ];field_simp [hC.ne']
    _ < ε := by linarith

variable [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Actual quadratic variation in probability and continuous paths close
all genuinely multivariate C² Taylor partition errors. -/
theorem remainder_tendstoInMeasure {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (X : ℝ≥0 → Ω → State N) (t : ℝ≥0) (q : Ω → ℝ)
    (hXm : ∀ s,AEStronglyMeasurable (X s) P)
    (hXc : ∀ᵐ ω ∂P,ContinuousOn (fun s => X s ω) (Icc 0 t))
    (hQ : TendstoInMeasure P (fun n => normQuadraticApprox X t (n+1)) atTop q) :
    TendstoInMeasure P (fun n => remainderApprox f X t (n+1)) atTop (fun _ => 0) := by
  have hm : ∀ n,AEStronglyMeasurable (remainderApprox f X t (n+1)) P := by
    intro n
    have hsum := Finset.aestronglyMeasurable_sum (Finset.range (n+1)) (fun i _ =>
      (remainder_continuous hf).comp_aestronglyMeasurable
        ((hXm (uniformPartitionTime t (n+1) i)).prodMk (hXm (uniformPartitionTime t (n+1) (i+1)))))
    apply hsum.congr
    exact .of_forall (fun ω => by simp only [Finset.sum_apply];rfl)
  rw [exists_seq_tendstoInMeasure_atTop_iff hm]
  intro ns hns
  obtain ⟨ms,hms,hq⟩ := (hQ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hXc,hq] with ω hc hqω
  exact remainder_subseq_tendsto_zero hf X t ω (ns ∘ ms)
    (hns.tendsto_atTop.comp hms.tendsto_atTop) (q ω) hc hqω

end SphericalAging.MultivariateTaylorPartition
