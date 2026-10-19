module
public import FourPapersCommon.NormalizedCGF
public import FourPapersCommon.ConvexHalfLines
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Actual differentiability of normalized logarithmic moments at every real
parameter, and rigorous gluing of signed open-half-line convexity at zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem analyticAt_normalizedCGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : integrableExpSet X P=univ) (lam : ℝ) :
    AnalyticAt ℝ (normalizedCGF P X) lam := by
  have hall (r : ℝ) : r∈interior (integrableExpSet X P) := by simp [hX]
  by_cases h0 : lam=0
  · subst lam
    exact analyticAt_normalizedCGF_zero P X (hall 0)
  · have he : (fun r : ℝ=>cgf X P r/r)=ᶠ[𝓝 lam] normalizedCGF P X := by
      filter_upwards [eventually_ne_nhds h0] with r hr
      exact (normalizedCGF_of_ne P X hr).symm
    exact ((analyticAt_cgf (hall lam)).div analyticAt_id h0).congr he

theorem convexOn_Ici_of_open_halfLine {f : ℝ → ℝ} (hf : Continuous f)
    (hconv : ConvexOn ℝ (Ioi 0) f) : ConvexOn ℝ (Ici 0) f := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [mem_Ici,mem_Iic] at hx hy
  let d := fun n : ℕ=>1/((n:ℝ)+1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hxlim : Tendsto (fun n=>x+d n) atTop (𝓝 x) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hylim : Tendsto (fun n=>y+d n) atTop (𝓝 y) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hleft := (hf.continuousAt.tendsto).comp ((hxlim.const_mul a).add (hylim.const_mul b))
  have hright := ((hf.continuousAt.tendsto.comp hxlim).const_mul a).add
    ((hf.continuousAt.tendsto.comp hylim).const_mul b)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  have hdpos : 0 < d n := by dsimp [d];positivity
  have hxx : x+d n∈Ioi (0:ℝ) := by change 0 < x+d n;linarith [hx]
  have hyy : y+d n∈Ioi (0:ℝ) := by change 0 < y+d n;linarith [hy]
  convert! hconv.2 hxx hyy ha hb hab using 1 <;> simp only [Function.comp_apply,smul_eq_mul]

theorem convexOn_Iic_of_open_halfLine {f : ℝ → ℝ} (hf : Continuous f)
    (hconv : ConvexOn ℝ (Iio 0) f) : ConvexOn ℝ (Iic 0) f := by
  refine ⟨convex_Iic 0,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [mem_Ici,mem_Iic] at hx hy
  let d := fun n : ℕ=>1/((n:ℝ)+1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hxlim : Tendsto (fun n=>x-d n) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hd
  have hylim : Tendsto (fun n=>y-d n) atTop (𝓝 y) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hd
  have hleft := (hf.continuousAt.tendsto).comp ((hxlim.const_mul a).add (hylim.const_mul b))
  have hright := ((hf.continuousAt.tendsto.comp hxlim).const_mul a).add
    ((hf.continuousAt.tendsto.comp hylim).const_mul b)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  have hdpos : 0 < d n := by dsimp [d];positivity
  have hxx : x-d n∈Iio (0:ℝ) := by change x-d n < 0;linarith [hx]
  have hyy : y-d n∈Iio (0:ℝ) := by change y-d n < 0;linarith [hy]
  convert! hconv.2 hxx hyy ha hb hab using 1 <;> simp only [Function.comp_apply,smul_eq_mul]

theorem convexOn_normalizedCGF_of_signed_halfLines {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : integrableExpSet X P=univ)
    (hleft : ConvexOn ℝ (Iio 0) (normalizedCGF P X))
    (hright : ConvexOn ℝ (Ioi 0) (normalizedCGF P X)) :
    ConvexOn ℝ univ (normalizedCGF P X) := by
  have hdiff : Differentiable ℝ (normalizedCGF P X) :=
    fun lam=>(analyticAt_normalizedCGF P X hX lam).differentiableAt
  exact convexOn_univ_of_halfLines hdiff
    (convexOn_Iic_of_open_halfLine hdiff.continuous hleft)
    (convexOn_Ici_of_open_halfLine hdiff.continuous hright)

end FourPapersCommon
