module

public import SphericalAging.GlobalHamiltonianParameter
public import SphericalAging.AdaptedContinuous
public import Mathlib.MeasureTheory.Function.Floor

public section

set_option backward.privateInPublic true

/-! Joint adapted continuous versions from the actual measurable fixed-time
L² classes. The countable past-grid selector preserves the full filtration;
no completion or right continuity of the filtration is assumed.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.JointAdaptedContinuous
set_option maxHeartbeats 1800000
variable {A Ω E : Type*} [MeasurableSpace A] [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}

omit mΩ in
private lemma measurableSpace_prod_le {m n : MeasurableSpace Ω} (h : m ≤ n) :
    ‹MeasurableSpace A›.prod m ≤ ‹MeasurableSpace A›.prod n :=
  sup_le_sup le_rfl (MeasurableSpace.comap_mono h)

/-- A joint representative inside any actual sub-sigma-algebra. -/
theorem exists_joint_subsigma_representative (t : ℝ≥0)
    (f : A → lpMeas E ℝ (F t) 2 P) (hf : StronglyMeasurable f) :
    ∃ G : A × Ω → E, StronglyMeasurable[‹MeasurableSpace A›.prod (F t)] G ∧ ∀ a,
      (fun ω => G (a,ω)) =ᵐ[P] (f a : Lp E 2 P) := by
  let e := lpMeasToLpTrimLie E ℝ 2 P (F.le t)
  obtain ⟨G,hG,hGa⟩ := @JointLpRepresentative.exists_joint_representative A Ω E
    ‹MeasurableSpace A› (F t) _ _ _ _ _ _ (P.trim (F.le t)) (fun a => e (f a))
      (e.continuous.comp_stronglyMeasurable hf)
  refine ⟨G,hG,fun a => ?_⟩
  have hae : (fun ω => G (a,ω)) =ᵐ[P] (e (f a) : Lp E 2 (P.trim (F.le t))) :=
    MeasureTheory.ae_eq_of_ae_eq_trim (hGa a)
  exact hae.trans (lpMeasToLpTrim_ae_eq (F.le t) (f a))

section Continuous
variable (f : (t : ℝ≥0) → A → lpMeas E ℝ (F t) 2 P)
  (hf : ∀ t, StronglyMeasurable (f t))

private def fixedVersion (t : ℝ≥0) : A × Ω → E :=
  (exists_joint_subsigma_representative t (f t) (hf t)).choose

private lemma fixedVersion_sm (t : ℝ≥0) :
    StronglyMeasurable[‹MeasurableSpace A›.prod (F t)] (fixedVersion f hf t) :=
  (exists_joint_subsigma_representative t (f t) (hf t)).choose_spec.1

private lemma fixedVersion_ae (t : ℝ≥0) (a : A) :
    (fun ω => fixedVersion f hf t (a,ω)) =ᵐ[P] (f t a : Lp E 2 P) :=
  (exists_joint_subsigma_representative t (f t) (hf t)).choose_spec.2 a

/-- Actual joint version selected from countably many measurable past-grid
values. -/
@[expose] def jointContinuousVersion (a : A) (t : ℝ≥0) (ω : Ω) : E :=
  limUnder atTop (fun n => fixedVersion f hf (AdaptedContinuous.pastGrid t n) (a,ω))

lemma jointContinuousVersion_jointAdapted (t : ℝ≥0) :
    StronglyMeasurable[‹MeasurableSpace A›.prod (F t)]
      (fun q : A × Ω => jointContinuousVersion f hf q.1 t q.2) := by
  let : MeasurableSpace (A × Ω) := ‹MeasurableSpace A›.prod (F t)
  exact StronglyMeasurable.limUnder (fun n =>
    (fixedVersion_sm f hf _).mono (measurableSpace_prod_le
      (F.mono (AdaptedContinuous.pastGrid_le t n))))

lemma jointContinuousVersion_jointMeasurable :
    StronglyMeasurable (fun q : A × (ℝ≥0 × Ω) => jointContinuousVersion f hf q.1 q.2.1 q.2.2) := by
  apply StronglyMeasurable.limUnder
  intro n
  have hm : Measurable (fun z : ℕ × (A × (ℝ≥0 × Ω)) =>
      fixedVersion f hf (AdaptedContinuous.gridTime n z.1) (z.2.1,z.2.2.2)) := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable (fun y : A × (ℝ≥0 × Ω) => fixedVersion f hf (AdaptedContinuous.gridTime n k) (y.1,y.2.2))
    exact ((fixedVersion_sm f hf (AdaptedContinuous.gridTime n k)).mono
      (measurableSpace_prod_le (F.le _))).measurable.comp
        (measurable_fst.prodMk measurable_snd.snd)
  have hgrid : Measurable (fun q : A × (ℝ≥0 × Ω) => ⌊q.2.1*(n+1)⌋₊) := by
    have h : Measurable (fun q : A × (ℝ≥0 × Ω) => ⌊(q.2.1 : ℝ)*((n : ℝ)+1)⌋₊) := by fun_prop
    convert h using 1
    funext q
    rfl
  exact (hm.comp (hgrid.prodMk measurable_id)).stronglyMeasurable

/-- Every deterministic slice is the original actual continuous process
on a common all-time almost-everywhere event. -/
lemma jointContinuousVersion_ae_eq (X : A → ℝ≥0 → Ω → E)
    (hX : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => X a t ω))
    (hclass : ∀ a t, (f t a : Lp E 2 P) =ᵐ[P] X a t) (a : A) :
    ∀ᵐ ω ∂P, ∀ t, jointContinuousVersion f hf a t ω = X a t ω := by
  have hgrid : ∀ᵐ ω ∂P, ∀ n k : ℕ,
      fixedVersion f hf (AdaptedContinuous.gridTime n k) (a,ω) =
        X a (AdaptedContinuous.gridTime n k) ω :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k =>
      (fixedVersion_ae f hf _ a).trans (hclass a _)))
  filter_upwards [hgrid,hX a] with ω hg hc
  intro t
  have hl : Tendsto (fun n => fixedVersion f hf (AdaptedContinuous.pastGrid t n) (a,ω))
      atTop (𝓝 (X a t ω)) := by
    have he : (fun n => fixedVersion f hf (AdaptedContinuous.pastGrid t n) (a,ω)) =
        (fun n => X a (AdaptedContinuous.pastGrid t n) ω) := funext (fun n => hg n _)
    rw [he]
    exact hc.continuousAt.tendsto.comp (AdaptedContinuous.tendsto_pastGrid t)
  exact hl.limUnder_eq

include hf in
/-- Construction theorem: the joint family is measurable, jointly adapted
at each time, and preserves the actual continuous process on every slice. -/
theorem exists_jointAdapted_continuous_version (X : A → ℝ≥0 → Ω → E)
    (hX : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => X a t ω))
    (hclass : ∀ a t, (f t a : Lp E 2 P) =ᵐ[P] X a t) :
    ∃ Y : A → ℝ≥0 → Ω → E,
      StronglyMeasurable (fun q : A × (ℝ≥0 × Ω) => Y q.1 q.2.1 q.2.2) ∧
      (∀ t, StronglyMeasurable[‹MeasurableSpace A›.prod (F t)]
        (fun q : A × Ω => Y q.1 t q.2)) ∧
      ∀ a, ∀ᵐ ω ∂P, (∀ t, Y a t ω = X a t ω) ∧ Continuous (fun t => Y a t ω) := by
  refine ⟨jointContinuousVersion f hf,jointContinuousVersion_jointMeasurable f hf,
    jointContinuousVersion_jointAdapted f hf,fun a => ?_⟩
  filter_upwards [jointContinuousVersion_ae_eq f hf X hX hclass a,hX a] with ω he hc
  exact ⟨he,by simpa only [he] using hc⟩

end Continuous
end SphericalAging.JointAdaptedContinuous
