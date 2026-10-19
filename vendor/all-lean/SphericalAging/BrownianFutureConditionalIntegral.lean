module

public import SphericalAging.BrownianFutureFiltered
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! Conditional integration of genuinely independent Wiener futures for
unbounded integrable tests and arbitrary observed waiting variables. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace SphericalAging.BrownianFutureConditionalIntegral
open BrownianFuturePath BrownianFutureFiltered VectorBrownian
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {A : Type*} [MeasurableSpace A]

theorem waiting_future_condExp (s : ℝ≥0) (Z : Space N → A)
    (hZ : Measurable[NullAugmentation.augment (filtration N) (law N) s] Z)
    (G : A × Space N → ℝ) (hG : StronglyMeasurable G)
    (hGi : Integrable G (((law N).map Z).prod (law N))) :
    (law N)[(fun ω => G (Z ω,future s ω)) |
      NullAugmentation.augment (filtration N) (law N) s] =ᵐ[law N]
      fun ω => ∫ η,G (Z ω,η) ∂law N := by
  let P := law N
  let F := NullAugmentation.augment (filtration N) P
  let μ := P.map Z
  let g : A → ℝ := fun z => ∫ η,G (z,η) ∂P
  have hmZ : Measurable Z := hZ.mono (F.le s) le_rfl
  have hμ : IsProbabilityMeasure μ :=
    (hasLaw_map hmZ.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  letI := hμ
  have hg : StronglyMeasurable g := hG.integral_prod_right'
  have hgi : Integrable g μ := hGi.integral_prod_left
  have hmapZ : MeasurePreserving Z P μ := ⟨hmZ,rfl⟩
  have hga : StronglyMeasurable[F s] (fun ω => g (Z ω)) := hg.comp_measurable hZ
  have hgiZ : Integrable (fun ω => g (Z ω)) P :=
    hmapZ.integrable_comp_of_integrable hgi
  have hφ := waiting_future_measurePreserving s Z hZ
  have hterminal : Integrable (fun ω => G (Z ω,future s ω)) P :=
    hφ.integrable_comp_of_integrable hGi
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) hterminal
    (fun _ _ _ => hgiZ.integrableOn) ?_ hga.aestronglyMeasurable
  intro S hS _
  let H : Space N → ℝ := S.indicator (fun _ => 1)
  have hH : StronglyMeasurable[F s] H := stronglyMeasurable_const.indicator hS
  have hHb (ω : Space N) : ‖H ω‖≤1 := by
    by_cases hω : ω∈S <;> simp [H,hω]
  let Z' : Space N → A×ℝ := fun ω => (Z ω,H ω)
  have hZ'a : Measurable[F s] Z' := hZ.prodMk hH.measurable
  have hZ'm : Measurable Z' := hZ'a.mono (F.le s) le_rfl
  let μ' := P.map Z'
  letI : IsProbabilityMeasure μ' :=
    (hasLaw_map hZ'm.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hdrop : MeasurePreserving (Prod.fst : A×ℝ→A) μ' μ := by
    refine ⟨measurable_fst,?_⟩
    change (P.map Z').map Prod.fst=P.map Z
    rw [Measure.map_map measurable_fst hZ'm]
    rfl
  let ψ : (A×ℝ)×Space N → A×Space N := fun q => (q.1.1,q.2)
  have hψ : MeasurePreserving ψ (μ'.prod P) (μ.prod P) :=
    hdrop.prod (MeasurePreserving.id P)
  let G' : (A×ℝ)×Space N → ℝ := fun q => G (ψ q)
  have hG' : StronglyMeasurable G' := hG.comp_measurable hψ.measurable
  have hG'i : Integrable G' (μ'.prod P) := hψ.integrable_comp_of_integrable hGi
  have hboundμ' : ∀ᵐ z ∂μ',‖z.2‖≤1 :=
    (ae_map_iff hZ'm.aemeasurable (measurableSet_le measurable_snd.norm measurable_const)).mpr
      (.of_forall hHb)
  let W : (A×ℝ)×Space N → ℝ := fun q => q.1.2*G' q
  have hW : StronglyMeasurable W :=
    (measurable_snd.comp measurable_fst).stronglyMeasurable.mul hG'
  have hWi : Integrable W (μ'.prod P) := by
    apply hG'i.norm.mono' hW.aestronglyMeasurable
    filter_upwards [(measurePreserving_fst (μ:=μ') (ν:=P)).quasiMeasurePreserving.ae hboundμ'] with q hq
    change ‖q.1.2*G' q‖≤‖G' q‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hq
  let φ' : Space N → (A×ℝ)×Space N := fun ω => (Z' ω,future s ω)
  have hφ' : MeasurePreserving φ' P (μ'.prod P) := waiting_future_measurePreserving s Z' hZ'a
  have hpull : (∫ ω,W (φ' ω) ∂P)=∫ q,W q ∂μ'.prod P := by
    rw [←hφ'.map_eq]
    exact (integral_map hφ'.measurable.aemeasurable hW.aestronglyMeasurable).symm
  have hinner : (∫ q,W q ∂μ'.prod P)=∫ z : A×ℝ,z.2*g z.1 ∂μ' := by
    rw [integral_prod W hWi]
    apply integral_congr_ae
    exact .of_forall (fun z => by
      change (∫ η,z.2*G (z.1,η) ∂P)=z.2*(∫ η,G (z.1,η) ∂P)
      exact integral_const_mul _ _)
  have hback : (∫ z : A×ℝ,z.2*g z.1 ∂μ')=∫ ω,H ω*g (Z ω) ∂P := by
    change (∫ z : A×ℝ,z.2*g z.1 ∂P.map Z')=_
    exact integral_map hZ'm.aemeasurable
      (measurable_snd.stronglyMeasurable.mul (hg.comp_measurable measurable_fst)).aestronglyMeasurable
  have ht : (∫ ω,H ω*G (Z ω,future s ω) ∂P)=∫ ω,H ω*g (Z ω) ∂P :=
    hpull.trans (hinner.trans hback)
  have hSambient : MeasurableSet S := F.le s S hS
  have ha : (fun ω => H ω*G (Z ω,future s ω))=
      S.indicator (fun ω => G (Z ω,future s ω)) := by
    funext ω
    by_cases hω : ω∈S <;> simp [H,hω]
  have hb : (fun ω => H ω*g (Z ω))=S.indicator (fun ω => g (Z ω)) := by
    funext ω
    by_cases hω : ω∈S <;> simp [H,hω]
  rw [ha,hb,integral_indicator hSambient,integral_indicator hSambient] at ht
  exact ht.symm

end SphericalAging.BrownianFutureConditionalIntegral
