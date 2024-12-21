/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal

/- recommended whenever you define anything new. -/
noncomputable section


/- Now write definitions and theorems. -/
namespace MeasureTheory

theorem SetAlgebraIsSetSemiRing (h1 : IsSetAlgebra S) : IsSetSemiring S := by {
  refine IsSetRing.isSetSemiring ?_
  exact IsSetAlgebra.isSetRing h1
}

-- def LE.lesser [les : LE α] (x : les.le a b) := a
def lesser {α : Type} [LE α] {x y : α} (h : x ≤ y) : α :=
  x
def greater {α : Type} [LE α] {x y : α} (h : x ≤ y) : α :=
  y


open Filter Topology

variable {α : Type*} {S : Set (Set α)} [mα : MeasurableSpace α] (μ : AddContent S)


lemma AddContent.additive (A B : Set α) (hAB : Disjoint A B) : μ (A ∪ B) = μ A + μ B := by {
  sorry
}
-- lemma AddContent.mono (A B : Set α) (hAB : Disjoint A B) : μ (A ∪ B) = μ A + μ B := by {
--   sorry
-- }
  -- := by {

  -- }

def AddContent.sAdditive : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (⋃ i, A i ∈ S) → Pairwise (Disjoint on A) →
    μ (⋃ i, A i) = ∑' i, μ (A i)

def AddContent.sSubAdditive  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (⋃ i, A i ∈ S) →
    μ (⋃ i, A i) <= ∑' i, μ (A i)

def AddContent.sContinuousFromBelow  : Prop :=
  ∀⦃A : ℕ → Set α⦄ {B : Set α }, (∀ i, (A i) ∈ S) -> (B ∈ S) ->
  (Tendsto A atTop (𝓝[≤] B)) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 (μ B))

def AddContent.sContinuousFromAbove  : Prop :=
  ∀⦃A : ℕ → Set α⦄ (B : Set α), (∀ i, (A i) ∈ S) -> (B ∈ S) -> (μ (A 0) < ∞) ->
  (Tendsto A atTop (𝓝[≥] B)) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 (μ B))

def AddContent.sContinuousInEmpty  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (μ (A 0) < ∞) ->
  (Tendsto A atTop (𝓝 ∅)) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 0)

lemma sAdditive_implies_sSubAdditive : μ.sAdditive -> μ.sSubAdditive := sorry
lemma sSubAdditive_implies_sAdditive : μ.sSubAdditive -> μ.sAdditive := sorry

lemma sAdditive_implies_sContinuousFromBelow : μ.sAdditive -> μ.sContinuousFromBelow := sorry
lemma sContinuousFromBelow_implies_sAdditive : μ.sContinuousFromBelow -> μ.sAdditive := sorry

lemma sContinuousFromAbove_implies_sContinuousInEmpty : μ.sContinuousFromAbove -> μ.sContinuousInEmpty := sorry
lemma sContinuousInEmpty_implies_sContinuousFromAbove : μ.sContinuousInEmpty -> μ.sContinuousFromAbove := sorry

lemma sAdditive_implies_sContinuousInEmpty : μ.sAdditive -> μ.sContinuousInEmpty := sorry

lemma sContinuousInEmpty_finite_implies_sAdditive : μ.sContinuousInEmpty ∧ μ univ < ∞ -> μ.sAdditive := sorry

  -- ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (μ (A 0) < ∞) ->
  -- (Tendsto A atTop (𝓝[≥] B)) ->
  --   Tendsto (λ n => μ (A n)) atTop (𝓝 0)


def AddContent.toOuterMeasure :=
    inducedOuterMeasure (λ s : Set α => λ _ : s ∈ S => μ s)

variable (hAlg : IsSetAlgebra S)

lemma addContent_outer_measure_equal_on_S (s : Set α) (hs : s ∈ S) (hμ : μ.sAdditive)
  : μ.toOuterMeasure hAlg.empty_mem μ.empty' s = μ s := by {
      -- generalize h : μ.toOuterMeasure hAlg.empty_mem μ.empty' = ν
      let ν := μ.toOuterMeasure hAlg.empty_mem μ.empty'
      suffices ν s <= μ s ∧ ν s >= μ s by exact le_antisymm this.1 this.2
      constructor
      ·
        unfold ν AddContent.toOuterMeasure inducedOuterMeasure OuterMeasure.ofFunction
        rw [← @OuterMeasure.measureOf_eq_coe]
        simp
        let f : ℕ -> Set α := fun n => if n = 0 then s else ∅
        have hf : ⋃ i, f i = s := by ext; simp [f]
        calc
        ⨅ f : ℕ -> Set α, ⨅ (_ : s ⊆ ⋃ i, f i), ∑' (i : ℕ), extend (fun s x ↦ μ s) (f i)
        <= ⨅ (_ : s ⊆ ⋃ i, f i), ∑' (i : ℕ),
          extend (P := Membership.mem S) (fun s x ↦ μ s) (f i) := by apply iInf_le
        _ =  ∑' (i : ℕ), extend (P := Membership.mem S) (fun s x ↦ μ s) (f i) := by simp [hf]
        _ =  μ s := by {
          unfold f
          simp [apply_ite, extend_eq (fun s x => μ s)]
          rw [show extend (P := Membership.mem S) (fun s x => μ s) s = μ s by {
            exact extend_eq (fun s x ↦ μ s) hs
          }]
          rw [show extend (P := Membership.mem S) (fun s x => μ s) ∅ = 0 by {
            have h := extend_eq (fun s x ↦ μ s) hAlg.empty_mem
            simp at h
            exact h
          }]
          simp
        }
      ·
        rw [ge_iff_le]
        unfold ν AddContent.toOuterMeasure inducedOuterMeasure OuterMeasure.ofFunction
        rw [← OuterMeasure.measureOf_eq_coe]
        simp
        intro A hA
        by_cases hAS : ∀n, A n ∈ S
        ·
          calc μ s = μ ((⋃n, A n) ∩ s) := by rw [inter_eq_self_of_subset_right hA]
          _ = μ (⋃ n, A n ∩ s) := by rw [@iUnion_inter]
          _ <= ∑' n, μ (A n ∩ s) := by {
            apply sAdditive_implies_sSubAdditive μ hμ
            intro n; exact IsSetAlgebra.inter_mem hAlg (hAS n) hs
            suffices ⋃ n, A n ∩ s = s by exact mem_of_eq_of_mem this hs
            simp [<- iUnion_inter, inter_eq_self_of_subset_right, hA]
          }
          _ <= ∑' n, μ (A n) := by {
            gcongr
            rename_i n
            specialize hAS n
            have h : A n ∩ s ∈ S := by exact IsSetAlgebra.inter_mem hAlg hAS hs
            have h' : A n ∩ s ⊆ A n := by exact inter_subset_left
            have hA : IsSetSemiring S := by exact SetAlgebraIsSetSemiRing hAlg
            apply addContent_mono hA h hAS h'
          }
          _ = ∑' n, extend (fun s x ↦ μ s) (A n) := by {
            congr; ext n
            exact Eq.symm (extend_eq (fun s x ↦ μ s) (hAS n))
          }
        ·
          suffices ∞ <= ∑' n, extend (P := Membership.mem S) (fun s x ↦ μ s) (A n) by {
            rw [@top_le_iff] at this
            rw [this]
            simp
          }
          push_neg at hAS
          obtain ⟨n, hn⟩ := hAS
          calc ∞ = extend (P := Membership.mem S) (fun s x => μ s) (A n) := by {
            unfold extend
            simp [hn]
          }
          _ <= ∑' n, extend (fun s x ↦ μ s) (A n) := by exact ENNReal.le_tsum n
  }

omit mα in
lemma addContent_caratheodory_measurable (s : Set α) (hs : s ∈ S)
  : (μ.toOuterMeasure hAlg.empty_mem μ.empty').IsCaratheodory s := by {
    unfold OuterMeasure.IsCaratheodory
    intro t
    have htsDisjoint : Disjoint (t ∩ s) (t \ s) := by exact Disjoint.symm disjoint_sdiff_inter
    have htsUnion : t ∩ s ∪ t \ s = t := by exact inter_union_diff t s
    have hSetRing : IsSetRing S := by exact IsSetAlgebra.isSetRing hAlg
    -- generalize_proofs hem μem
    apply le_antisymm
    · apply measure_le_inter_add_diff
    · unfold AddContent.toOuterMeasure inducedOuterMeasure OuterMeasure.ofFunction
      rw [← OuterMeasure.measureOf_eq_coe]
      simp
      intro A hA
      have h: ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ S) (n : ℕ),
        extend (P := Membership.mem S) (fun s x => μ s) (A n) = μ (A n) := by {
          intro A hAS n;
          exact extend_eq (fun s x ↦ μ s) (hAS n)
        }
      by_cases hAS : ∀n, A n ∈ S
      · have hans : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ S) n, A n ∩ s ∈ S := by intro A hAS n; exact IsSetRing.inter_mem hSetRing (hAS n) hs
        have hans2 : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ S) n, A n \ s ∈ S := by intro A hAS n; exact hSetRing.diff_mem (hAS n) hs
        have hansU : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ S) n, A n ∩ s ∪ A n \ s = A n := by intro A hAS n; exact inter_union_diff (A n) s
        have hansD : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ S) n, Disjoint (A n ∩ s) (A n \ s) := by {
          intro A hAS n
          exact Disjoint.symm disjoint_sdiff_inter
        }
        simp_rw [h A hAS]

        rw [show ∑' n, μ (A n) = ∑' n, μ (A n ∩ s) + ∑' n, μ (A n \ s) by {
          calc ∑' (n : ℕ), μ (A n) = ∑' (n : ℕ), (μ (A n ∩ s) + μ (A n \ s)) := by {
              congr
              ext n
              have h := addContent_union (m := μ) hSetRing (hans A hAS n) (hans2 A hAS n) (hansD A hAS n)
              rw [hansU A hAS] at h
              exact h
            }
          _ = ∑' (n : ℕ), μ (A n ∩ s) + ∑' (n : ℕ), μ (A n \ s) := ENNReal.tsum_add
            }]
        gcongr
        ·
          let B n := A n ∩ s
          have hBS : ∀n, B n ∈ S := by intro n; exact hans A hAS n
          have hB : t ∩ s ⊆ ⋃ n, A n ∩ s := by
            calc t ∩ s ⊆ (⋃ n, A n) ∩ s := by exact inter_subset_inter hA fun ⦃a⦄ a ↦ a
            _ = ⋃ n, A n ∩ s := by rw [iUnion_inter]

          calc ⨅ f : ℕ -> Set α, ⨅ (_ : t ∩ s ⊆ ⋃ n, f n), ∑' n, extend (fun s x ↦ μ s) (f n)
            <= ⨅ (_ : t ∩ s ⊆ ⋃ n, B n), ∑' n, extend (fun s x ↦ μ s) (B n) := by apply iInf_le
          _  = ∑' n, extend (fun s x ↦ μ s) (B n) := by simp [B, hB]; rfl
          _ = ∑' (n : ℕ), μ (B n) := by congr; ext n; exact h B (hans A hAS) n
          _ = ∑' (n : ℕ), μ (A n ∩ s) := by simp [B]
        ·
          let B n := A n \ s
          have hBS : ∀n, B n ∈ S := by intro n; exact hans2 A hAS n
          have hB : t \ s ⊆ ⋃ n, A n \ s := by
            calc t \ s ⊆ (⋃ n, A n) \ s := by exact inter_subset_inter hA fun ⦃a⦄ a ↦ a
            _ = ⋃ n, A n \ s := by rw [iUnion_diff]

          calc ⨅ f : ℕ -> Set α, ⨅ (_ : t \ s ⊆ ⋃ n, f n), ∑' n, extend (fun s x ↦ μ s) (f n)
            <= ⨅ (_ : t \ s ⊆ ⋃ n, B n), ∑' n, extend (fun s x ↦ μ s) (B n) := by apply iInf_le
          _  = ∑' n, extend (fun s x ↦ μ s) (B n) := by simp [B, hB]; rfl
          _ = ∑' (n : ℕ), μ (B n) := by congr; ext n; exact h B (hans2 A hAS) n
          _ = ∑' (n : ℕ), μ (A n \ s) := by simp [B]
      · push_neg at hAS
        obtain ⟨n, hn⟩ := hAS
        suffices ∞ <= ∑' (i : ℕ), extend (fun s x ↦ μ s) (A i) by {
          rw [@top_le_iff] at this
          rw [this]
          simp
        }
        calc ⊤ = extend (P := Membership.mem S) (fun s x ↦ μ s) (A n) := Eq.symm (extend_eq_top (fun s x ↦ μ s) hn)
          _ <= ∑' n, extend (fun s x ↦ μ s) (A n) := by exact ENNReal.le_tsum n
}


end MeasureTheory

namespace ProductProbabilityMeasure
open MeasureTheory MeasurableSpace Measurable ProductLike



variable {I : Type*}
variable (Ω : ∀(i : I), Type*)
variable [∀i, MeasurableSpace (Ω i)]
variable (J : Set I)
variable (JF : Finset I)

instance : (i : JF) -> MeasurableSpace (JF.restrict Ω i) := by {
  intro i
  rw [show JF.restrict Ω i = Ω i by rfl]
  infer_instance
}
instance : ∀(i : J), MeasurableSpace (J.restrict Ω i) := by {
  intro i
  rw [show J.restrict Ω i = Ω i by rfl]
  infer_instance
}
-- ×_(i ∈ I) Ω_i
abbrev ProductSpace := (i: I) -> Ω i


-- def π (i : I) (ω : ProductSpace Ω) := ω i
def π (J : Set I) : ProductSpace Ω  -> ProductSpace (J.restrict Ω) :=
  fun ω => J.restrict ω

-- variable (i : I)
-- #check π Ω {i}

lemma pi_measurable (J : Set I) : Measurable (π Ω J) := by {
    exact measurable_restrict J
}

-- Ionescu-Tulcea
open ProbabilityMeasure

-- theorem finite_product {I : Type*} [Fintype I] (Ω : I -> Type*) [∀i, MeasurableSpace (Ω i)]
--   (P : (i : I) -> ProbabilityMeasure (Ω i)) :
--   ∃! ℙ : ProbabilityMeasure (ProductSpace Ω), ∀A : (i : I) -> Set (Ω i),
--   ℙ {a : a i ∈ A i} = Π (i : I), P i (A i) := sorry

open ProbabilityTheory
def measurable_equivalence_singleton_product {I : Type*} (α : I -> Type*) (i : I) [∀m, MeasurableSpace (α m)]
  : (∀(j : ({i} : Set I)), α j) ≃ᵐ α i
  := MeasurableEquiv.piUnique (δ' := ({i} : Set I)) (π := fun x => α ↑x)


/- There is no 1 in the kernel composition semigroup, n=0 means choose first kernel -/
def FiniteCompKernelNat
  (n : ℕ)
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  : Kernel (α 0) (∀k : {k|0 < k ∧ k <= n+1}, α k) :=
  if hn : n = 0 then
    by {
      let K' := K 0
      rw [show {k | k <= 0} = {0} by {
        ext; simp [hn]
      }] at K'
      simp at K'
      have h : {k | 0 < k ∧ k <= n + 1} = {1} := by ext; simp [hn]; omega
      rw [h]
      let K'' := change_right K' (measurable_equivalence_singleton_product α 1).symm
      exact change_left K'' (measurable_equivalence_singleton_product α 0)
    }
  else by {
    let n₀ := n - 1
    have hn₀ : n₀ + 1 = n := Nat.succ_pred_eq_of_ne_zero hn
    let K₀ := FiniteCompKernelNat n₀ K
    let K₁ := K n
    simp only [mem_setOf_eq] at K₀
    rw [hn₀] at K₀
    have h : {k | k <= n} = {0} ∪ {k | 0 < k ∧ k <= n} := by ext; simp; omega
    rw [h] at K₁
    have h₀ : Fact (0 ∉ {k : ℕ | 0 < k ∧ k <= n}) := ⟨by simp⟩
    have h₁ : Fact (n+1 ∉ {k : ℕ | 0 < k ∧ k <= n}) := ⟨by simp⟩
    let q : ProdLikeM ((k : ↑{k | 0 < k ∧ k ≤ n + 1}) → α ↑k) ((k : ↑{k | 0 < k ∧ k ≤ n}) → α ↑k) (α (n + 1)) := by {
      rw [show {k| 0 < k ∧ k <= n + 1} = {k | 0 < k ∧ k <= n} ∪ {n+1} by ext; simp; omega]
      infer_instance
    }
    exact compProd K₀ K₁
  }

-- def Measure.change (μ : Measure α) := μ.comapRight


def FiniteCompMeasureKernelNat
  (n : ℕ)
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  : Measure (∀k : {k|k <= n}, α k) :=
  if hn : n = 0 then
    by {
      rw [show {k | k <= n} = {0} by ext; simp[hn]]
      exact μ.comap (measurable_equivalence_singleton_product α 0)
    }
  else by {
    let n₀ := n - 1
    have hn₀ : n₀ + 1 = n := Nat.succ_pred_eq_of_ne_zero hn
    let μ₀ := FiniteCompMeasureKernelNat n₀ μ K
    let K₁ := K n₀
    let μ₁ := μ₀ ⊗ₘ K₁
    rw [show {k| k <= n} = {k | k <= n₀} ∪ {n} by ext; simp; omega]
    have h₁ : Fact (Disjoint {k | k <= n₀} {n}) := ⟨by simp [hn₀]; omega⟩
    let τ : (∀k : ↑({k | k <= n₀} ∪ {n}), α k) ≃ᵐ (∀k : {k | k <= n₀}, α k) × α n := by {
      let τ' := prod_equiv α (J := {k | k<= n₀}) (K:= {n})
      apply MeasurableEquiv.trans τ'.symm
      apply MeasurableEquiv.prodCongr
      exact MeasurableEquiv.refl ((i : ↑{k | k ≤ n₀}) → α ↑i)
      exact measurable_equivalence_singleton_product α n
    }
    rw [<- hn₀] at *
    exact μ₁.comap τ
  }


#check Measure.ext_of_generateFrom_of_iUnion
#check MeasureTheory.ext_of_generate_finite
theorem uniqeness_of_prob_measures [mα : MeasurableSpace α] (μ ν : ProbabilityMeasure α)
  {S : Set (Set α)}
  (hSG : mα = generateFrom S) (hS : IsPiSystem S) (he : ∀s ∈ S, μ s = ν s) : μ = ν := by {
    ext t ht
    induction t, ht using induction_on_inter with
    | h_eq => exact hSG
    | h_inter => exact hS
    | empty => simp
    | basic t' ht' => {
      specialize he t' ht'
      repeat rw [← ennreal_coeFn_eq_coeFn_toMeasure]
      norm_cast
    }
    | compl t' ht' h => rw [prob_compl_eq_one_sub ht', prob_compl_eq_one_sub ht', h]
    | iUnion A pd mA hi => {
      rw [measure_iUnion pd mA, measure_iUnion pd mA]
      exact tsum_congr fun b ↦ hi b
    }
  }


#check extend_iUnion_le_tsum_nat'

theorem extend_iUnion_le_tsum_nat' {α : Type u_1} {P : Set α → Prop}
{m : (s : Set α) → P s → ENNReal}
(s : ℕ → Set α)
  (PU : (∀ (i : ℕ), P (s i)) → P (⋃ i, s i))
  (msU : ∀ (hm : ∀ (i : ℕ), P (s i)), m (⋃ i, s i) (PU hm) ≤ ∑' (i : ℕ), m (s i) (hm i))
  : MeasureTheory.extend m (⋃ i, s i) ≤ ∑' (i : ℕ), MeasureTheory.extend m (s i)
   := by
  by_cases h : ∀ i, P (s i)
  · rw [extend_eq _ (PU h), congr_arg tsum _]
    · apply msU h
    funext i
    apply extend_eq _ (h i)
  · cases' not_forall.1 h with i hi
    exact le_trans (le_iInf fun h => hi.elim h) (ENNReal.le_tsum i)

#check inducedOuterMeasure_eq_extend'

-- theorem inducedOuterMeasure_eq_extend'
-- {α : Type u_1} {P : Set α → Prop} {m : (s : Set α) → P s → ENNReal}
--   {P0 : P ∅} {m0 : m ∅ P0 = 0} (PU : ∀ ⦃f : ℕ → Set α⦄, (∀ (i : ℕ), P (f i)) → P (⋃ i, f i))
--   (msU : ∀ ⦃f : ℕ → Set α⦄ (hm : ∀ (i : ℕ), P (f i)), m (⋃ i, f i) ⋯ ≤ ∑' (i : ℕ), m (f i) ⋯)
--   (m_mono : ∀ ⦃s₁ s₂ : Set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)
--   {s : Set α} (hs : P s) :
--   (inducedOuterMeasure m P0 m0) s = MeasureTheory.extend m s := by {
--     ofFunction_eq s (fun _t => extend_mono' m_mono hs) (extend_iUnion_le_tsum_nat' PU msU)
--   }


#check MeasureTheory.OuterMeasure.toMeasure
#check MeasureTheory.inducedOuterMeasure_caratheodory
theorem existence_of_measures [mα : MeasurableSpace α] (hSG : mα = generateFrom S)
  {μ : AddContent S} (hS : IsSetAlgebra S) (hμ : μ.sAdditive)
  : ∃ ν : Measure α, ∀s ∈ S,  ν s = μ s := by {
    let μ' := μ.toOuterMeasure (hS.empty_mem) (μ.empty')
    have hν : mα <= μ'.caratheodory := by {
      have hSC : ∀s ∈ S, μ'.IsCaratheodory s := by intro s hs; exact addContent_caratheodory_measurable μ hS s hs
      rw [hSG]
      refine (generateFrom_le_iff μ'.caratheodory).mpr ?_
      intro s hs
      exact hSC s hs
    }
    let ν := μ'.toMeasure hν
    have hν : ∀s ∈ S, ν s = μ s := by {
      intro s hs
      have hμμ' : μ s = μ' s := by exact Eq.symm (addContent_outer_measure_equal_on_S μ hS s hs hμ)
      rw [hμμ']
      unfold ν
      simp [OuterMeasure.toMeasure]
      have hsM : MeasurableSet s := by {
        have h := measurableSet_generateFrom hs
        rw [<- hSG] at h
        exact h
      }
      apply Measure.ofMeasurable_apply s hsM
    }
    use ν
  }









def ProductProbabilityMeasure  {I : Type*} [Fintype I] {Ω : I -> Type*}
[∀i, MeasurableSpace (Ω i)] (P : (i : I) -> ProbabilityMeasure (Ω i)) :
  ProbabilityMeasure (ProductSpace Ω) := sorry


theorem existence_infinite_product_probability_measure :
∀(P : (i : I) -> ProbabilityMeasure (Ω i)),
  ∃! PP : ProbabilityMeasure (ProductSpace Ω), ∀(J : Finset I),
   ProbabilityMeasure.map ℙ (aemeasurable (measurable_restrict J))
    = ProductProbabilityMeasure (J.restrict P) := by {
      sorry
  }








  --  (show AEMeasurable (π Ω J) (μ := ↑ℙ)
  --  by {
  --   -- exact aemeasurable (pi_measurable Ω J)
  --   exact aemeasurable (measurable_restrict (J : Set I))
  --   }
    -- )

-/
