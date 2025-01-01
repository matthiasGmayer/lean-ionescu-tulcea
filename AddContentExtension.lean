import Mathlib

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal

/- recommended whenever you define anything new. -/
noncomputable section

namespace MeasureTheory

theorem SetAlgebraIsSetSemiRing (h1 : IsSetAlgebra S) : IsSetSemiring S := by {
  refine IsSetRing.isSetSemiring ?_
  exact IsSetAlgebra.isSetRing h1
}

theorem SetAlgebraFiniteUnion (S : Set (Set α)) (hS : IsSetAlgebra S) (I : Finset (Set α)) (hI : ∀i ∈ I, i ∈ S) :
  ⋃₀ I ∈ S := by {
    induction I using Finset.induction with
    | empty => simp; exact hS.empty_mem
    | insert ha hI => {
      rename_i h a hA
      simp [*] at *
      specialize hA hI.2
      exact hS.union_mem hI.1 hA
    }
  }
open Filter Topology

variable {α : Type*} {S : Set (Set α)} [mα : MeasurableSpace α] (μ : AddContent S)

namespace AddContent


def mk' (C : Set (Set α)) (hAlg : IsSetAlgebra C) (toFun : Set α -> ℝ≥0∞) (empty' : toFun ∅ = 0)
  (additivity : ∀s ∈ C, ∀t ∈ C, (Disjoint s t) -> toFun (s ∪ t) = toFun s + toFun t) : AddContent C where
  toFun := toFun
  empty' := empty'
  sUnion' := by {
    intro I hI hpwdf hclear
    clear hclear
    induction I using Finset.induction_on with
    | empty => simp [empty']
    | insert hx hI=> {
      rename_i s I h
      simp [*] at *
      have hsub := (subset_insert s I)
      have hI' : ↑I ⊆ C := Subset.trans hsub hI
      have hpwd' : (I : Set (Set α)).PairwiseDisjoint id := PairwiseDisjoint.subset hpwdf hsub
      specialize h hI' hpwd'
      rw [<- h]
      have hUI : ⋃₀ ↑I ∈ C := SetAlgebraFiniteUnion C hAlg I hI'
      have hs : s ∈ C := hI (mem_insert s ↑I)
      have hd : Disjoint s (⋃₀ ↑I) := by {
        rw [@disjoint_sUnion_right]
        intro t ht
        unfold PairwiseDisjoint Set.Pairwise  at hpwdf
        specialize hpwdf (hsub ht) (mem_insert s ↑I) (ne_of_mem_of_not_mem ht hx)
        rw [show (Disjoint on id) t s = Disjoint (id t) (id s) from rfl] at hpwdf
        simp at hpwdf
        exact Disjoint.symm hpwdf
      }
      apply additivity s hs (⋃₀ ↑I) hUI hd
    }
  }


omit mα in
@[simp]
lemma mk'_on_C (C : Set (Set α)) (hAlg : IsSetAlgebra C) (toFun : Set α -> ℝ≥0∞) (empty' : toFun ∅ = 0)
  (additivity : ∀s ∈ C, ∀t ∈ C, (Disjoint s t) -> toFun (s ∪ t) = toFun s + toFun t)
  (s : Set α)
  : mk' C hAlg toFun empty' additivity s = toFun s := by rfl

variable (hAlg : IsSetAlgebra S)
open MeasureTheory AddContent OuterMeasure Membership ENNReal MeasurableSpace

def sAdditive : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (⋃ i, A i ∈ S) → Pairwise (Disjoint on A) →
    μ (⋃ i, A i) = ∑' i, μ (A i)

def sSubAdditive  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (⋃ i, A i ∈ S) →
    μ (⋃ i, A i) <= ∑' i, μ (A i)

def sContinuousFromBelow  : Prop :=
  ∀⦃A : ℕ → Set α⦄ {B : Set α }, (∀ i, (A i) ∈ S) -> (B ∈ S) ->
  (Tendsto A atTop (𝓝[≤] B)) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 (μ B))

def sContinuousFromAbove  : Prop :=
  ∀⦃A : ℕ → Set α⦄ (B : Set α), (∀ i, (A i) ∈ S) -> (B ∈ S) -> (μ (A 0) < ∞) ->
  (Tendsto A atTop (𝓝[≥] B)) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 (μ B))

def sContinuousInEmpty  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ S) -> (μ (A 0) < ∞) ->
  (Tendsto A atTop (𝓝 ∅)) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 0)

include hAlg in
lemma sAdditive_implies_sSubAdditive : μ.sAdditive -> μ.sSubAdditive := by {
  unfold sAdditive sSubAdditive
  intro h A hA hAU
  sorry
}
lemma sSubAdditive_implies_sAdditive : μ.sSubAdditive -> μ.sAdditive := sorry

lemma sAdditive_implies_sContinuousFromBelow : μ.sAdditive -> μ.sContinuousFromBelow := sorry
lemma sContinuousFromBelow_implies_sAdditive : μ.sContinuousFromBelow -> μ.sAdditive := sorry

lemma sContinuousFromAbove_implies_sContinuousInEmpty : μ.sContinuousFromAbove -> μ.sContinuousInEmpty := sorry
lemma sContinuousInEmpty_implies_sContinuousFromAbove : μ.sContinuousInEmpty -> μ.sContinuousFromAbove := sorry

lemma sAdditive_implies_sContinuousInEmpty : μ.sAdditive -> μ.sContinuousInEmpty := sorry

lemma sContinuousInEmpty_finite_implies_sAdditive : μ.sContinuousInEmpty ∧ μ univ < ∞ -> μ.sAdditive := sorry


def toOuterMeasure :=
    inducedOuterMeasure (λ s : Set α => λ _ : s ∈ S => μ s)


lemma outer_measure_equal_on_S (s : Set α) (hs : s ∈ S) (hμ : μ.sAdditive)
  : μ.toOuterMeasure hAlg.empty_mem μ.empty' s = μ s := by {
      -- generalize h : μ.toOuterMeasure hAlg.empty_mem μ.empty' = ν
      let ν := μ.toOuterMeasure hAlg.empty_mem μ.empty'
      suffices ν s <= μ s ∧ ν s >= μ s by exact le_antisymm this.1 this.2
      constructor
      ·
        unfold ν toOuterMeasure inducedOuterMeasure OuterMeasure.ofFunction
        rw [← @OuterMeasure.measureOf_eq_coe]
        simp
        let f : ℕ -> Set α := fun n => if n = 0 then s else ∅
        have hf : ⋃ i, f i = s := by ext; simp [f]
        calc
        ⨅ f : ℕ -> Set α, ⨅ (_ : s ⊆ ⋃ i, f i), ∑' (i : ℕ), extend (fun s x ↦ μ s) (f i)
        <= ⨅ (_ : s ⊆ ⋃ i, f i), ∑' (i : ℕ),
          extend (P := mem S) (fun s x ↦ μ s) (f i) := by apply iInf_le
        _ =  ∑' (i : ℕ), extend (P := mem S) (fun s x ↦ μ s) (f i) := by simp [hf]
        _ =  μ s := by {
          unfold f
          simp [apply_ite, extend_eq (fun s x => μ s)]
          rw [show extend (P := mem S) (fun s x => μ s) s = μ s by {
            exact extend_eq (fun s x ↦ μ s) hs
          }]
          rw [show extend (P := mem S) (fun s x => μ s) ∅ = 0 by {
            have h := extend_eq (fun s x ↦ μ s) hAlg.empty_mem
            simp at h
            exact h
          }]
          simp
        }
      ·
        rw [ge_iff_le]
        unfold ν toOuterMeasure inducedOuterMeasure OuterMeasure.ofFunction
        rw [← OuterMeasure.measureOf_eq_coe]
        simp
        intro A hA
        by_cases hAS : ∀n, A n ∈ S
        ·
          calc μ s = μ ((⋃n, A n) ∩ s) := by rw [inter_eq_self_of_subset_right hA]
          _ = μ (⋃ n, A n ∩ s) := by rw [iUnion_inter]
          _ <= ∑' n, μ (A n ∩ s) := by {
            apply sAdditive_implies_sSubAdditive μ hAlg hμ
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
          suffices ∞ <= ∑' n, extend (P := mem S) (fun s x ↦ μ s) (A n) by {
            rw [@top_le_iff] at this
            rw [this]
            simp
          }
          push_neg at hAS
          obtain ⟨n, hn⟩ := hAS
          calc ∞ = extend (P := mem S) (fun s x => μ s) (A n) := by {
            unfold extend
            simp [hn]
          }
          _ <= ∑' n, extend (fun s x ↦ μ s) (A n) := by exact ENNReal.le_tsum n
  }

omit mα in
lemma caratheodory_measurable (s : Set α) (hs : s ∈ S)
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


def toMeasure (hSG : mα = generateFrom S) (hS : IsSetAlgebra S) (hμ : μ.sAdditive) : Measure α := by {
  let μ' := μ.toOuterMeasure (hS.empty_mem) (μ.empty')
  have hν : mα <= μ'.caratheodory := by {
    have hSC : ∀s ∈ S, μ'.IsCaratheodory s := by intro s hs; exact caratheodory_measurable μ hS s hs
    rw [hSG]
    refine (generateFrom_le_iff μ'.caratheodory).mpr ?_
    intro s hs
    exact hSC s hs
  }
  let ν := μ'.toMeasure hν
  have hν : ∀s ∈ S, ν s = μ s := by {
    intro s hs
    have hμμ' : μ s = μ' s := by exact Eq.symm (outer_measure_equal_on_S μ hS s hs hμ)
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
  exact ν
}

lemma toMeasure_eq_on_S (hSG : mα = generateFrom S) (hS : IsSetAlgebra S) (hμ : μ.sAdditive)
  (s : Set α) (hs : s ∈ S) : μ.toMeasure hSG hS hμ s = μ s := by {
    unfold AddContent.toMeasure
    simp
    generalize_proofs h1 h2
    have hμμ' : μ s = μ.toOuterMeasure h1 h2 s := by exact Eq.symm (outer_measure_equal_on_S μ hS s hs hμ)
    rw [hμμ']
    simp [OuterMeasure.toMeasure]
    have hsM : MeasurableSet s := by {
      have h := measurableSet_generateFrom hs
      rw [<- hSG] at h
      exact h
    }
    apply Measure.ofMeasurable_apply s hsM
  }

theorem existence_of_measures (hSG : mα = generateFrom S)
  {μ : AddContent S} (hS : IsSetAlgebra S) (hμ : μ.sAdditive)
  : ∃ ν : Measure α, ∀s ∈ S,  ν s = μ s := by {
    use μ.toMeasure hSG hS hμ
    intro s hs
    exact toMeasure_eq_on_S μ hSG hS hμ s hs
  }
