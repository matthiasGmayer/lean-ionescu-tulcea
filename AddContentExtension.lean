import Mathlib

set_option autoImplicit true
open Function Set Classical ENNReal

noncomputable section

/-!
This file contains the Carathéodory extension theorem, which allows to extend a content defined on
a set algebra to a σ-algebra.
-/

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

variable {α : Type*} {C : Set (Set α)} [mα : MeasurableSpace α] (μ : AddContent C)

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

variable (hAlg : IsSetAlgebra C)
open MeasureTheory AddContent OuterMeasure Membership ENNReal MeasurableSpace

def sAdditive : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ C) -> (⋃ i, A i ∈ C) → Pairwise (Disjoint on A) →
    μ (⋃ i, A i) = ∑' i, μ (A i)

def sSubAdditive  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ C) -> (⋃ i, A i ∈ C) →
    μ (⋃ i, A i) <= ∑' i, μ (A i)

def sContinuousFromBelow  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ C) ->
  (hmono : Monotone A) ->
  (⋃n, A n ∈ C) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 (μ (⋃n, A n)))

def sContinuousFromAbove  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ C) -> (μ (A 0) < ∞) ->
  (hmono : Antitone A) ->
  (⋂n, A n ∈ C) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 (μ (⋂n, A n)))

def sContinuousInEmpty  : Prop :=
  ∀⦃A : ℕ → Set α⦄, (∀ i, (A i) ∈ C) -> (μ (A 0) < ∞) ->
  (hmono : Antitone A) ->
  (⋂n, A n = ∅) ->
  Tendsto (λ n => μ (A n)) atTop (𝓝 0)


lemma Setalgebra_finite_union (α : Type*) (C : Set (Set α)) (hC : IsSetAlgebra C)
  (F : Finset ι) (f : F -> Set α) (h : ∀i, f i ∈ C) : ⋃ i, f i ∈ C := by {
    induction F using Finset.induction_on with
    | empty => simp; exact hC.empty_mem
    | insert nmem hI => {
      rename_i s F
      rw [show (⋃ i : ↑(insert s F), f i) = f ⟨s, by exact Finset.mem_insert_self s F⟩  ∪ (⋃ i : F, f ⟨i, by simp⟩ ) by {
        ext x
        simp_all only [Subtype.forall, Finset.mem_insert, mem_iUnion, Subtype.exists, mem_union]
        apply Iff.intro
        · intro a
          obtain ⟨w, h_1⟩ := a
          obtain ⟨w_1, h_1⟩ := h_1
          cases w_1 with
          | inl h_2 =>
            subst h_2
            simp_all only [true_or]
          | inr h_3 =>
            apply Or.inr
            apply Exists.intro
            · apply Exists.intro
              · exact h_1
              · simp_all only
        · intro a
          cases a with
          | inl h_1 =>
            apply Exists.intro
            · apply Exists.intro
              · exact h_1
              · simp_all only [or_false]
          | inr h_2 =>
            obtain ⟨w, h_1⟩ := h_2
            obtain ⟨w_1, h_1⟩ := h_1
            apply Exists.intro
            · apply Exists.intro
              · exact h_1
              · simp_all only [or_true]
      }]
      apply hC.union_mem
      exact h ⟨s, Finset.mem_insert_self s F⟩
      apply hI
      intro x
      apply h
    }
  }

include hAlg in
omit mα in
lemma sAdditive_implies_sSubAdditive : μ.sAdditive -> μ.sSubAdditive := by {
  unfold sAdditive sSubAdditive
  intro h A hA hAU
  let B n := A n \ ⋃ i : Finset.range n, A i
  have hB : ∀n, B n ∈ C := by {
    intro n
    unfold B
    refine IsSetRing.diff_mem ?_ (hA n) ?_
    exact IsSetAlgebra.isSetRing hAlg
    exact Setalgebra_finite_union α C hAlg (Finset.range n) (fun i ↦ A ↑i) fun i ↦ hA ↑i
  }
  have hB' : ⋃n, B n = ⋃n, A n := by {
    ext x
    unfold B
    simp
    constructor <;> intro h
    · obtain ⟨n, hn⟩ := h
      use n
      exact hn.1
    · use Nat.find h
      simp
      constructor
      · exact Nat.find_spec h
      · intro y hy
        exact hy y (by rfl)
  }
  have hBunionS : ⋃n, B n ∈ C := by {
    rw [hB']
    exact hAU
  }
  have hBsub n : B n ⊆ A n := by {
    unfold B
    intro x hx
    simp_all only [mem_diff, mem_iUnion, Subtype.exists, Finset.mem_range, exists_prop, not_exists, not_and, B]
  }
  have hBdisjoint : Pairwise (Disjoint on B) := by {
    intro i j hij
    unfold onFun
    wlog hle : i <= j generalizing i j hij
    {
      specialize @this j i (hij.symm) (by omega)
      exact Disjoint.symm this
    }
    have hlt : i < j := by omega
    suffices Disjoint (A i) (B j) by exact disjoint_of_subset (hBsub i) (fun ⦃a⦄ a ↦ a) this
    rw [disjoint_iff_inter_eq_empty]
    unfold B
    ext x
    simp
    intro hx h
    use i
  }
  rw [<- hB']
  rw [h hB hBunionS hBdisjoint]
  gcongr
  rename_i n
  refine addContent_mono ?_ (hB n) (hA n) (hBsub n)
  exact SetAlgebraIsSetSemiRing hAlg
}
-- lemma sSubAdditive_implies_sAdditive : μ.sSubAdditive -> μ.sAdditive := sorry

-- lemma sAdditive_implies_sContinuousFromBelow : μ.sAdditive -> μ.sContinuousFromBelow := sorry
-- lemma sContinuousFromBelow_implies_sAdditive : μ.sContinuousFromBelow -> μ.sAdditive := sorry

-- lemma sContinuousFromAbove_implies_sContinuousInEmpty : μ.sContinuousFromAbove -> μ.sContinuousInEmpty := sorry
-- lemma sContinuousInEmpty_finite_implies_sContinuousFromAbove :  μ.sContinuousInEmpty -> μ.sContinuousFromAbove := by {
--   unfold sContinuousInEmpty sContinuousFromAbove
--   intro μbounded h
-- }

include hAlg in
omit mα in
lemma bounded_complement (huniv : univ ∈ C) (bounded : μ univ < ∞) {A : Set α} (hA : A ∈ C) : μ (Aᶜ) = μ univ - μ A := by {
  refine ENNReal.eq_sub_of_add_eq' ?_ ?_
  exact LT.lt.ne_top bounded
  have hAAc : A ∪ Aᶜ = univ := by {
    rw [<- show A ∪ Aᶜ = univ by {
      ext x
      simp
    }]
  }
  have hdisjoint : Disjoint A Aᶜ := by exact disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a ↦ a
  have hAc : Aᶜ ∈ C := by {
    rw [@compl_eq_univ_diff]
    exact IsSetAlgebra.diff_mem hAlg huniv hA
  }
  rw [<- hAAc]
  rw [add_comm]
  symm
  exact addContent_union (by exact IsSetAlgebra.isSetRing hAlg) hA hAc hdisjoint (m := μ)
}

-- include hAlg in
-- omit mα in
-- lemma EReal.bounded_complement (huniv : univ ∈ C) (bounded : μ univ < ∞) {A : Set α} (hA : A ∈ C) : μ (Aᶜ) = μ univ - (μ A : EReal) := by {
-- }


lemma EReal_cast_sub (a b : ℝ≥0∞) (hab : a >= b) (hb : b < ∞)
: (a : EReal) - (b : EReal) = (a - b : ℝ≥0∞) := by {
  refine Eq.symm (toEReal_sub ?_ hab)
  exact LT.lt.ne_top hb
}

include hAlg in
omit mα in
lemma sContinuousFromBelow_implies_sAdditive : μ.sContinuousFromBelow -> μ.sAdditive := by {
  unfold sContinuousFromBelow sAdditive
  intro h A hA hAU hAdisjoint
  let B n := ⋃ i : Finset.range n, A i
  have hBS n : B n ∈ C := by {
    unfold B
    exact Setalgebra_finite_union α C hAlg (Finset.range n) (fun i ↦ A ↑i) fun i ↦ hA ↑i
  }
  have hBmono : Monotone B := by {
    intro n m hnm
    unfold B
    intro x
    simp
    intro y hy hx
    use y
    constructor
    · omega
    · exact hx
  }
  have hBU : ⋃n, B n = ⋃n, A n := by {
    ext x
    simp
    unfold B
    constructor <;> intro h
    · obtain ⟨n, hn⟩ := h
      simp only [mem_iUnion, Subtype.exists, Finset.mem_range, exists_prop] at hn
      obtain ⟨i, hi⟩ := hn
      use i
      exact hi.2
    · obtain ⟨n, hn⟩ := h
      simp only [mem_iUnion, Subtype.exists, Finset.mem_range, exists_prop]
      use n + 1
      use n
      simp only [lt_add_iff_pos_right, zero_lt_one, hn, and_self]
  }
  rw [<- hBU]
  rw [@ENNReal.tsum_eq_limsup_sum_nat]
  rw [show (fun n ↦ ∑ i ∈ Finset.range n, μ (A i)) = fun n => μ (B n) by {
    ext n
    unfold B
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, iUnion_of_empty, addContent_empty]
    | succ n hn => {
      rw [Finset.sum_range_succ, hn]
      rw [show (⋃ i:Finset.range (n+1), A i) = A n ∪ ⋃ i : Finset.range n, A i by {
        ext x
        simp only [mem_iUnion, Subtype.exists, Finset.mem_range, exists_prop, mem_union]
        constructor <;> intro h'
        · obtain ⟨i, hi⟩ := h'
          by_cases he : i = n
          left
          rw [he] at hi
          exact hi.2
          right
          use i
          constructor
          · omega
          · exact hi.2
        · obtain (h'|h') := h'
          use n
          constructor
          · omega
          · exact h'
          obtain ⟨i, hi⟩ := h'
          use i
          constructor
          · omega
          · exact hi.2
      }]
      rw [addContent_union, add_comm]
      exact IsSetAlgebra.isSetRing hAlg
      exact hA n
      exact Setalgebra_finite_union α C hAlg (Finset.range n) (fun i ↦ A ↑i) fun i ↦ hA ↑i
      rw [disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro h y hn
      have hxn: y ≠ n := by omega
      by_contra hcontra
      have hhh : x ∈ A y ∩ A n := by simp_all only [ne_eq, mem_inter_iff, and_self, B]
      specialize hAdisjoint hxn
      unfold onFun at hAdisjoint
      rw [disjoint_iff_inter_eq_empty] at hAdisjoint
      rw [hAdisjoint] at hhh
      contradiction
    }
  }]

  specialize h hBS hBmono (by rwa [hBU])
  exact Eq.symm (Tendsto.limsup_eq h)
}

include hAlg in
omit mα in
lemma sContinuousFromAbove_implies_sContinuousFromBelow : univ ∈ C -> μ univ < ∞ -> μ.sContinuousFromAbove -> μ.sContinuousFromBelow := by {
  unfold sContinuousFromAbove sContinuousFromBelow
  intro huniv hbounded h A hAS hAmono hAU
  let A' n := (A n)ᶜ
  have hA' : ∀n, A' n ∈ C := by {
    intro n
    unfold A'
    exact hAlg.compl_mem (hAS n)
  }
  have hbounded' : μ (A' 0) < ∞ := by {
    calc μ (A' 0) <= μ univ := by apply addContent_mono (SetAlgebraIsSetSemiRing hAlg) (hA' 0) huniv (by simp)
    _ < ∞ := by exact hbounded
  }
  have hA'antitone : Antitone A' := by {
    intro n m hnm
    unfold A'
    simp
    exact hAmono hnm
  }
  have hAI : ⋂n, A' n = (⋃n, A n)ᶜ := by {
    unfold A'
    rw [← @compl_iUnion]
  }
  specialize h hA' hbounded' hA'antitone (by rw [hAI]; exact hAlg.compl_mem hAU)
  rw [hAI] at h
  unfold A' at h
  rw [bounded_complement μ hAlg huniv hbounded hAU] at h
  conv at h => arg 1; intro n; rw [bounded_complement μ hAlg huniv hbounded (hAS n)]
  let f := λ r => μ univ - r
  have fidem x (hx : x <= μ univ) : f (f x) = x := by {
    unfold f
    refine ENNReal.sub_sub_cancel ?_ hx
    exact LT.lt.ne_top hbounded
  }
  have fidemset {s} (hs : s ∈ C) : f (f (μ s)) = μ s := by {
    apply fidem
    apply addContent_mono (SetAlgebraIsSetSemiRing hAlg) hs (huniv) (by simp)
  }
  have hf : Continuous f := by {
    unfold f
    refine ENNReal.continuous_sub_left (LT.lt.ne_top hbounded)
  }
  rw [show (fun n => μ univ - μ (A n)) = fun x => f ((fun n => μ (A n)) x) by rfl] at h
  rw [show (μ univ - μ (⋃n, A n)) = f (μ (⋃n, A n))by rfl] at h
  let hc := hf.tendsto (f (μ (⋃n, A n)))
  have hhh := Tendsto.comp hc h
  simp only at hhh
  rw [show (f ∘ fun n => f (μ (A n))) = fun n => μ (A n) by {
    ext n
    simp
    apply fidemset
    exact hAS n
  }] at hhh
  rwa [fidemset hAU] at hhh
}
-- lemma sAdditive_implies_sContinuousInEmpty : μ.sAdditive -> μ.sContinuousInEmpty := sorry

include hAlg in
omit mα in
lemma sContinuousInEmpty_implies_ContinuousFromAbove : μ.sContinuousInEmpty -> μ.sContinuousFromAbove := by {
  unfold sContinuousInEmpty sContinuousFromAbove
  intro h A hAS hbounded hAmono hAU
  let B n := A n \ (⋂n, A n)
  have hB : ∀n, B n ∈ C := by {
    unfold B
    exact fun n ↦ IsSetAlgebra.diff_mem hAlg (hAS n) hAU
  }
  have hBantitone : Antitone B := by {
    intro n m hnm
    unfold B
    exact sdiff_le_sdiff (hAmono hnm) fun ⦃a⦄ a ↦ a
  }
  have hB0 : μ (B 0) < ⊤ := by {
    calc μ (B 0) <= μ (A 0) := by {
      apply addContent_mono
      exact SetAlgebraIsSetSemiRing hAlg
      exact hB 0
      exact hAS 0
      exact diff_subset
    }
    _ < ⊤ := by exact hbounded
  }
  have hBU : ⋂n, B n = ∅ := by {
    unfold B
    calc ⋂ n, A n \ ⋂ n, A n = ⋂ n, A n ∩ (⋂ n, A n)ᶜ := by rfl
    _ = (⋂ n, A n) ∩ (⋂ n, A n)ᶜ := by exact Eq.symm (iInter_inter (⋂ n, A n)ᶜ A)
    _ = ∅ := by exact inter_compl_self (⋂ n, A n)
  }
  specialize h hB hB0 hBantitone hBU

  let f := λ r => μ (⋂n, A n) + r
  have hf : Continuous f := by {
    exact continuous_add_left (μ (⋂ n, A n))
  }
  let hf' := hf.tendsto 0
  let hhh := Tendsto.comp hf' h
  unfold f at hhh
  simp at hhh
  have hg : ((fun r ↦ μ (⋂ n, A n) + r) ∘ fun n ↦ μ (B n)) = fun n => μ (A n) := by {
    ext x
    simp [B]
    nth_rw 2 [show A x = (⋂n, A n) ∪ A x ∩  (⋂ n, A n)ᶜ by {
      ext y
      constructor <;> intro h
      · by_cases h' : y ∈ ⋂ n, A n
        · left
          exact h'
        · right
          simp at h'
          simp
          constructor
          · exact h
          · exact h'
      ·
        simp_all only [compl_iInter, mem_union, mem_iInter, mem_inter_iff, mem_iUnion, mem_compl_iff, B]
        cases h with
        | inl h_2 => simp_all only
        | inr h_3 => simp_all only
    }]
    rw [addContent_union]
    rfl
    exact IsSetAlgebra.isSetRing hAlg
    exact hAU
    exact hB x
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp
    intros
    simp_all
  }
  rwa [hg] at hhh
}

include hAlg in
omit mα in
lemma sContinuousInEmpty_finite_implies_sAdditive : univ ∈ C -> μ univ < ∞ -> μ.sContinuousInEmpty -> μ.sAdditive := by {
  intros huniv hbounded h
  apply sContinuousFromBelow_implies_sAdditive μ
  exact hAlg
  apply sContinuousFromAbove_implies_sContinuousFromBelow μ hAlg huniv hbounded
  apply sContinuousInEmpty_implies_ContinuousFromAbove μ hAlg h
}


def toOuterMeasure :=
    inducedOuterMeasure (λ s : Set α => λ _ : s ∈ C => μ s)


lemma outer_measure_equal_on_S (s : Set α) (hs : s ∈ C) (hμ : μ.sAdditive)
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
          extend (P := mem C) (fun s x ↦ μ s) (f i) := by apply iInf_le
        _ =  ∑' (i : ℕ), extend (P := mem C) (fun s x ↦ μ s) (f i) := by simp [hf]
        _ =  μ s := by {
          unfold f
          simp [apply_ite, extend_eq (fun s x => μ s)]
          rw [show extend (P := mem C) (fun s x => μ s) s = μ s by {
            exact extend_eq (fun s x ↦ μ s) hs
          }]
          rw [show extend (P := mem C) (fun s x => μ s) ∅ = 0 by {
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
        by_cases hAS : ∀n, A n ∈ C
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
            have h : A n ∩ s ∈ C := by exact IsSetAlgebra.inter_mem hAlg hAS hs
            have h' : A n ∩ s ⊆ A n := by exact inter_subset_left
            have hA : IsSetSemiring C := by exact SetAlgebraIsSetSemiRing hAlg
            apply addContent_mono hA h hAS h'
          }
          _ = ∑' n, extend (fun s x ↦ μ s) (A n) := by {
            congr; ext n
            exact Eq.symm (extend_eq (fun s x ↦ μ s) (hAS n))
          }
        ·
          suffices ∞ <= ∑' n, extend (P := mem C) (fun s x ↦ μ s) (A n) by {
            rw [@top_le_iff] at this
            rw [this]
            simp
          }
          push_neg at hAS
          obtain ⟨n, hn⟩ := hAS
          calc ∞ = extend (P := mem C) (fun s x => μ s) (A n) := by {
            unfold extend
            simp [hn]
          }
          _ <= ∑' n, extend (fun s x ↦ μ s) (A n) := by exact ENNReal.le_tsum n
  }

omit mα in
lemma caratheodory_measurable (s : Set α) (hs : s ∈ C)
  : (μ.toOuterMeasure hAlg.empty_mem μ.empty').IsCaratheodory s := by {
    unfold OuterMeasure.IsCaratheodory
    intro t
    have htsDisjoint : Disjoint (t ∩ s) (t \ s) := by exact Disjoint.symm disjoint_sdiff_inter
    have htsUnion : t ∩ s ∪ t \ s = t := by exact inter_union_diff t s
    have hSetRing : IsSetRing C := by exact IsSetAlgebra.isSetRing hAlg
    -- generalize_proofs hem μem
    apply le_antisymm
    · apply measure_le_inter_add_diff
    · unfold AddContent.toOuterMeasure inducedOuterMeasure OuterMeasure.ofFunction
      rw [← OuterMeasure.measureOf_eq_coe]
      simp
      intro A hA
      have h: ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ C) (n : ℕ),
        extend (P := Membership.mem C) (fun s x => μ s) (A n) = μ (A n) := by {
          intro A hAS n;
          exact extend_eq (fun s x ↦ μ s) (hAS n)
        }
      by_cases hAS : ∀n, A n ∈ C
      · have hans : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ C) n, A n ∩ s ∈ C := by intro A hAS n; exact IsSetRing.inter_mem hSetRing (hAS n) hs
        have hans2 : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ C) n, A n \ s ∈ C := by intro A hAS n; exact hSetRing.diff_mem (hAS n) hs
        have hansU : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ C) n, A n ∩ s ∪ A n \ s = A n := by intro A hAS n; exact inter_union_diff (A n) s
        have hansD : ∀(A : ℕ -> Set α) (hAS : ∀n, A n ∈ C) n, Disjoint (A n ∩ s) (A n \ s) := by {
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
          have hBS : ∀n, B n ∈ C := by intro n; exact hans A hAS n
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
          have hBS : ∀n, B n ∈ C := by intro n; exact hans2 A hAS n
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
        calc ⊤ = extend (P := Membership.mem C) (fun s x ↦ μ s) (A n) := Eq.symm (extend_eq_top (fun s x ↦ μ s) hn)
          _ <= ∑' n, extend (fun s x ↦ μ s) (A n) := by exact ENNReal.le_tsum n
}


def toMeasure (hSG : mα = generateFrom C) (hS : IsSetAlgebra C) (hμ : μ.sAdditive) : Measure α := by {
  let μ' := μ.toOuterMeasure (hS.empty_mem) (μ.empty')
  have hν : mα <= μ'.caratheodory := by {
    have hSC : ∀s ∈ C, μ'.IsCaratheodory s := by intro s hs; exact caratheodory_measurable μ hS s hs
    rw [hSG]
    refine (generateFrom_le_iff μ'.caratheodory).mpr ?_
    intro s hs
    exact hSC s hs
  }
  let ν := μ'.toMeasure hν
  exact ν
}

lemma toMeasure_eq_on_S (hSG : mα = generateFrom C) (hS : IsSetAlgebra C) (hμ : μ.sAdditive)
  (s : Set α) (hs : s ∈ C) : μ.toMeasure hSG hS hμ s = μ s := by {
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

theorem existence_of_measures (hSG : mα = generateFrom C)
  {μ : AddContent C} (hS : IsSetAlgebra C) (hμ : μ.sAdditive)
  : ∃ ν : Measure α, ∀s ∈ C,  ν s = μ s := by {
    use μ.toMeasure hSG hS hμ
    intro s hs
    exact toMeasure_eq_on_S μ hSG hS hμ s hs
  }
