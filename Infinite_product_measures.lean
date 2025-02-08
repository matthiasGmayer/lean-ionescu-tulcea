/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea
import IonescuTulcea.finiteCompProd
import IonescuTulcea.finiteCompProdProps
import IonescuTulcea.strong_rec
import IonescuTulcea.AddContentExtension
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal ProductProbabilityMeasure IndexedFamilies

/- recommended whenever you define anything new. -/
open Filter Topology
noncomputable section


/- Now write definitions and theorems. -/

namespace ProductProbabilityMeasure
open MeasureTheory MeasurableSpace Measurable ProductLike ProductProbabilityMeasure

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory ENNReal

-- #check biSup_sup_biSup
-- lemma biSup_sup' {α : Type*} {I : Type*} {s : I -> α}
--   [CompleteLattice α]
--   {J K L : Finset I}
--   (hJKL : K ∪ L = J)
--   : ⨆ i ∈ J, s i = (⨆ i ∈ K, s i) ⊔ (⨆ i ∈ L, s i) := by {
--     subst hJKL
--     rw [← @Finset.iSup_union]
--     simp
-- }
lemma biUnion_union' {α : Type*} {I : Type*} {s : I -> Set α}
  {J K L : Finset I}
  (hJKL : K ∪ L = J)
  : ⋃ i ∈ J, s i = (⋃ i ∈ K, s i) ∪ ⋃ i ∈ L, s i := by {
    aesop
}

lemma Surj_emp (f : α -> β) (hf : Surjective f) (hS : f ⁻¹' S = ∅) : S = ∅  := by {
  rw [show ∅ = f ⁻¹' ∅ by exact rfl] at hS
  exact (preimage_eq_preimage hf).mp (id (Eq.symm hS)).symm
}

lemma Surj_disjoint (f : α -> β) (hf : Surjective f) (hab : Disjoint (f ⁻¹' a) (f ⁻¹' b))
  : Disjoint a b := by {
    exact Disjoint.of_preimage hf hab
  }

lemma restrict_union (α : I -> Type*)
[∀i, Inhabited (α i)]
{J : Set I}
{s t r : Set (∀j : J, α j)}
  (h : (J.restrict ⁻¹' s) ∪ (J.restrict ⁻¹' t) = (J.restrict ⁻¹' r))
  : s ∪ t = r
   := by {
    ext x
    have hh := Subtype.exists_pi_extension x
    have hy := choose_spec hh
    let y := choose hh
    rw [show choose hh = y from rfl] at *
    have h' : J.restrict y = x := by {
      ext i
      simp
      apply_fun (· i) at hy
      simp at hy
      assumption
    }
    have hxy s : x ∈ s <-> y ∈ J.restrict ⁻¹' s := by simp [h']
    rw [hxy, hxy, <- h]
    simp
  }

lemma restrict_surjective (α : I -> Type*) [∀i, Nonempty (α i)] {J : Set I} : Surjective (J.restrict (π := α)) := by {
  -- unfold Surjective
  intro b
  exact Subtype.exists_pi_extension b
}

def MeasureKernelSequenceContent
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  : AddContent (cylinders α) := AddContent.mk'
    (C := cylinders α)
    (hAlg := cylinders_SetAlgebra α)
    (toFun := fun s =>
      if h : ∃n, s ∈ cylinder_n α n then
        have h' := Nat.find_spec h
        let n := Nat.find h
        let T := choose h'
        FiniteCompMeasureKernelNat μ K n T
      else 0)
    (empty' := by {
      simp
      intro n h
      generalize_proofs h1 h2
      have ⟨_,h3⟩ := choose_spec h2
      have h' : choose h2 = ∅ := by {
        exact Surj_emp {x | x ≤ Nat.find h1}.restrict (restrict_surjective _) h3
      }
      rw [h']
      simp only [measure_empty]
    })
    (additivity := by {
      intro s hs t ht hst
      have hsut : s ∪ t ∈ cylinders α := by apply (cylinders_SetAlgebra α).union_mem hs ht
      unfold cylinders at hs ht hsut
      simp only [mem_iUnion] at hs ht hsut
      simp only [hsut, ↓reduceDIte, coe_setOf, mem_setOf_eq, hs, ht]
      generalize_proofs hTnm hTn hTm

      let k := Nat.find hs ⊔ Nat.find ht ⊔ Nat.find hsut
      have hnk : Nat.find hs <= k := by omega
      have hmk : Nat.find ht <= k := by omega
      have hnmk : Nat.find hsut <= k := by omega
      rw [<- Measure.finiteCompLift μ K hnk, <- Measure.finiteCompLift μ K hmk, <- Measure.finiteCompLift μ K hnmk]
      generalize_proofs gnm gn gm
      simp only [coe_setOf, mem_setOf_eq]
      repeat rw [Measure.map_apply]
      {
        let restrictk := {n|n<=k}.restrict (π := α)
        have hrnm : restrict₂ gnm ∘ restrictk = {n | n <= Nat.find hsut}.restrict := by rfl
        have hrn : restrict₂ gn ∘ restrictk = {n | n <= Nat.find hs}.restrict := by rfl
        have hrm : restrict₂ gm ∘ restrictk = {n | n <= Nat.find ht}.restrict := by rfl
        have hunion : restrict₂ gnm ⁻¹' choose hTnm =
          restrict₂ gn ⁻¹' choose hTn ∪ restrict₂ gm ⁻¹' choose hTm := by {
            symm
            apply restrict_union α
            repeat rw [comp_preimage]
            rw [hrnm, hrn, hrm]
            rw [(choose_spec hTnm).2, (choose_spec hTn).2, (choose_spec hTm).2]
          }
        have hdisjoint : Disjoint (restrict₂ gn ⁻¹' choose hTn) (restrict₂ gm ⁻¹' choose hTm)
        := by {
          apply Disjoint.of_preimage (restrict_surjective _)
          repeat rw [comp_preimage]
          rw[hrn, hrm]
          rw [(choose_spec hTn).2, (choose_spec hTm).2]
          assumption
        }
        rw [hunion]
        apply measure_union hdisjoint
        apply MeasurableSet.preimage
        exact (choose_spec hTm).1
        exact measurable_restrict₂ gm
      }
      exact measurable_restrict₂ gm
      exact (choose_spec hTm).1
      exact measurable_restrict₂ gn
      exact (choose_spec hTn).1
      exact measurable_restrict₂ gnm
      exact (choose_spec hTnm).1
    })


lemma MeasureKernelSequenceContent_cylinder_apply
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  {n : ℕ}
  {s : Set _}
  (hs : s ∈ cylinder_n α n)
  : MeasureKernelSequenceContent μ K s = FiniteCompMeasureKernelNat μ K n (choose hs) := by {
    have hs' : s ∈ cylinders α := by {
      unfold cylinders
      simp
      exact ⟨n, hs⟩
    }
    unfold MeasureKernelSequenceContent
    rw [AddContent.mk'_on_C]
    simp only [show ∃ n, s ∈ cylinder_n α n from ⟨n, hs⟩, ↓reduceDIte, coe_setOf, mem_setOf_eq]
    generalize_proofs h1 h2 h3
    have hn : Nat.find h1 <= n := by
      simp only [Nat.find_le_iff]
      apply Exists.intro
      · apply And.intro
        · rfl
        · simp_all only
    rw [<- Measure.finiteCompLift μ K hn]
    simp only [coe_setOf, mem_setOf_eq]
    rw [Measure.map_apply]
    congr
    have h : {x|x<= Nat.find h1}.restrict ⁻¹' choose h2 = {x|x<=n}.restrict ⁻¹' choose h3 := by {
      rw [(choose_spec h2).2, (choose_spec h3).2]
    }
    nth_rw 1 [show {x | x <= Nat.find h1}.restrict
      = {x | x <= Nat.find h1}.restrict₂ (by simp only [setOf_subset_setOf];intros;omega)
        ∘ {x | x <= n}.restrict from rfl] at h
    rw [preimage_comp, restrict_preimage_equal_iff] at h
    exact h
    apply measurable_restrict₂
    exact (choose_spec h2).1
  }

-- lemma seq_inf : Tendsto a atTop 0 :


-- def slice {α : I -> Type*} (J : Set I)
--   (A : Set (∀i : J, α i)) (K : Set I) (ω : (∀i : K, α i))
--   : Set (∀i : ↑(J \ K), α i)
--   := {x | }

def partial_apply
  {α : I -> Type*}
  [∀n, Inhabited (α n)]
  {J K L : Set I}
  (ω : ∀k: J, α k)
  (f : (∀k: K, α k) -> β)
  (ω₂ : (∀k : L, α k))
  : β :=
  let ω₂ := compose ω ω₂
  f (K.restrict ω₂)

theorem measurable_partial_apply
  {α : I -> Type*}
  [∀n, Inhabited (α n)]
  [∀n, MeasurableSpace (α n)]
  [MeasurableSpace β]
  {J K L : Set I}
  (ω : ∀k: J, α k)
  (f : (∀k: K, α k) -> β)
  (hf : Measurable f)
  : Measurable (partial_apply (L := L) ω f) := by {
    unfold partial_apply
    simp only
    apply Measurable.comp' hf
    apply Measurable.comp'
    exact measurable_restrict K
    exact measurable_compose_snd ω
  }

def partial_apply_kernel_n {α : ℕ -> Type*} {n:ℕ}
  [∀n, MeasurableSpace (α n)]
  [∀n, Inhabited (α n)]
  (K : Kernel (∀k: {k|k <= n}, α k) (α (n+1)))
  {m : ℕ} (ω : ∀k: {k|k<=m}, α k)
  : Kernel (∀k: {k | m < k <= n}, α k) (α (n+1)) where
  toFun := partial_apply ω K.toFun
  measurable' := by {
    apply measurable_partial_apply
    exact K.measurable'
  }

lemma prob_method_integral [MeasurableSpace α] (f : α -> ℝ≥0∞) (μ : Measure α)
  (hpos: ∫⁻x, f x ∂μ > 0) : ∃x, f x > 0 := by {
    by_contra h
    simp at h
    have h : ∫⁻ x, f x ∂μ = 0 := by {
      calc ∫⁻ (x : α), f x ∂μ = ∫⁻ (x : α), 0 ∂μ := by congr; ext x; exact h x
        _ = 0 := by simp
    }
    rw [h] at hpos
    exact (lt_self_iff_false 0).mp hpos
}
-- lemma test (f : I -> ℝ≥0∞) (hf : ∀i, f i >= c)
--   : (⨅i, f i) >= c := by {
--     exact le_iInf hf
--   }

-- lemma iInf_fun {α : I -> Type*} {f : I -> ℝ≥0∞} {g : I -> I}
--   : ⨅i, f i <= ⨅i, f (g i)  := by {
--     exact le_iInf_comp f g
--   }

@[simp]
lemma MeasureSequenceKernelNatProb
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  : MeasureKernelSequenceContent μ K univ = 1 := by {
    have h : univ ∈ cylinder_n α 0 := by {
      unfold cylinder_n
      simp only [coe_setOf, mem_setOf_eq, mem_image, preimage_eq_univ_iff]
      use univ
      simp only [MeasurableSet.univ, subset_univ, and_self]
    }
    rw [MeasureKernelSequenceContent_cylinder_apply μ K h]
    simp only [coe_setOf, mem_setOf_eq, preimage_eq_univ_iff]
    generalize_proofs hT
    suffices choose hT = univ by simp [this]; exact measure_univ
    have h := (choose_spec hT).2
    simp at h
    generalize hs : choose hT = s
    rw [hs] at h
    suffices range {x | x <= 0}.restrict = univ by {
      rw [this] at h
      simp only [coe_setOf, mem_setOf_eq, univ_subset_iff] at h
      exact h
    }
    ext x
    simp only [coe_setOf, mem_setOf_eq, mem_range, mem_univ, iff_true]
    exact Subtype.exists_pi_extension x
  }

lemma MeasureSequenceKernelNatLeOne
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  {s : Set _}
  (hs : s ∈ cylinders α)
  : MeasureKernelSequenceContent μ K s ≤ 1 := by {
    suffices _ <= MeasureKernelSequenceContent μ K univ by {
    simp only [MeasureSequenceKernelNatProb] at this
    exact this
    }
    apply addContent_mono $ SetAlgebraIsSetSemiRing (cylinders_SetAlgebra α)
    exact hs
    exact univ_cylinders α
    simp only [subset_univ]
  }

theorem MeasureKernelSequenceContentSAdditive
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (⇑α {k|k <= m}) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  : (MeasureKernelSequenceContent μ K).sAdditive := by {
    apply AddContent.sContinuousInEmpty_finite_implies_sAdditive
    constructor
    · suffices ∀(B : (n : ℕ) -> Set _),
        (∀n, (B n) ∈ cylinder_n α n) ->
        (∀n, B n ⊇ B (n+1)) ->
        ⋂n, B n = ∅ ->
        Tendsto (fun n => MeasureKernelSequenceContent μ K (B n)) atTop (𝓝 0) by
          intro A hA hT hmono hempsect
          unfold cylinders at hA
          simp only [mem_iUnion] at hA
          let B n := ⋂ m ∈ {m| m <= n ∧ A m ∈ cylinder_n α n}, A m
          have hB : ∀n, B n ∈ cylinder_n α n := by {
            intro n
            unfold B
            rw [@biInter_eq_iInter]
            apply cylinder_iInter
            simp only [coe_setOf, mem_setOf_eq, Subtype.forall, and_imp, imp_self, implies_true]
          }
          have hBcylinder n : B n ∈ cylinders α := by {
            unfold cylinders
            simp only [mem_iUnion]
            use n
            exact hB n
          }
          have hBmono : ∀n, B n ⊇ B (n+1) := by {
            simp only [B, subset_iInter_iff]
            intro n m' hA
            simp at hA
            calc ⋂ m ∈ {m | m <= n+1 ∧ A m ∈ cylinder_n α (n + 1)}, A m ⊆
                ⋂ m ∈ {m | m = m'}, A m := by {
                  apply biInter_mono
                  simp only [setOf_eq_eq_singleton, singleton_subset_iff, mem_setOf_eq]
                  constructor
                  · omega
                  · exact cylinder_subset α (Nat.le_add_right n 1) hA.2
                  simp only [setOf_eq_eq_singleton, mem_singleton_iff, subset_refl, implies_true]
                  }
            _ = A m' := by simp only [setOf_eq_eq_singleton, mem_singleton_iff,
                iInter_iInter_eq_left]
          }
          have hBempsect : ⋂n, B n = ∅ := by {
            unfold B
            calc ⋂ n, ⋂ m ∈ {m | m <= n ∧ A m ∈ cylinder_n α n}, A m = ⋂ m, A m  := by {
              ext x
              simp only [mem_setOf_eq, mem_iInter]
              constructor <;> intro h
              · intro i
                obtain ⟨i',h'⟩ := hA i
                apply h (i' ⊔ i) i
                simp only [le_sup_right, true_and]
                apply cylinder_subset α (by omega) h'
              ·
                intro i i_1 i_2
                simp_all only [Nat.lt_find_iff, le_refl, not_false_eq_true, implies_true, mem_setOf_eq,
                  subset_iInter_iff, B]
            }
            _ = ∅ := by exact hempsect
          }
          specialize this B hB hBmono hBempsect

          let F := fun n => MeasureKernelSequenceContent μ K (A n)
          simp_rw [show (fun n => MeasureKernelSequenceContent μ K (A n)) = F by rfl]
          have hFbounded : ∀n, F n ≠ ⊤ := by {
            intro n
            suffices F n < ⊤ by exact LT.lt.ne_top this
            calc F n <= 1 := MeasureSequenceKernelNatLeOne μ K (by unfold cylinders; simp only [mem_iUnion]; exact hA n)
            _ < ⊤ := by simp only [one_lt_top]
          }
          have hAcylinder n : A n ∈ cylinders α := by {
            unfold cylinders
            simp only [mem_iUnion]
            exact hA n
          }
          have hFantitone : Antitone F := by {
            intro n m hnm
            exact addContent_mono (cylinders_setSemiRing α)
              (hAcylinder m)
              (hAcylinder n)
              (hmono hnm)
          }
          suffices BsupA : ∀n, ∃m, B n ⊇ A m by {
            rw [@ENNReal.tendsto_atTop_zero]
            rw [@ENNReal.tendsto_atTop_zero] at this
            intro ε hε
            specialize this ε hε
            obtain ⟨N, hN⟩ := this
            specialize BsupA N
            obtain ⟨m, hm⟩ := BsupA
            use m
            intro n hn
            specialize hN N (by rfl)
            calc F n ≤ F m := by exact hFantitone hn
            _ <= (MeasureKernelSequenceContent μ K) (B N) := by {
              apply addContent_mono (cylinders_setSemiRing α)
               (hAcylinder m)
               (hBcylinder N)
               (hm)
            }
            _ <= ε := by exact hN
          }
          intro n
          use n
          unfold B
          intro x hx
          simp only [mem_setOf_eq, mem_iInter, and_imp]
          intro i hi hc
          exact hmono hi hx

      intro B hB hmono hempsect
      by_contra hcontra
      let A n := choose (hB n)
      have hBmono n m : (hnm : n <= m) -> B m ⊆ B n := by {
        intro hnm
        let k := m-n
        have hmnk : m = n+k := by omega
        rw [hmnk]
        induction k with
        | zero => rfl
        | succ k hk=> {
          calc B (n + (k + 1)) ⊆ B (n + k) := hmono (n + k)
          _ ⊆ B n := hk
        }
      }
      have hABel n x : x ∈ A n <-> ∃y, {k|k<=n}.restrict y = x ∧ y ∈ B n := by {
        obtain ⟨_, h⟩ := choose_spec (hB n)
        rw [<- h]
        unfold A
        simp only [coe_setOf, mem_setOf_eq, mem_preimage]
        constructor <;> intro g
        · have hy: ∃y, {k|k<=n}.restrict y = x := by apply Subtype.exists_pi_extension
          obtain ⟨y, hy⟩ := hy
          use y
          constructor
          · exact hy
          · rw [hy]
            assumption
        · obtain ⟨y, hy⟩ := g
          rw [<- hy.1]
          exact hy.2
      }
      have hA n : MeasurableSet (A n) := (choose_spec (hB n)).1
      have hAB n : {k|k<=n}.restrict ⁻¹' A n = B n := by {
        ext x
        unfold A
        obtain ⟨_, h⟩ := choose_spec (hB n)
        constructor <;> intro h'
        · rw [<- h]
          exact h'
        · rw [<- h] at h'
          exact h'
      }
      have hABμ n: MeasureKernelSequenceContent μ K (B n)
        = FiniteCompMeasureKernelNat μ K n (A n) := by {
          rw [MeasureKernelSequenceContent_cylinder_apply μ K (hB n)]
        }
      have hcontmono : Antitone fun n => (MeasureKernelSequenceContent μ K) (B n) := by {
        intro m n hmn
        simp only
        refine addContent_mono ?_ ?_ ?_ (hBmono m n hmn)
        exact SetAlgebraIsSetSemiRing (cylinders_SetAlgebra α)
        unfold cylinders
        simp only [mem_iUnion]
        use n
        exact hB n
        unfold cylinders
        simp only [mem_iUnion]
        use m
        exact hB m
      }

      have hinf : ⨅ n, MeasureKernelSequenceContent μ K (B n) > 0 := by {
        by_contra h
        simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
        have h' := tendsto_atTop_iInf hcontmono
        rw [h] at h'
        contradiction
      }

      suffices ∃ω, ∀n, ({k|k<=n}.restrict ω) ∈ A (n) by {
        obtain ⟨ω,hω⟩ := this
        have inB : ω ∈ ⋂n, B n := by {
          simp
          intro n
          specialize hω n
          rw [<- hAB]
          simp
          assumption
        }
        rw [hempsect] at inB
        contradiction
      }
      let Q n m := FiniteCompKernelNat K n m
      let p n m : ProdLikeM _ _ _ := ProdLikeM.insert_m (α := α) n (m + 1)
      let f n m := kernel_slice (Q n m) (A (n + m + 1))
        (p := p n m)


      have hAmem n ω : ω ∈ A (n + 1) -> {k|k<=n}.restrict₂ (by simp; omega) ω ∈ A n := by {
        unfold A
        generalize_proofs h1 h2 h3
        intro h
        -- simp at h1 h2
        obtain ⟨h1m,h1s⟩ := choose_spec h1
        obtain ⟨h2m,h2s⟩ := choose_spec h2
        simp only at h1s h2s

        have hhh : ∃ω' , {k | k <= n + 1}.restrict ω' = ω := by exact Subtype.exists_pi_extension ω
        let ω' := choose hhh
        have hω' : ω' ∈ B (n + 1) := by {
          rw [<- h1s]
          simp
          rw [choose_spec hhh]
          exact h
        }
        specialize hmono n hω'
        rw [<- h2s] at hmono
        simp at hmono

        have hhhh : {k | k<=n}.restrict ω' = {k | k <= n}.restrict₂ (by simp;omega) ω := by {
          rw [<- choose_spec hhh]
          simp
          unfold ω'
          exact rfl
        }
        rw [<- hhhh]
        assumption
      }

      have hf n ω : f n 0 ω > 0 -> ω ∈ A n := by {
        unfold f
        simp
        intro h
        rw [show kernel_slice (Q n 0) (A (n + 1)) (p := p n 0) ω = ((Q n 0) ω)
          ((p n 0).slice (A (n + 1)) ω) from rfl] at h
        rw [show (p n 0).slice (A (n + 1)) ω = {b | (p n 0).equiv.symm (ω, b) ∈ A (n + 1)} from rfl] at h
        simp at h
        have h : {b | (p n 0).equiv.symm (ω, b) ∈ A (n + 1)} ≠ ∅ := by {
          by_contra hh
          simp only [Nat.reduceAdd, coe_setOf, mem_setOf_eq, ProdLikeM.insert_m_apply_inv,
            eq_mp_eq_cast, id_eq, eq_mpr_eq_cast] at hh
          rw [hh] at h
          simp at h
        }
        let hnon : Nonempty {b | (p n 0).equiv.symm (ω,b) ∈ A (n+1)} := by exact nonempty_iff_ne_empty'.mpr h
        let ⟨b,hb⟩ := hnon.some
        let ω' := (p n 0).equiv.symm (ω, b)
        have hω' : ω' ∈ A (n+1) := by exact hb
        specialize hAmem n ω' hω'
        generalize_proofs hgg at hAmem
        rw [show restrict₂ hgg ω' = ω by unfold ω'; {
          ext i
          simp only [mem_setOf_eq, restrict₂, coe_setOf, Nat.reduceAdd,
            ProdLikeM.insert_m_apply_inv, eq_mp_eq_cast, id_eq, eq_mpr_eq_cast]
          let hi : (i : ℕ) <= n := i.2
          simp [hi]
          rfl
        }] at hAmem
        assumption
      }

      suffices ∃ω, ∀n, ⨅m, f n m ({k|k<=n}.restrict ω) > 0 by {
        obtain ⟨ω, hω⟩ := this
        use ω
        intro n
        specialize hω n
        have h : f n 0 (({k | k <= n}).restrict ω) > 0 := by {
          calc 0 < ⨅m, f n m ({k|k<=n}.restrict ω) := by apply hω
            _ <= f n 0 ({k|k<=n}.restrict ω) := by apply iInf_le
        }
        exact hf n ({k | k ≤ n}.restrict ω) h
      }

      have hQ n m : IsMarkovKernel (Q n m) := by unfold Q; infer_instance

      have fmono : ∀n, Antitone (f n) := by {
        intro n
        intro m k hmk
        unfold f kernel_slice Q
        intro a
        simp only
        rw [<- Kernel.finiteCompLift μ K hmk]
        rw [Kernel.map_apply, Measure.map_apply]
        gcongr
        unfold ProdLikeM.slice
        intro x hx
        simp only [coe_setOf, mem_setOf_eq] at hx
        simp only [coe_setOf, mem_setOf_eq, preimage_setOf_eq]
        rw [hABel]
        rw [hABel] at hx
        obtain ⟨y,hy⟩ := hx
        use y
        constructor
        · rw [ show {k|k<= n + m+ 1}.restrict y
            = {k|k<= n+m+1}.restrict₂ (by simp;intros;omega)
              ({k'|k'<=n+k+1}.restrict y) from rfl]
          rw [hy.1]
          rfl
        · exact hBmono (n + m + 1) (n+k+1) (by omega) hy.2
        apply measurable_restrict₂
        exact ProdLikeM.slice_measurable (p n m) (A (n + m + 1)) (hA (n + m + 1)) a
        apply measurable_restrict₂
      }
      have fone : ∀n m ω, f n m ω <= 1 := by intros; simp [f, kernel_slice, Q]; apply prob_le_one
      have hf n m : Measurable (f n m) := by apply kernel_application_measurable; apply hA

      let μ' : Measure <| ∀k : {k | k <= 0}, α k := convert_measure μ

      have hf0m : ∀m, ∫⁻ ω, f 0 m ω ∂μ' = FiniteCompMeasureKernelNat μ K (m+1) (A (m+1)) := by {
        intro m
        unfold f Q
        rw [kernel_slice_integral]
        rw [show μ' = FiniteCompMeasureKernelNat μ K 0 by rfl]
        rw [compProd'_measure_kernel_finite_comp]
        have h0 : {k | k <= 0 + (m+1)} = {k | k <= m+1} := by simp only [zero_add]
        have h1 : 0+m+1 = m+1 := by simp only [zero_add]
        congr <;> try rw [h0]
        -- <;> try rw [h1]
        exact congr_arg_heq A h1
        exact hA (0 + m + 1)
      }

      have hf0inf : ⨅m, ∫⁻ ω, f 0 m ω ∂μ' = ∫⁻ ω, ⨅m, f 0 m ω ∂μ' := by {
        refine Eq.symm (lintegral_iInf (hf 0) (fmono 0) ?_)
        suffices ∫⁻ (a : (k : ↑{k | k ≤ 0}) → α ↑k), f 0 0 a ∂μ' < ⊤ by {
          exact LT.lt.ne_top this
        }
        refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ' ?_
        use 1
        intro x
        exact fone 0 0 x
      }
      simp_rw [<- hAB] at hinf
      simp_rw [<- hAB] at hABμ
      simp_rw [hABμ] at hinf
      have hf0ω : ∃ω, ⨅m, f 0 m ω > 0 := by {
        apply prob_method_integral
        rw [<- hf0inf]
        simp_rw [hf0m]
        have h : ∀m, (FiniteCompMeasureKernelNat μ K (m + 1)) (A (m + 1))
          >= ⨅ n, (FiniteCompMeasureKernelNat μ K n) (A n) := by {
            intro m
            apply iInf_le
        }
        have h' := le_iInf h
        calc 0 < _ := hinf
            _ <= _ := h'
      }

      have hf1 : ∀n m ω, f n (m+1) ω = ∫⁻ ω', f (n+1) m (compapp ω ω') ∂K n ω := by {
        intro n m ω
        unfold f Q
        exact kernel_slice_integral' K A hA n m ω
      }

      have hf1inf : ∀n ω, ⨅m, f n (m+1) ω = ∫⁻ ω', ⨅m, f (n+1) m (compapp ω ω') ∂K n ω := by {
        intro n ω
        -- symm
        simp_rw [hf1]
        symm
        apply lintegral_iInf
        · intro m
          apply Measurable.comp'
          apply hf
          apply measurable_compapp_snd
        · refine antitone_lam ?_
          intro b
          exact fun ⦃a b_1⦄ a_1 ↦ fmono (n + 1) a_1 (compapp ω b)
        · suffices _ < ⊤ by refine LT.lt.ne_top this
          calc ∫⁻ (a : α (n + 1)), f (n + 1) 0 (compapp ω a) ∂(K n) ω
            <= 1 := by {
              rw [<- hf1]
              exact fone n (0 + 1) ω
            }
          _ < ⊤ := by exact one_lt_top
      }

      apply strong_rec_on_nat_existence (h₀ := choose_spec hf0ω) (h:=fun n ω => ⨅m, f n m ω > 0)
      intro n ⟨ω, hω⟩
      apply prob_method_integral (μ := K n ω)
      rw [<- hf1inf]
      calc 0 < ⨅ m, f n m ω := by exact hω
        _ <= ⨅ m, f n (m + 1) ω := by apply le_iInf_comp

    ·
      unfold MeasureKernelSequenceContent
      simp only [coe_setOf, mem_setOf_eq, AddContent.mk'_on_C, preimage_eq_univ_iff]
      have nothing : univ ∈ cylinder_n α 0 := by {
        unfold cylinder_n
        simp only [coe_setOf, mem_setOf_eq, mem_image, preimage_eq_univ_iff]
        use univ
        simp only [MeasurableSet.univ, subset_univ, and_self]
      }
      have h : ∃n, univ ∈ cylinder_n α n := by use 0
      simp only [h, ↓reduceDIte, gt_iff_lt]
      generalize_proofs g
      have hg : choose g = univ := by {
        have hg := (choose_spec g).2
        generalize hgg : choose g = gg
        have hr : range ({x | x <= Nat.find h}.restrict (π := α)) = univ := by {
          ext x
          simp
          exact Subtype.exists_pi_extension x
        }
        have hhgg : range {x | x ≤ Nat.find h}.restrict ⊆ gg := by {
          rw [<- hgg]
          assumption
        }
        rw [hr] at hhgg
        exact eq_univ_of_univ_subset hhgg
      }
      rw [hg]
      have h1 : (FiniteCompMeasureKernelNat μ K (Nat.find h))
        (@univ ((k : { x // x ≤ Nat.find h }) → α ↑k) :
          Set ((k : { x // x ≤ Nat.find h }) → α ↑k))
        = 1 := by {
        let t : IsProbabilityMeasure (FiniteCompMeasureKernelNat μ K (Nat.find h))
          := inferInstance
        exact isProbabilityMeasure_iff.mp t
      }
      have h2 : (FiniteCompMeasureKernelNat μ K (Nat.find h))
        (@univ ((k : { x // x ≤ Nat.find h }) → α ↑k) :
          Set ((k : { x // x ≤ Nat.find h }) → α ↑k))
        < ⊤ := by {
          rw [h1]
          simp
        }
      exact h2
  }

def pi_equiv (α : I -> Type*) (J : Set I) (T : Type*) (TJequiv : T ≃ J)
[mα : ∀i : I, MeasurableSpace (α i)]
: (∀i : J, α i) ≃ᵐ ∀t : T, α (TJequiv t) where
toFun x t := x (TJequiv t)
invFun x i :=
  have h : TJequiv (TJequiv.symm  i) = i := by simp
  have hα : α (TJequiv (TJequiv.symm  i)) = α i := by rw [h]
  have hmα : HEq (mα (TJequiv (TJequiv.symm  i))) (mα i) := by rw [h]
  MeasurableEquiv.cast hα hmα (x (TJequiv.symm i))
left_inv := by {
  intro x
  ext i
  have h : TJequiv (TJequiv.symm  i) = i := by simp
  symm
  simp [MeasurableEquiv.cast]
  rw [eq_cast_iff_heq]
  rw [h]
  }
right_inv := by {
  intro x
  ext i
  simp [MeasurableEquiv.cast]
  have h : TJequiv.symm (TJequiv i) = i := by simp
  symm
  rw [eq_cast_iff_heq]
  rw [h]
  }
measurable_invFun := by {
  simp
  apply measurable_pi_lambda
  intro j
  obtain ⟨val, property⟩ := j
  simp_all only
  apply Measurable.comp'
  · apply MeasurableEquiv.measurable
  · apply measurable_pi_apply
}
measurable_toFun := by {
  simp
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_apply
}
set_option pp.proofs true

def Finset_equiv_set (F : Finset I) : (F ≃ (F : Set I)) := Equiv.subtypeEquivProp rfl

def Finset_set_equiv (α : I -> Type*) [mα : ∀m, MeasurableSpace (α m)] (F : Finset I)
  : (∀i:F, α i) ≃ᵐ ∀i:↑(F : Set I), α i
    := pi_equiv α F F (Finset_equiv_set F)
  -- toFun x i := by {
    -- have : α
    -- rw [<- h] at i
    -- have : α
    -- MeasurableEquiv.cast h x i
  -- }

lemma  cylinders_measurableCylinders
  (α : ℕ -> Type*)
  [mα : ∀m, MeasurableSpace (α m)]
  : cylinders α = measurableCylinders α := by {
      unfold cylinders cylinder_n
      unfold measurableCylinders cylinder
      simp
      ext x
      simp
      constructor
      · intro ⟨n, ⟨s, hs⟩⟩
        let F := Finset.range (n+1)
        use F
        have h : Finset.range (n+1) = {k | k <= n} := by {
          ext y
          simp
          omega
        }
        -- let t
        -- let t := Finset_set_equiv α F  ⁻¹' s
        -- have hα
        have h' : {x // x <= n} = ↑{k|k<=n} := by rfl
        have mα1 : MeasurableSpace (∀k:{k|k<=n}, α k) := inferInstance
        have mα2 : MeasurableSpace (∀k:Finset.range (n+1), α k) := inferInstance
        #check MeasurableEquiv
        -- have hm : HEq mα1 mα2 := by {
        --   rw [<- h']
        -- }

        rw [h] at s
        use s
        -- use i hi
    }


lemma cylinders_generate
  (α : ℕ -> Type*)
  [∀m, MeasurableSpace (α m)]
  : by infer_instance = generateFrom (cylinders α) := by {
    rw [cylinders_measurableCylinders]
    exact Eq.symm generateFrom_measurableCylinders
  }



def CompMeasureKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  : Measure (∀k, α k)
  := (MeasureKernelSequenceContent μ K).toMeasure
    (cylinders_generate α)
    (cylinders_SetAlgebra α)
    (MeasureKernelSequenceContentSAdditive μ K)


instance CompMeasureKernelNat_on_cylinders
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  (s : Set (∀k, α k))
  (hs : s ∈ cylinders α)
  : CompMeasureKernelNat μ K s = MeasureKernelSequenceContent μ K s := by {
    unfold CompMeasureKernelNat
    rwa [AddContent.toMeasure_eq_on_S]
  }


instance CompMeasureKernelNatProbability
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  : IsProbabilityMeasure (CompMeasureKernelNat μ K) := by {
    rw [@isProbabilityMeasure_iff]
    rw [CompMeasureKernelNat_on_cylinders]
    exact (MeasureSequenceKernelNatProb μ K)
    exact (univ_cylinders α)
  }




-- #check Measure.ext_of_generateFrom_of_iUnion
-- #check MeasureTheory.ext_of_generate_finite
lemma uniqeness_of_prob_measures [mα : MeasurableSpace α] (μ ν : Measure α)
  (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν)
  {S : Set (Set α)}
  (hSG : mα = generateFrom S) (hS : IsPiSystem S) (he : ∀s ∈ S, μ s = ν s) : μ = ν := by {
    ext t ht
    induction t, ht using induction_on_inter with
    | h_eq => exact hSG
    | h_inter => exact hS
    | empty => simp
    | basic t' ht' => {
      specialize he t' ht'
      norm_cast
    }
    | compl t' ht' h => rw [prob_compl_eq_one_sub ht', prob_compl_eq_one_sub ht', h]
    | iUnion A pd mA hi => {
      rw [measure_iUnion pd mA, measure_iUnion pd mA]
      exact tsum_congr fun b ↦ hi b
    }
  }

theorem uniqueness_compMeasureKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  (ν : Measure (∀k, α k))
  [hν : IsProbabilityMeasure ν]
  (h : ∀s ∈ cylinders α, CompMeasureKernelNat μ K s = ν s)
  : CompMeasureKernelNat μ K = ν := by {
    apply uniqeness_of_prob_measures
    exact CompMeasureKernelNatProbability μ K
    exact hν
    sorry
    -- exact Eq.symm cylinders_generate
    -- exact isPiSystem_measurableCylinders

    -- exact cylinders_SetAlgebra α
    -- exact h
  }






-- def ProductProbabilityMeasure  {I : Type*} [Fintype I] {Ω : I -> Type*}
-- [∀i, MeasurableSpace (Ω i)] (P : (i : I) -> ProbabilityMeasure (Ω i)) :
--   ProbabilityMeasure (ProductSpace Ω) := sorry


-- theorem existence_infinite_product_probability_measure :
-- ∀(P : (i : I) -> ProbabilityMeasure (Ω i)),
--   ∃! PP : ProbabilityMeasure (ProductSpace Ω), ∀(J : Finset I),
--    ProbabilityMeasure.map ℙ (aemeasurable (measurable_restrict J))
--     = ProductProbabilityMeasure (J.restrict P) := by {
--       sorry
--   }
--/
