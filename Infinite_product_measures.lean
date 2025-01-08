/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea
import IonescuTulcea.finiteCompProd
import IonescuTulcea.strong_rec
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal ProductProbabilityMeasure

/- recommended whenever you define anything new. -/
noncomputable section


/- Now write definitions and theorems. -/

namespace ProductProbabilityMeasure
open MeasureTheory MeasurableSpace Measurable ProductLike ProductProbabilityMeasure

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory

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
      rw [<- KernelLift μ K hnk, <- KernelLift μ K hmk, <- KernelLift μ K hnmk]
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

-- lemma seq_inf : Tendsto a atTop 0 :
open Filter Topology


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
    apply measurable_compose
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

theorem MeasureCompKernelNatContentSAdditive
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  : (MeasureKernelSequenceContent μ K).sAdditive := by {
    apply AddContent.sContinuousInEmpty_finite_implies_sAdditive
    constructor
    · suffices ∀(B : (n : ℕ) -> Set _),
        (∀n, (B n) ∈ cylinder_n α n) ->
        (∀n, B n ⊇ B (n+1)) ->
        ⋂n, B n = ∅ ->
        Tendsto (fun n => MeasureKernelSequenceContent μ K (B n)) atTop (𝓝 0) by {
          sorry
        }
      intro B hB hmono hempsect
      by_contra hcontra
      let A n := choose (hB n)
      have hA n : MeasurableSet (A n) := (choose_spec (hB n)).1
      have hAB n : {k|k<=n}.restrict ⁻¹' A n = B n := sorry
      have hABμ n: MeasureKernelSequenceContent μ K (B n)
        = FiniteCompMeasureKernelNat μ K n (A n) := sorry

      have hinf : ⨅ n, MeasureKernelSequenceContent μ K (B n) > 0 := sorry

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
      #check Q
      #check kernel_slice
      let p n m : ProdLikeM _ _ _ := ⟨equiv_6 (α := α) n (m + 1)⟩
      let f n m := kernel_slice (Q n m) (A (n + m + 1))
        (p := p n m)


      have hAmem n ω : ω ∈ A (n + 1) -> {k|k<=n}.restrict₂ (by simp; omega) ω ∈ A n := by {
        sorry
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
        sorry
        unfold f
        simp
        intro h
        rw [show kernel_slice (Q n n) (A (n + 1)) (p := p n 0) ω = ((Q n n) ω)
          ((p n 0).slice (A (n + 1)) ω) from rfl] at h
        rw [show (p n 0).slice (A (n + 1)) ω = {b | (p n 0).equiv.symm (ω, b) ∈ A (n + 1)} from rfl] at h
        simp at h
        have h : {b | (p n 0).equiv.symm (ω, b) ∈ A (n + 1)} ≠ ∅ := by {
          by_contra hh
          simp only [Nat.add_zero, coe_setOf, mem_setOf_eq] at hh -- Why do i need this
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
          simp
          unfold ProdLikeM.equiv
          unfold p equiv_4
          let hi : (i : ℕ) <= n := i.2
          simp [hi]
          rfl
        }] at hAmem
        assumption
      }

      suffices ∃ω, ∀n, ⨅m, f n m ({k|k<=n}.restrict ω) > 0 by {
        sorry
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


      -- suffices ∀n, ∃ω, ⨅m, f n m ω > 0 by {
      --   let n : ℕ  := sorry
      --   let ω := fun n => choose (this n)
      --   -- use ω
      -- }

      have hQ n m : IsMarkovKernel (Q n m) := by unfold Q; infer_instance

      -- #check kernel_application_measurable
      have fmono : ∀n, Antitone (f n) := by sorry
      -- have fpos : ∀n m ω, f n m ω >= 0 := by simp [f, kernel_slice, Q]
      have fone : ∀n m ω, f n m ω <= 1 := by intros; simp [f, kernel_slice, Q]; apply prob_le_one
      have hf n m : Measurable (f n m) := by apply kernel_application_measurable; apply hA

      let μ' : Measure <| ∀k : {k | k <= 0}, α k := convert_measure μ

      have hf0m : ∀m, ∫⁻ ω, f 0 m ω ∂μ' = FiniteCompMeasureKernelNat μ K m (A m) := by {
        intro m
        unfold f Q
        rw [kernel_slice_integral]
        calc ∫⁻ (ω : (k : ↑{k | k ≤ 0}) → α ↑k),
          kernel_slice (FiniteCompKernelNat K 0 m) (A (0 + m + 1)) (p := p _ _) ω ∂μ' =
          compProd' μ' (FiniteCompKernelNat K 0 m) (A (0 + m + 1)) ( p := p _ _ ) := by {
            generalize FiniteCompKernelNat K 0 m = K'
            -- unfold kernel_slice
          }
          _ = FiniteCompMeasureKernelNat μ K m (A m) := by {
            sorry
          }
          -- (FiniteCompMeasureKernelNat μ K m) (A m) := by sorry
        -- have h : kernel_slice (FiniteCompKernelNat K 0 m) (A (0 + m + 1)) ω
        --   = FiniteComp
        -- conv => rhs; rw [show m = 0 + m by simp]

      }

      have hf0inf : ⨅m, ∫⁻ ω, f 0 m ω ∂μ' = ∫⁻ ω, ⨅m, f 0 m ω ∂μ' := by {
        sorry
      }

      have hf0ω : ∃ω, ⨅m, f 0 m ω > 0 := by {
        sorry
      }

      have hf1 : ∀n m ω, f n m ω = ∫⁻ ω', f (n+1) m (compapp ω ω') ∂K n ω := by {
        sorry
      }

      have hf1inf : ∀n ω, ⨅m, f n m ω = ∫⁻ ω', ⨅m, f (n+1) m (compapp ω ω') ∂K n ω := by {
        sorry
      }

      -- have hf1ω : ∀n, ∃ω, (⨅m, f n m ω) > 0 := by {
      -- }
      sorry
      apply strong_rec_on_nat_existence (h₀ := choose_spec hf0ω) (h:=fun n ω => ⨅m, f n m ω > 0)

      intro n ⟨ω, hω⟩
      simp at hω
      specialize hf1inf n ω
      rw [hf1inf] at hω
      apply prob_method_integral (μ := K n ω)
      exact hω

    · sorry
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

-- lemma test : ({0,1}:Set ℕ) = {k|k < 2} := by exact toFinset_inj.mp rfl

-- lemma test2 : (J : Set I) (hJ : Finite J) : Finset J :=
/- ENDFILE HERE

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
    (MeasureCompKernelNatContentSAdditive μ K)


-- #check Measure.ext_of_generateFrom_of_iUnion
-- #check MeasureTheory.ext_of_generate_finite
-- theorem uniqeness_of_prob_measures [mα : MeasurableSpace α] (μ ν : ProbabilityMeasure α)
--   {S : Set (Set α)}
--   (hSG : mα = generateFrom S) (hS : IsPiSystem S) (he : ∀s ∈ S, μ s = ν s) : μ = ν := by {
--     ext t ht
--     induction t, ht using induction_on_inter with
--     | h_eq => exact hSG
--     | h_inter => exact hS
--     | empty => simp
--     | basic t' ht' => {
--       specialize he t' ht'
--       repeat rw [← ennreal_coeFn_eq_coeFn_toMeasure]
--       norm_cast
--     }
--     | compl t' ht' h => rw [prob_compl_eq_one_sub ht', prob_compl_eq_one_sub ht', h]
--     | iUnion A pd mA hi => {
--       rw [measure_iUnion pd mA, measure_iUnion pd mA]
--       exact tsum_congr fun b ↦ hi b
--     }
--   }






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
