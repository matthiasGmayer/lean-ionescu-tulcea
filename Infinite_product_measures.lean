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





#check squareCylinders

-- #check {1,n} : Set ℕ

--  (squareCylinders fun (i : ℕ) => {s : Set (α i) | MeasurableSet s})
--  := (squareCylinders fun (i : ℕ) => {s : Set (α i) | MeasurableSet s})

def cylinder_n (α : ℕ -> Type*) (n : ℕ) [mα :∀n, MeasurableSpace (α n)]
 := ({k | k <= n}.restrict ⁻¹' ·) '' {T : Set (∀k : {k | k <= n}, α k)| MeasurableSet T}

-- #check measurableCylinders
def cylinders (α : ℕ -> Type*) [mα :∀n, MeasurableSpace (α n)] := ⋃n, cylinder_n α n

lemma Surj_emp (f : α -> β) (hf : Surjective f) (hS : f ⁻¹' S = ∅) : S = ∅  := by {
  rw [show ∅ = f ⁻¹' ∅ by exact rfl] at hS
  exact (preimage_eq_preimage hf).mp (id (Eq.symm hS)).symm
}


-- lemma test (S : Finset α) (f : α -> ℝ) : ∑ s ∈ S, f s = ∑ s : S, f s.1 := by {
--   exact Eq.symm (Finset.sum_coe_sort S f)
-- }

def MeasureKernelSequenceContent
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  : AddContent (cylinders α) where
    toFun s :=
      if h : ∃n, s ∈ cylinder_n α n then
        have h' := Nat.find_spec h
        let n := Nat.find h
        let T := choose h'
        FiniteCompMeasureKernelNat n μ K T
      else 0
    empty' := by {
      simp
      intro n h
      generalize_proofs h1 h2
      have ⟨_,h3⟩ := choose_spec h2
      have h' : choose h2 = ∅ := by {
        have g : Surjective ({x | x <= Nat.find h1}.restrict (π := α)) := by {
          unfold Surjective
          intro b
          exact Subtype.exists_pi_extension b
        }
        exact Surj_emp {x | x ≤ Nat.find h1}.restrict g h3
      }
      rw [h']
      simp
    }
    sUnion' := by {
      intro S hS pwd Urec
      simp [Urec]
      have h0 (s : S) : ∃ n, s.1 ∈ cylinder_n α n := by {
        specialize hS s.2
        exact mem_iUnion.mp hS
      }
      have h0' (s : S)  := Nat.find_spec (h0 s)
      -- ∃ x_1, MeasurableSet x_1 ∧ {x_2 | x_2 ≤ Nat.find (h0 s hs)}.restrict ⁻¹' x_1 = s := by {
      --   specialize h0 s hs
      --   unfold cylinder_n at h0
      -- }
      have h' : ∃ n, ⋃₀ S ∈  cylinder_n α n := by exact mem_iUnion.mp Urec
      simp [h']

      generalize_proofs h1 h2 h3
      have hhh
  --     : (@Finset.sum (Set ((a : ℕ) → α a)) ℝ≥0∞ NonUnitalNonAssocSemiring.toAddCommMonoid S fun x ↦
  -- if h : ∃ n, x ∈ cylinder_n α n then (FiniteCompMeasureKernelNat (Nat.find (h2 x h)) μ K) (choose (h3 x h)) else 0 : ℝ≥0∞)
  --       =
  --       ∑ s : S, (FiniteCompMeasureKernelNat (Nat.find (h0 s)) μ K) (choose (h0' s))
        := by
         calc
        ∑ x ∈ S, (if h : ∃ n, x ∈ cylinder_n α n
          then (FiniteCompMeasureKernelNat (Nat.find (h2 x h)) μ K) (choose (h3 x h)) else 0)
        = ∑ s : S, (if h : ∃ n, s.1 ∈ cylinder_n α n
          then (FiniteCompMeasureKernelNat (Nat.find (h2 s.1 h)) μ K) (choose (h3 s.1 h)) else 0)
            := by symm; apply Finset.sum_coe_sort S (fun s => (if h : ∃ n, s ∈ cylinder_n α n
                  then (FiniteCompMeasureKernelNat (Nat.find (h2 s h)) μ K) (choose (h3 s h)) else 0))
        _ = ∑ s : S, (FiniteCompMeasureKernelNat (Nat.find (h0 s)) μ K) (choose (h0' s)) := by {
          congr
          ext s
          simp [h0 s]
      }
      have hgoal :(FiniteCompMeasureKernelNat (Nat.find h') μ K) (choose h1) =
        (@Finset.sum (Set ((a : ℕ) → α a)) ℝ≥0∞ NonUnitalNonAssocSemiring.toAddCommMonoid S fun x ↦
          if h : ∃ n, x ∈ cylinder_n α n then (FiniteCompMeasureKernelNat (Nat.find (h2 x h)) μ K) (choose (h3 x h)) else 0 : ℝ≥0∞)
          := by {
            rw [hhh]


          }
      -- rw [hhh]
      exact hgoal
}


lemma rectangles_SetAlgebra (α : ℕ -> Type* ) [mα : ∀n, MeasurableSpace (α n)]: IsSetAlgebra (rectangles α) := by {
  sorry
}


-- def rectangles (α : ℕ -> Type*) [mα : ∀n, MeasurableSpace (α n)]
--  := {S : Set (∀n, α n) | ∃n T, MeasurableSet T ∧ S = {k | k <= n}.restrict ⁻¹' T}
-- def KernelSequenceContent
--   (n : ℕ)
--   {α : ℕ -> Type*}
--   [∀m, MeasurableSpace (α m)]
--   [∀m, Inhabited (α m)]
--   (μ : Measure (α 0))
--   (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
--   : AddContent (rectangles α)  where
--     toFun s := if h : s ∈ (rectangles α) then by {
--       unfold rectangles at h
--       simp at h
--       have hn := Classical.choose_spec h
--       generalize choose h = n at hn
--       have hT := Classical.choose_spec hn
--       generalize choose hn = T at hT
--       exact FiniteCompMeasureKernelNat n μ K T
--     } else 0
--     empty' := by {
--       simp
--       intro h
--       generalize_proofs h1 h2
--       have ⟨_,h3⟩ := choose_spec h2
--       have h' : choose h2 = ∅ := by {
--         have g : Surjective ({x | x <= choose h1}.restrict (π := α)) := by {
--           unfold Surjective
--           intro b
--           exact Subtype.exists_pi_extension b
--         }
--         exact Surj_emp {x | x ≤ choose h1}.restrict g (id (Eq.symm h3))
--       }
--       rw [h']
--       simp
--     }
--     sUnion' := by {
--       intro S hS pwd Urec
--       simp [Urec]
--       -- generalize_proofs h1 h2 hx1 hx2
--       sorry


--     }
-- }






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
