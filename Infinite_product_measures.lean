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

-- variable {I : Type*}
-- variable (Ω : ∀(i : I), Type*)
-- variable [∀i, MeasurableSpace (Ω i)]
-- variable (J : Set I)
-- variable (JF : Finset I)

-- instance : (i : JF) -> MeasurableSpace (JF.restrict Ω i) := by {
--   intro i
--   rw [show JF.restrict Ω i = Ω i by rfl]
--   infer_instance
-- }
-- instance : ∀(i : J), MeasurableSpace (J.restrict Ω i) := by {
--   intro i
--   rw [show J.restrict Ω i = Ω i by rfl]
--   infer_instance
-- }
-- -- ×_(i ∈ I) Ω_i
-- abbrev ProductSpace := (i: I) -> Ω i


-- -- def π (i : I) (ω : ProductSpace Ω) := ω i
-- def π (J : Set I) : ProductSpace Ω  -> ProductSpace (J.restrict Ω) :=
--   fun ω => J.restrict ω

-- -- variable (i : I)
-- -- #check π Ω {i}

-- lemma pi_measurable (J : Set I) : Measurable (π Ω J) := by {
--     exact measurable_restrict J
-- }

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

-- theorem finite_product {I : Type*} [Fintype I] (Ω : I -> Type*) [∀i, MeasurableSpace (Ω i)]
--   (P : (i : I) -> ProbabilityMeasure (Ω i)) :
--   ∃! ℙ : ProbabilityMeasure (ProductSpace Ω), ∀A : (i : I) -> Set (Ω i),
--   ℙ {a : a i ∈ A i} = Π (i : I), P i (A i) := sorry

open ProbabilityTheory
def measurable_equivalence_singleton_product {I : Type*} (α : I -> Type*) (i : I) [∀m, MeasurableSpace (α m)]
  : (∀(j : ({i} : Set I)), α j) ≃ᵐ α i
  := MeasurableEquiv.piUnique (δ' := ({i} : Set I)) (π := fun x => α ↑x)

-- def measurable_equivalence_unique_product {I : Type*} (α : I -> Type*) (i : I) [∀m, MeasurableSpace (α m)]
--   : (∀(j : ({i} : Set I)), α j) ≃ᵐ α i
--   := MeasurableEquiv.piUnique (δ' := ({i} : Set I)) (π := fun x => α ↑x)


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
    -- exact K₀ ⊗ₖ' K₁
    sorry
  }

-- def Measure.change (μ : Measure α) := μ.comapRight
-- def measurable_equivalence1 (α : ℕ -> Type*) {n : ℕ} (hn: n <= 0) [∀m, MeasurableSpace (α m)]
--   : (∀k : {k | k <= n}, α k.1) ≃ᵐ α 0
--   := MeasurableEquiv.piUnique (δ' := ({i} : Set I)) (π := fun x => α ↑x)

-- @[simps (config := .asFn)]
lemma Unique.el_eq_el [αU : Unique α] (a b : α) : a = b := Eq.trans (αU.uniq a) (αU.uniq b).symm

def uniqueElim' [αU : Unique α] (β : α → Sort*) (a : α) (x : β a) (a' : α) : β a' := by
  rw [Unique.el_eq_el a' a]
  exact x

@[simp]
lemma uniqueElim'_el [αU : Unique α] (β : α → Sort*) (a : α) (x : β a) :
  uniqueElim' β a x a = x := by rfl

def Equiv.piUnique' [αU : Unique α] (β : α → Sort*) (a : α) : (∀ i, β i) ≃ β a where
  toFun f := f a
  invFun := uniqueElim' β a
  left_inv f := by ext i; rw [Unique.el_eq_el i a]; rfl
  right_inv _ := rfl

theorem measurable_uniqueElim' [αU : Unique α]  (β : α → Type*)
[∀a, MeasurableSpace (β a)]
    (a : α) :
    Measurable (uniqueElim' β a) := by {
      simp_rw [measurable_pi_iff]
      intro a'
      rw [Unique.el_eq_el a a']
      simp
      exact measurable_id
    }

def MeasurableEquiv.piUnique' [αU : Unique α] (β : α → Type*) [∀a, MeasurableSpace (β a)]
  (a : α) : (∀ i, β i) ≃ᵐ β a where
  toEquiv := Equiv.piUnique' β a
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := by {
    rw [show ⇑(Equiv.piUnique' β a).symm = uniqueElim' β a by rfl]
    exact measurable_uniqueElim' β a
  }

lemma not_le_n_is_n_add_one {n : ℕ} {i : {k | k <= n+1}} (h : ¬i <= n) : i = ⟨n+1, by simp⟩  := by {
  rw [Nat.not_le_eq] at h
  apply_fun (·.1)
  exact Nat.le_antisymm i.2 h
  exact Subtype.val_injective
}

def equiv {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  :(∀k : {k| k <= n + 1}, α k) ≃ᵐ (∀k : {k | k <= n}, α k) × (α (n+1)) where
  toFun x := ⟨fun i : {k | k <= n} =>
    x ⟨↑i, by obtain ⟨x,hx⟩ := i; simp at hx; simp; omega ⟩,
    x ⟨n+1, by simp⟩⟩
  invFun := fun (x, y) => fun i => if hi : i <= n then x ⟨↑i, hi⟩ else
    have h : α (n+1) = α ↑i := by rw [not_le_n_is_n_add_one hi]
    have h' : HEq (mα (n+1)) (mα ↑i) := by rw [not_le_n_is_n_add_one hi]
    MeasurableEquiv.cast h h' y
  left_inv := by {
    simp
    intro x
    ext i
    by_cases hi : i <= n <;> simp [hi]
    have h := not_le_n_is_n_add_one hi
    subst h
    rfl
  }
  right_inv := by {
    intro x
    ext i
    · simp [show ↑i <= n from i.2]; rfl
    · simp; rfl
  }
  measurable_toFun := by {
    -- measurability
    simp_all only [coe_setOf, mem_setOf_eq, Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, eq_mpr_eq_cast,
      Equiv.coe_fn_mk]
    apply Measurable.prod
    · simp_all only [Int.reduceNeg]
      apply measurable_pi_lambda
      intro a
      simp_all only [Int.reduceNeg]
      obtain ⟨val, property⟩ := a
      simp_all only [Int.reduceNeg]
      apply measurable_pi_apply
    · simp_all only
      apply measurable_pi_apply
  }
  measurable_invFun := by {
    simp
    apply measurable_pi_lambda
    intro a
    by_cases ha : a <= n <;> simp [ha]
    · -- measurability
      obtain ⟨val, property⟩ := a
      simp_all only
      apply Measurable.eval
      simp_all only
      apply measurable_fst
    · -- measurability
      obtain ⟨val, property⟩ := a
      simp_all only
      apply Measurable.comp'
      · apply MeasurableEquiv.measurable
      · simp_all only [not_le]
        apply measurable_snd
  }

instance {α : ℕ -> Type*} [∀n, MeasurableSpace (α n)] (n : ℕ)
  : ProdLikeM (∀k : {k| k <= n + 1}, α k) (∀k : {k | k <= n}, α k) (α (n+1)) where
  equiv := equiv n
-- instance {α : ℕ -> Type*} [∀n, MeasurableSpace (α n)] (n : ℕ)
--   : ProdLikeM (∀k : {k| k <= n}, α k) (∀k : {k | k <= n-1}, α k) (α (n- 1 + 1)) := by {
--       rw [show {k| k <= n} = {k | k <= n -1} ∪ {n -1 + 1} by ext; simp; omega]
--       have h : Fact (n -1 + 1 ∉ {k | k <= n-1}) := ⟨by simp⟩
--       -- exact instProdLikeMForallValMemSetUnionSingletonForall α (n₀ + 1)
--       infer_instance
--     }
class EquivalentMeasurableSpace (α : Type*) (β : Type*)
  [MeasurableSpace α] [MeasurableSpace β] where
  equiv : α ≃ᵐ β

def convert_measure [MeasurableSpace α] [MeasurableSpace β]
  [e : EquivalentMeasurableSpace α β] (μ : Measure α) := μ.map e.equiv

-- def test : DFunLike.coe

-- instance
-- {α : Type*}
-- {β : Type*}
-- [(MeasurableSpace α)]
-- [(MeasurableSpace β)]
-- -- [EquivalentMeasurableSpace α β]
--  : Coe (Measure α) ((Measure β))  where
--   coe m := sorry

instance {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)]
  : EquivalentMeasurableSpace (∀k : {k | k <= 0}, α k) (α 0) where
  equiv :=
      let U : Unique {k | k <= 0} := by {
          simp; infer_instance
        -- rw [show {k | k <= n} = {0} by ext; simp]
        -- exact uniqueSingleton 0
      }
      let τ := MeasurableEquiv.piUnique'
        (α := ({k | k <= 0})) (β := fun x => α ↑x) ⟨0, by simp⟩
      τ
instance [MeasurableSpace α] [MeasurableSpace β] [e : EquivalentMeasurableSpace α β]
: EquivalentMeasurableSpace β α where
  equiv := e.equiv.symm



def FiniteCompMeasureKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  : (n : ℕ) -> Measure (∀k : {k|k <= n}, α k)
  | 0 => convert_measure μ
  | m + 1 => compProd' (FiniteCompMeasureKernelNat μ K m) (K m)


-- def FiniteCompMeasureKernelNat
--   (n : ℕ)
--   {α : ℕ -> Type*}
--   [∀m, MeasurableSpace (α m)]
--   (μ : Measure (α 0))
--   (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
--   : Measure (∀k : {k|k <= n}, α k) :=
--   match n with
--   | 0 => (
--   -- if hn : n = 0 then
--     let ms : α 0 ≃ᵐ ∀k : {k | k <= n}, α k :=
--       let U : Unique {k | k <= n} := by {
--         sorry
--         -- rw [show {k | k <= n} = {0} by ext; simp]
--         -- exact uniqueSingleton 0
--       }
--       let τ := MeasurableEquiv.piUnique'
--         (α := ({k | k <= n})) (β := fun x => α ↑x) ⟨0, by simp⟩
--       τ.symm
--     μ.map ms
--   )
--   -- else
--   | Nat.succ m => sorry
--     -- let n₀ := n - 1
--     -- let p : ProdLikeM (∀k : {k| k <= n}, α k) (∀k : {k | k <= n₀}, α k) (α (n₀ + 1)) := by {
--     --   rw [show {k| k <= n} = {k | k <= n₀} ∪ {n₀ + 1} by ext; simp; omega]
--     --   have h : Fact (n₀ + 1 ∉ {k | k <= n₀}) := ⟨by simp⟩
--     --   -- exact instProdLikeMForallValMemSetUnionSingletonForall α (n₀ + 1)
--     --   infer_instance
--     -- }
--   --  compProd' (FiniteCompMeasureKernelNat n₀ μ K) (K n₀)

-- -- #check squareCylinders

-- #check {1,n} : Set ℕ

--  (squareCylinders fun (i : ℕ) => {s : Set (α i) | MeasurableSet s})
--  := (squareCylinders fun (i : ℕ) => {s : Set (α i) | MeasurableSet s})

def cylinder_n (α : ℕ -> Type*) (n : ℕ) [mα :∀n, MeasurableSpace (α n)]
 := ({k | k <= n}.restrict ⁻¹' ·) '' {T : Set (∀k : {k | k <= n}, α k)| MeasurableSet T}

lemma cylinder_subset (α : ℕ -> Type*) [mα :∀n, MeasurableSpace (α n)]
{n m : ℕ} (h : n <= m) : (cylinder_n α n) ⊆ (cylinder_n α m) := by {
  intro s hs
  unfold cylinder_n at *
  simp at *
  obtain ⟨x, ⟨xms,hx⟩⟩ := hs
  have hsnm : {a | a <= n} ⊆ {a | a <= m} := by simp; intro a ha; exact Nat.le_trans ha h
  use {a | a <= n}.restrict₂ hsnm ⁻¹' x
  constructor
  · apply MeasurableSet.preimage
    exact xms
    exact measurable_restrict₂ hsnm
  · rw [<- hx]
    rfl
}

-- def cylinder_lift (α : ℕ -> Type*) [mα :∀n, MeasurableSpace (α n)] {n : ℕ}
--   (s : Set (∀k : {k | k <= m})) (hs : s ∈ cylinder_n α n) (m : ℕ) (hnm : n <= m) : Set (∀k : {k | k <= m}, α k) :=

-- #check measurableCylinders
def cylinders (α : ℕ -> Type*) [mα :∀n, MeasurableSpace (α n)] := ⋃n, cylinder_n α n

lemma le_to_subset {n m : ℕ} (hnm : n <= m) : {k | k <= n} ⊆ {k | k <= m} := by {
  intro a ha
  simp at *
  exact Nat.le_trans ha hnm
}



@[simp]
lemma compProd_fst_is_measure [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α β)
  [mK : IsMarkovKernel K] : (μ ⊗ₘ K).map Prod.fst = μ := by {
    ext s hs
    rw [Measure.map_apply measurable_fst hs,
      ← setLIntegral_one,
      ← prod_univ,
      setLIntegral_compProd measurable_const hs MeasurableSet.univ
      ]
    simp
  }

@[simp]
lemma compProd'_fst_is_measure [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (μ : Measure α)
[IsProbabilityMeasure μ] (K : Kernel α β) [MeasurableSpace γ]
[p : ProdLikeM γ α β]
  [mK : IsMarkovKernel K]
  : (compProd' μ K (p := p)).map p.fst = μ := by {
    rw [show p.fst = (Prod.fst ∘ p.equiv) by rfl]
    ext s hs
    have hf : Measurable (Prod.fst ∘ p.equiv) := by {
      apply Measurable.comp
      exact @measurable_fst α β mα mβ
      exact MeasurableEquiv.measurable ProdLikeM.equiv
    }
    rw [Measure.map_apply hf hs]
    let t := Prod.fst (α := α) (β := β) ⁻¹' s
    have ht : MeasurableSet t := by {
      apply MeasurableSet.preimage
      exact hs
      exact measurable_fst
    }
    rw [show (Prod.fst ∘ ⇑ProdLikeM.equiv ⁻¹' s) = ⇑ProdLikeM.equiv ⁻¹' t by rfl]
    rw [compProd'_apply]
    let h := compProd_fst_is_measure (α := α) (β := β) μ K
    rw [<- Measure.map_apply, h]
    exact measurable_fst
    exact hs
    exact ht
  }


lemma comp_preimage (f : α -> β) (g : γ -> α) : g ⁻¹' (f ⁻¹' t) = (f ∘ g) ⁻¹' t := rfl

lemma restrict_prod_fst
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (n: ℕ)
  : restrict₂ (π := α) (le_to_subset <| Nat.le_add_right n 1) ∘ ⇑ProdLikeM.equiv.symm
    = Prod.fst
    := by {
      ext x y
      simp
      unfold ProdLikeM.equiv
      unfold instProdLikeMForallValNatMemSetSetOfLeHAddOfNatForall
      unfold equiv
      simp [show ↑y<= n from y.2]
      rfl
    }

lemma KernelLift
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  (mK : ∀m, IsMarkovKernel (K m))
  {n m: ℕ}
  (hnm : n <= m)
  : (FiniteCompMeasureKernelNat μ K m).map ({k | k <= n}.restrict₂ (le_to_subset hnm))
  = (FiniteCompMeasureKernelNat μ K n)
  := by {
  ext s hs
  revert n
  induction m with
  | zero => {
    intro n hnm
    rw [@Nat.le_zero] at hnm
    subst hnm
    generalize_proofs h
    unfold restrict₂
    simp
    }
  | succ m hm => {
    intro n hnm
    generalize_proofs hres
    have h : m <= m + 1 := by exact Nat.le_add_right m 1

    have hresm := le_to_subset (Nat.le_add_right m 1)
    have heqm : ∀ (s : Set ((a : ↑{k | k ≤ m}) → α ↑a)), MeasurableSet s →
    (Measure.map (restrict₂ hresm) (FiniteCompMeasureKernelNat μ K (m + 1))) s
      = (FiniteCompMeasureKernelNat μ K m) s := by {
        intro s hs
        have restrms : Measurable (restrict₂ (π := α) hresm) := measurable_restrict₂ hresm
        rw [Measure.map_apply restrms hs]
        unfold FiniteCompMeasureKernelNat
        simp only [coe_setOf, mem_setOf_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
          ↓reduceDIte, Nat.add_one_sub_one, eq_mpr_eq_cast]
        by_cases hm0 : m = 0
        ·
        -- -- · simp only [hm0, ↓reduceDIte]
        --   have hm1 : m+1 = 1 := by exact Nat.add_left_eq_self.mpr hm0

          -- have ph : Fact (m + 1 ∉ {k | k ≤ m}) := ⟨by simp⟩
          -- let p : ProdLikeM ((k : ↑({k | k ≤ m} ∪ {m + 1})) → α ↑k)
          --   ((k : { x // x ≤ m }) → α ↑k) (α (m + 1))
          --   := @inferInstance (ProdLikeM ((k : ↑({k | k ≤ m} ∪ {m + 1})) → α ↑k)
          --     ((k : { x // x ≤ m }) → α ↑k) (α (m + 1)))
          --           (instProdLikeMForallValMemSetUnionSingletonForall α (m + 1))

          subst hm0
          simp at *

          -- simp only [Nat.reduceAdd, ↓reduceDIte]
          -- let p : ProdLikeM ((k : { x // x ≤ 0 + 1 }) → α ↑k) ((k : { x // x ≤ 0 }) → α ↑k) (α (0 + 1))
          --   := by infer_instance
          rw [compProd'_def]
          -- unfold FiniteCompMeasureKernelNat
          -- simp
          rw [Measure.map_apply]
          · rw [comp_preimage]
            simp
            rw [show p.equiv.symm ⁻¹' (restrict₂ hresm ⁻¹' s)
              = (restrict₂ hresm ∘ p.equiv.symm) ⁻¹' s by {sorry}]
          -- have h : restrict₂ hresm = Prod.fst ∘ ((⇑ProdLikeM.equiv.symm) : ((k : { x // x ≤ 0 }) → α ↑k) × α 1 → (k : { x // x ≤ 1 }) → α ↑k) := by {
          }
          -- generalize_proofs p1 F1 hms hclear

          -- rw [Measure.map_apply]
          -- unfold restrict₂

          -- have h : (restrict₂ hresm ⁻¹' s) = p1.equiv '' s
          -- nth_rw 3 [DFunLike.coe]


          -- rw [show ⇑(MeasurableEquiv.piUnique' (fun k : {k | k <= 0} ↦ α ↑k) ⟨0, hclear⟩).symm =
          --     (MeasurableEquiv.piUnique' (fun k ↦ α ↑k) ⟨0, hclear⟩).invFun from rfl]

          -- rw [show (MeasurableEquiv.piUnique' (fun k : {k | k <= 0} ↦ α ↑k) (⟨0, hclear⟩ : {k | k <= 0})).symm
          --     = uniqueElim' (fun k ↦ α ↑k) (⟨0, hclear⟩ : {k | k <= 0}) from rfl]


      }

    rw [@Nat.le_add_one_iff] at hnm
    -- obtain hnm|hnm := hnm

    -- ·
      -- exact hm hnm
    -- have heq :

    }
}


lemma cylinders_SetAlgebra (α : ℕ -> Type*) [mα : ∀n, MeasurableSpace (α n)] : IsSetAlgebra (cylinders α) where
  empty_mem := by {
    unfold cylinders cylinder_n
    simp
    use 0
    use ∅
    simp
  }
  compl_mem := by {
    intro s hs
    unfold cylinders cylinder_n at *
    simp at *
    obtain ⟨n, ⟨x, ⟨xms, hx⟩⟩⟩ := hs
    use n
    use xᶜ
    constructor
    · exact MeasurableSet.compl_iff.mpr xms
    · rw [<- hx]
      rfl
  }
  union_mem := by {
    intro s t hs ht
    unfold cylinders at *
    simp at *
    obtain ⟨n, hs⟩ := hs
    obtain ⟨m, ht⟩ := ht
    let k := n ⊔ m
    have hs : s ∈ cylinder_n α k := cylinder_subset α (Nat.le_max_left n m) hs
    have ht : t ∈ cylinder_n α k := cylinder_subset α (Nat.le_max_right n m) ht
    use k
    unfold cylinder_n at *
    simp at *
    obtain ⟨x,⟨xms,hx⟩⟩ := hs
    obtain ⟨y,⟨yms,hy⟩⟩ := ht
    use x ∪ y
    constructor
    · exact MeasurableSet.union xms yms
    · rw [<- hy, <- hx]
      rfl
  }

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
  : AddContent (cylinders α) := AddContent.mk'
    (C := cylinders α)
    (hAlg := cylinders_SetAlgebra α)
    (toFun := fun s =>
      if h : ∃n, s ∈ cylinder_n α n then
        have h' := Nat.find_spec h
        let n := Nat.find h
        let T := choose h'
        FiniteCompMeasureKernelNat n μ K T
      else 0)
    (empty' := by {
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
    })
    (additivity := by {
      intro s hs t ht hst
      have hsut : s ∪ t ∈ cylinders α := by apply (cylinders_SetAlgebra α).union_mem hs ht
      unfold cylinders at hs ht hsut
      simp at hs ht hsut
      simp [hs, ht, hsut]

    })

  --   sUnion' := by {
  --     intro S hS pwd Urec
  --     simp [Urec]
  --     have h0 (s : S) : ∃ n, s.1 ∈ cylinder_n α n := by {
  --       specialize hS s.2
  --       exact mem_iUnion.mp hS
  --     }
  --     have h0' (s : S)  := Nat.find_spec (h0 s)
  --     -- ∃ x_1, MeasurableSet x_1 ∧ {x_2 | x_2 ≤ Nat.find (h0 s hs)}.restrict ⁻¹' x_1 = s := by {
  --     --   specialize h0 s hs
  --     --   unfold cylinder_n at h0
  --     -- }
  --     have h' : ∃ n, ⋃₀ S ∈  cylinder_n α n := by exact mem_iUnion.mp Urec
  --     simp [h']

  --     generalize_proofs h1 h2 h3
  --     have hhh
  -- --     : (@Finset.sum (Set ((a : ℕ) → α a)) ℝ≥0∞ NonUnitalNonAssocSemiring.toAddCommMonoid S fun x ↦
  -- -- if h : ∃ n, x ∈ cylinder_n α n then (FiniteCompMeasureKernelNat (Nat.find (h2 x h)) μ K) (choose (h3 x h)) else 0 : ℝ≥0∞)
  -- --       =
  -- --       ∑ s : S, (FiniteCompMeasureKernelNat (Nat.find (h0 s)) μ K) (choose (h0' s))
  --       := by
  --        calc
  --       ∑ x ∈ S, (if h : ∃ n, x ∈ cylinder_n α n
  --         then (FiniteCompMeasureKernelNat (Nat.find (h2 x h)) μ K) (choose (h3 x h)) else 0)
  --       = ∑ s : S, (if h : ∃ n, s.1 ∈ cylinder_n α n
  --         then (FiniteCompMeasureKernelNat (Nat.find (h2 s.1 h)) μ K) (choose (h3 s.1 h)) else 0)
  --           := by symm; apply Finset.sum_coe_sort S (fun s => (if h : ∃ n, s ∈ cylinder_n α n
  --                 then (FiniteCompMeasureKernelNat (Nat.find (h2 s h)) μ K) (choose (h3 s h)) else 0))
  --       _ = ∑ s : S, (FiniteCompMeasureKernelNat (Nat.find (h0 s)) μ K) (choose (h0' s)) := by {
  --         congr
  --         ext s
  --         simp [h0 s]
  --     }
  --     have hgoal :(FiniteCompMeasureKernelNat (Nat.find h') μ K) (choose h1) =
  --       (@Finset.sum (Set ((a : ℕ) → α a)) ℝ≥0∞ NonUnitalNonAssocSemiring.toAddCommMonoid S fun x ↦
  --         if h : ∃ n, x ∈ cylinder_n α n then (FiniteCompMeasureKernelNat (Nat.find (h2 x h)) μ K) (choose (h3 x h)) else 0 : ℝ≥0∞)
  --         := by {
  --           rw [hhh]


  --         }
  --     -- rw [hhh]
  --     exact hgoal
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
