/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea.prodLike
import IonescuTulcea.equivalences
import IonescuTulcea.AddContentExtension
import Mathlib

open IndexedFamilies

set_option autoImplicit true
open Function Set Classical ENNReal

noncomputable section

/-!

This file contains the definition of a finite composition of kernels and measures
and some lemmas about them.
It defines cylinders that are naturally defined on {k<=n} (instead of finset like in mathlib)
We can then define the sequence of finite compositions (μ ⊗ ... K n), and we show that
we can Lift up, i.e. we have the consistency property that (π{≤n})#(μ ⊗ ... K m) = (μ ⊗ ... K n) for n <= m

In the end there are some definitions to handle interaction between indexed families.
I.e. compose a b uses a on its indices and b on its indices.
For convenience i assumed inhabited, which could be relaxed, but Ionescu Tulcea becomes trivially untrue then,
so i didn't bother.
-/

namespace CompProdMeasures
open MeasureTheory MeasurableSpace Measurable ProductLike

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike
open ProbabilityTheory
open IndexedFamilies


def FiniteCompMeasureKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (⇑α {k|k <= m}) (α (m+1)))
  : (n : ℕ) -> Measure (⇑α {k|k <= n})
  | 0 => convert_measure μ
  | m + 1 => FiniteCompMeasureKernelNat  μ K m ⊗ₘ' K m

def FiniteCompKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (⇑α {k|k <= m}) (α (m+1)))
  (n : ℕ)
  : (m : ℕ) -> Kernel (⇑α {k | k <= n}) (⇑α {k | n < k ∧ k <= n+m+1})
  | 0 => convert_kernel (K n)
  | m+1 =>
    FiniteCompKernelNat K n m ⊗ₖ' K (n + m + 1)

instance compProd'_stays_probability
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [p : ProdLikeM γ α β]
  (μ : Measure α)
  [IsProbabilityMeasure μ]
  (K : Kernel α β)
  [IsMarkovKernel K]
  : IsProbabilityMeasure (compProd' μ K : Measure γ) := by {
    rw [compProd'_def]
    apply isProbabilityMeasure_map
    measurability
  }



instance finite_comp_stays_probability
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [mK : ∀m, IsMarkovKernel (K m)]
  (n : ℕ) : IsProbabilityMeasure (FiniteCompMeasureKernelNat μ K n) := by {
    induction n with
    | zero =>  {
      unfold FiniteCompMeasureKernelNat
      infer_instance
    }
    | succ n => {
      unfold FiniteCompMeasureKernelNat
      infer_instance
    }
  }

instance Kernel.compProd'_stays_markov
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  [p : ProdLikeM γ α β]
  [q : ProdLikeM ε β δ]
  (K : Kernel α β)
  (L : Kernel γ δ)
  [IsMarkovKernel K]
  [IsMarkovKernel L]
  : IsMarkovKernel (Kernel.compProd' K L) := by {
    -- rw [compProd'_def]
    rw [show Kernel.compProd' K L =
    change_right (K ⊗ₖ change_left L ProdLikeM.equiv) ProdLikeM.equiv.symm from rfl]
    unfold change_left change_right
    refine
      Kernel.IsMarkovKernel.map
        (K ⊗ₖ L.comap ProdLikeM.equiv.invFun ProdLikeM.equiv.measurable_invFun) ?_
    measurability
  }

instance convert_kernel_stays_markov
  -- {α β: Type*}
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  (K : Kernel α β)
  [mK : IsMarkovKernel K]
  [e: EquivalentMeasurableSpace α γ]
  [f : EquivalentMeasurableSpace β δ]
  : IsMarkovKernel (convert_kernel K : Kernel γ δ) := by {
    unfold convert_kernel
    simp
    have m : IsMarkovKernel (K.map f.equiv) := by {
      apply Kernel.IsMarkovKernel.map
      apply MeasurableEquiv.measurable
    }
    apply Kernel.IsMarkovKernel.comap (K.map ⇑EquivalentMeasurableSpace.equiv) convert_kernel.proof_1
  }

instance Kernel.FiniteCompProd'_stays_markov
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  [∀m, IsMarkovKernel (K m)]
  (m : ℕ) (n : ℕ)
  : IsMarkovKernel (FiniteCompKernelNat K n m) := by {
    induction m with
    | zero => {
      simp [FiniteCompKernelNat]
      infer_instance
    }
    | succ m => {
      simp [FiniteCompKernelNat]
      infer_instance
    }
  }

def kernel_slice
  [MeasurableSpace α ]
  [MeasurableSpace β ]
  [MeasurableSpace γ ]
  (K : Kernel α β)
  [p : ProdLikeM γ α β]
  (B : Set γ)
  (a : α)
  : ℝ≥0∞ := K a (p.slice B a)

def rectangles α β [MeasurableSpace α] [MeasurableSpace β]
  := (Set.image2 (fun (x1 : Set α) (x2 : Set β) => x1 ×ˢ x2) {s : Set α | MeasurableSet s}
      {t : Set β | MeasurableSet t})
lemma measurable_section [MeasurableSpace α] [MeasurableSpace β] (A : Set (α × β))
  (hA : MeasurableSet A)
  : MeasurableSet {b | (a, b) ∈ A} := by {
    induction A, hA using induction_on_inter with
    | h_eq => symm; exact generateFrom_prod
    | h_inter => exact isPiSystem_prod
    | empty => exact MeasurableSet.const False
    | basic A hA => {
      simp at hA
      obtain ⟨A₁,⟨hA₁,⟨A₂,⟨hA₂,hA⟩⟩⟩⟩ := hA
      rw [<- hA]
      subst hA
      simp_all only [mem_prod, measurableSet_setOf]
      apply Measurable.comp'
      · apply measurable_from_top
      · simp_all only [measurable_mem]
    }
    | compl t htm hc => {
      simp_all only [measurableSet_setOf, mem_compl_iff]
      apply Measurable.comp'
      · apply measurable_from_top
      · simp_all only
    }
    | iUnion f dis hfm hui => {
      rw [show {b | (a, b) ∈ ⋃ i, f i} = ⋃i, {b | (a, b) ∈ f i} by ext i; simp]
      exact MeasurableSet.iUnion fun b ↦ hui b
    }
}

lemma slice_preimage [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [p : ProdLikeM γ α β]
  (a : α)
  (B : Set γ)
  : {b | p.equiv.symm (a,b) ∈ B} = {b | (a, b) ∈ p.equiv '' B}:= by {
      ext x
      simp
      rw [show ProdLikeM.equiv.symm (a, x) ∈ B <->
        ∃y ∈ B, ProdLikeM.equiv.symm (a, x) = y by simp]
      apply exists_congr
      intro y
      apply and_congr; simp
      constructor <;> intro h
      apply_fun p.equiv at h
      simp at h
      exact h.symm
      apply_fun p.equiv.symm at h
      simp at h
      exact h.symm
  }
-- lemma slice_preimage_measurable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
--   [p : ProdLikeM γ α β]
--   (B : Set γ)
--   (hB : MeasurableSet B)
--   : MeasurableSet <| p.equiv '' B := by {
--     simp_all only [MeasurableEquiv.measurableSet_image]
--   }

lemma kernel_application_measurable
  {α β γ : Type*}
  [MeasurableSpace α ]
  [MeasurableSpace β ]
  [mγ : MeasurableSpace γ ]
  (K : Kernel α β)
  [mK : IsMarkovKernel K]
  [p : ProdLikeM γ α β]
  (B : Set γ)
  (hB : @MeasurableSet _ mγ B)
  : Measurable (kernel_slice K B) := by {
    unfold kernel_slice ProdLikeM.slice
    let B' : Set (α × β) := p.equiv '' B
    have hB' : MeasurableSet B' := by {
      simp_all only [MeasurableEquiv.measurableSet_image, B']
    }
    have h : ∀a, {b | ProdLikeM.equiv.symm (a, b) ∈ B} = {b | (a, b) ∈ B'} := by {
      intro a
      exact slice_preimage a B
    }
    simp_rw [h]

    induction B', hB' using induction_on_inter with
    | h_eq => exact generateFrom_prod.symm
    | h_inter => exact isPiSystem_prod
    | empty => simp_all only [MeasurableEquiv.measurableSet_image, mem_image, mem_empty_iff_false, setOf_false,
      measure_empty, measurable_const, B']
    | basic A hA => {
      simp at hA
      obtain ⟨A₁,⟨hA₁,⟨A₂,⟨hA₂,hA⟩⟩⟩⟩ := hA
      rw [<- hA]
      simp only [mem_prod]
      rw [show (fun a ↦ (K a) {b | a ∈ A₁ ∧ b ∈ A₂})
      = A₁.indicator (K · A₂) by {
        ext a
        by_cases h : a ∈ A₁ <;> simp [h]
      }]
      apply Measurable.indicator ?_ hA₁
      exact Kernel.measurable_coe K hA₂
    }
    | compl A hA h => {
      simp_rw [show ∀a, {b | (a, b) ∈ Aᶜ} = {b | (a,b) ∈ A}ᶜ by intro; rfl]
      simp_rw [show ∀a, (K a) {b | (a, b) ∈ A}ᶜ = 1 - (K a) {b | (a, b) ∈ A} by {
        intro a
        rw [prob_compl_eq_one_sub]
        exact measurable_section A hA
        }]
      simp_all only [MeasurableEquiv.measurableSet_image, mem_image, B']
      apply Measurable.const_sub
      simp_all only
    }
    | iUnion f dis hfm hui => {
      simp_rw [show ∀a, {b | (a, b) ∈ ⋃ i, f i} = ⋃i, {b | (a,b) ∈ f i} by intro;ext;simp]
      simp_rw [show ∀a, (K a) (⋃i, {b | (a,b) ∈ f i}) = ∑' i, (K a) {b | (a,b) ∈ f i} by {
        intro a
        apply (K a).m_iUnion
        exact fun i ↦ measurable_section (f i) (hfm i)
        intro n m hnm
        rw [show (Disjoint on fun i ↦ {b | (a, b) ∈ f i}) = fun x y ↦
          Disjoint ((fun i ↦ {b | (a, b) ∈ f i}) x) ((fun i ↦ {b | (a, b) ∈ f i}) y) from rfl]
        simp
        rw [@disjoint_iff_inter_eq_empty]
        ext x
        simp
        intro h
        by_contra h'
        unfold Pairwise at dis
        specialize dis hnm
        rw [show (Disjoint on f) = fun x y ↦ Disjoint (f x) (f y) from rfl] at dis
        rw [@disjoint_iff_inter_eq_empty] at dis
        have h'' : (a, x) ∈ f n ∩ f m:= by simp; constructor <;> assumption
        rw [dis] at h''
        contradiction
      }]
      simp_all only [MeasurableEquiv.measurableSet_image, mem_image, B']
      apply Measurable.ennreal_tsum
      intro i
      simp_all only
    }
  }

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

lemma cylinder_iInter
  {α : ℕ -> Type*}
  [∀i, MeasurableSpace (α i)]
  {n : ℕ}
  [Countable I]
  (A : I -> Set _)
  (hA : ∀i, A i ∈ cylinder_n α n)
  : ⋂i, A i ∈ cylinder_n α n := by {
    simp [cylinder_n, *] at *
    let x n := choose (hA n)
    let hx n := choose_spec (hA n)
    let hx1 n := (hx n).1
    let hx2 n := (hx n).2
    use ⋂n, x n
    constructor
    · exact MeasurableSet.iInter hx1
    · simp_rw [preimage_iInter, hx2]
  }


lemma restrict_preimage_subset_iff
  {α : I -> Type*}
  [∀i, Inhabited (α i)]
  (J : Set I)
  (s t : Set (∀j : J, α j))
  : (J.restrict ⁻¹' s ⊆ J.restrict ⁻¹' t) ↔ s ⊆ t := by {
    constructor <;> intro h
    · intro x hx
      let y := choose (Subtype.exists_pi_extension x)
      have hy : J.restrict y = x := choose_spec (Subtype.exists_pi_extension x)
      rw [<- hy]
      suffices y ∈ J.restrict ⁻¹' t from this
      apply h
      simp_all only [mem_preimage, y]
    · intro x hx
      simp_all
      apply h hx
  }
lemma restrict_preimage_equal_iff
  {α : I -> Type*}
  [∀i, Inhabited (α i)]
  {J : Set I}
  {s t : Set (∀j : J, α j)}
  : (J.restrict ⁻¹' s = J.restrict ⁻¹' t) ↔ s = t := by {
    constructor <;> intro h
    · ext x
      let y := choose (Subtype.exists_pi_extension x)
      have hy : J.restrict y = x := choose_spec (Subtype.exists_pi_extension x)
      rw [<- hy]
      suffices y ∈ J.restrict ⁻¹' s <-> y ∈ J.restrict ⁻¹' t from this
      rw [<- h]
    · rw [h]
  }

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
  : (compProd' μ K).map p.fst = μ := by {
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

lemma restrict_equiv_prod_fst
  (α : ℕ -> Type*)
  [∀m, MeasurableSpace (α m)]
  (n: ℕ)
  : restrict₂ (π := α) (le_to_subset <| Nat.le_add_right n 1)
    ∘ ProdLikeM.equiv.symm
    = (Prod.fst (α := ⇑α {k | k <= n}) (β := α (n+1)))
    := by {
      ext x : 1
      unfold ProdLikeM.equiv
      simp
      conv => lhs; rhs; apply ProdLikeM.insert_n_plus_1_apply_inv
      ext y
      simp [show ↑y <= n from y.2]
      rfl
    }
lemma restrict_prod_fst
  (α : ℕ -> Type*)
  [∀m, MeasurableSpace (α m)]
  (n: ℕ)
  : restrict₂ (π := α) (le_to_subset <| Nat.le_add_right n 1)
    = (ProdLikeM.insert_n_plus_1 _).fst
    := by rfl

lemma restrict_prod_fst'
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (n m: ℕ)
  : {a | n < a ∧ a <= n+m}.restrict₂ (π := α)
      (show {a | n < a ∧ a <= n+m} ⊆ {a | n < a ∧ a <= n+m+1} by simp; intros; omega)
    = (ProdLikeM.ge_n_insert_m_plus_1 (α := α) n m).fst
    := by {
      rfl
    }

def Kernel.apply_fst
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (K : Kernel (α × β) γ)
  (a : α)
  : Kernel β γ
  := K.comap (λ b => (a, b)) (measurable_prod_mk_left)
  -- where
  -- toFun := λ b => K (a, b)
  -- measurable' := Measurable.comp (Kernel.measurable K) measurable_prod_mk_left

instance
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (K : Kernel (α × β) γ)
  [mK: IsSFiniteKernel K]
  : IsSFiniteKernel (Kernel.apply_fst K a) := by {
    unfold Kernel.apply_fst
    infer_instance
  }

instance
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (K : Kernel (α × β) γ)
  [mK: IsMarkovKernel K]
  : IsMarkovKernel (Kernel.apply_fst K a) := by {
    unfold Kernel.apply_fst
    infer_instance
  }

def Kernel.compProd_apply
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (K : Kernel α β)
  (L : Kernel (α × β) γ)
  [mK : IsMarkovKernel K]
  [mL: IsMarkovKernel L]
  : (K ⊗ₖ L) a = K a ⊗ₘ (Kernel.apply_fst L a) := by {
    ext s hs
    induction s, hs using induction_on_inter with
    | h_eq => exact generateFrom_prod.symm
    | h_inter => exact isPiSystem_prod
    | empty => simp
    | basic s hs => {
      simp at hs
      obtain ⟨s₁, ⟨hs₁, ⟨s₂, ⟨hs₂, hs⟩⟩⟩⟩ := hs
      rw [<- hs]
      rw [<- setLIntegral_one,  Kernel.setLIntegral_compProd]
      rw [<- setLIntegral_one,  Measure.setLIntegral_compProd]
      congr
      all_goals {
        try assumption
        try exact measurable_const
      }
    }
    | compl s hs => {
      rw [prob_compl_eq_one_sub hs]
      rw [prob_compl_eq_one_sub hs]
      simp_all only
    }
    | iUnion A pwd hA hAeq => {
      repeat rw [measure_iUnion pwd hA]
      congr
      ext i
      exact hAeq i
    }
  }

def Kernel.apply_fst'
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace αβ ]
  [MeasurableSpace γ]
  (K : Kernel αβ γ)
  [p : ProdLikeM αβ α β]
  (a : α)
  : Kernel β γ
  := K.comap (λ b => p.equiv.symm (a, b))
    (by {
      apply Measurable.comp
      exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
      exact measurable_prod_mk_left
    })
  -- where
  -- toFun := λ b => K (a, b)
  -- measurable' := Measurable.comp (Kernel.measurable K) measurable_prod_mk_left

instance
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace αβ ]
  [MeasurableSpace γ]
  (K : Kernel αβ γ)
  [p : ProdLikeM αβ α β]
  [mK : IsMarkovKernel K]
  (a : α)
  : IsMarkovKernel (Kernel.apply_fst' (p:=p) K a) := by {
    unfold Kernel.apply_fst'
    infer_instance
  }

lemma Kernel.compProd'_apply
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace αβ]
  [MeasurableSpace γ]
  [MeasurableSpace βγ]
  (K : Kernel α β)
  (L : Kernel αβ γ)
  [mK : IsMarkovKernel K]
  [mL: IsMarkovKernel L]
  [p : ProdLikeM αβ α β]
  [q : ProdLikeM βγ β γ]
  (a : α)
  : (K ⊗ₖ' L) a = (K a) ⊗ₘ' (Kernel.apply_fst' L a) := by {
    ext s hs
    rw [Kernel.compProd'_def, compProd'_def]
    unfold change_right change_left
    simp only [Equiv.invFun_as_coe, MeasurableEquiv.coe_toEquiv_symm]
    rw [Kernel.map_apply]
    rw [Kernel.compProd_apply]
    rfl
    exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
  }

lemma Kernel.finiteCompLift
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ ]
  (K : ∀m, Kernel (⇑α {k|k <= m}) (α (m+1)))
  [mK : ∀m, IsMarkovKernel (K m)]
  {n m k: ℕ}
  (hnm : n <= m)
  : (FiniteCompKernelNat K k m).map ({a | k < a ∧ a <= k+n+1}.restrict₂ (by simp; intros; omega))
  = (FiniteCompKernelNat K k n)
  := by {
  ext x s hs
  revert n
  induction m with
  | zero => {
    intro n hnm
    rw [Nat.le_zero] at hnm
    subst hnm
    unfold restrict₂
    simp
    }
  | succ m hm => {
    intro n hnm
    intro s hs
    generalize_proofs hresm
    wlog hn₀ : n <= m
    {
      have hn : n = m+1 := by omega
      subst hn
      rw [show restrict₂ hresm = id by rfl]
      simp only [coe_setOf, mem_setOf_eq, Kernel.map_id]
    }
    rw [Kernel.map_apply, Measure.map_apply]
    conv => rhs; tactic => {
      rw [<- hm]
      exact hn₀
      exact hs
    }
    generalize_proofs hresn
    have hres : {k' | k < k' ∧ k' <= k+m+1} ⊆ {k' | k < k' ∧ k' <= k+(m+1)+1} := by simp; intros; omega
    rw [show restrict₂ hresm = (restrict₂ hresn) ∘  (restrict₂ hres) by rfl]
    rw [preimage_comp]
    rw [Kernel.map_apply, Measure.map_apply]
    generalize hst :restrict₂ hresn ⁻¹' s = t
    have ht : MeasurableSet t := by {
      rw [<- hst]
      apply MeasurableSet.preimage
      exact hs
      apply measurable_restrict₂
    }
    rw [show restrict₂ hres = (ProdLikeM.ge_n_insert_m_plus_1_plus_1 (α := α) k m).fst by rfl]
    conv => lhs; unfold FiniteCompKernelNat; rfl
    rw [Kernel.compProd'_apply]
    rw [<- Measure.map_apply]
    rw [compProd'_fst_is_measure]
    all_goals {
      try assumption
      try apply measurable_restrict₂
      try simp; intros; omega
    }
  }
}
lemma Measure.finiteCompLift
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  -- [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ ]
  (K : ∀m, Kernel (⇑α {k|k <= m}) (α (m+1)))
  [mK : ∀m, IsMarkovKernel (K m)]
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
    rw [Nat.le_zero] at hnm
    subst hnm
    unfold restrict₂
    simp
    }
  | succ m hm => {
    intro n hnm
    have hresm := le_to_subset (Nat.le_add_right m 1)
    have heqm : ∀ (s : Set (⇑α {k | k ≤ m})), MeasurableSet s →
    (Measure.map (restrict₂ hresm) (FiniteCompMeasureKernelNat μ K (m + 1))) s
      = (FiniteCompMeasureKernelNat μ K m) s := by {
        intro s hs
        rw [restrict_prod_fst]
        unfold FiniteCompMeasureKernelNat
        conv => lhs; arg 1; {
          apply compProd'_fst_is_measure
            -- (p := ProdLikeM.insert_n_plus_1 m)
            (FiniteCompMeasureKernelNat μ K m) (K m)
        }
        match m with
        | 0 => {
          simp only [Nat.reduceAdd]
          rfl
        }
        | m + 1 => {
          simp only [Nat.reduceAdd]
          rfl
        }
      }
    intro s hs
    generalize_proofs hres
    by_cases h0 : n = m + 1
    · subst h0
      rw [show restrict₂ hres = id by rfl]
      simp
    by_cases h1 : n = m
    · subst h1
      exact heqm s hs
    have h : n <= m := by omega
    have hresn := le_to_subset h
    rw [Measure.map_apply (measurable_restrict₂ hres) hs]
    rw [show restrict₂ hres = restrict₂ hresn ∘ (restrict₂ hresm) from rfl]
    let t := restrict₂ hresn ⁻¹' s
    have ht : MeasurableSet t := MeasurableSet.preimage hs (measurable_restrict₂ _)
    rw [<- comp_preimage]
    rw [show restrict₂ hresn ⁻¹'s = t from rfl]
    rw [<- Measure.map_apply (measurable_restrict₂ hresm) ht]
    specialize heqm t ht
    rw [heqm]
    unfold t
    rw [<- Measure.map_apply (measurable_restrict₂ hresn) hs]
    exact hm h s hs
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


lemma cylinders_setSemiRing (α : ℕ -> Type*) [mα : ∀n, MeasurableSpace (α n)]
  : IsSetSemiring (cylinders α)
  := SetAlgebraIsSetSemiRing (cylinders_SetAlgebra α)

lemma univ_cylinder_n (n : ℕ) (α : ℕ -> Type*) [mα : ∀n, MeasurableSpace (α n)] : univ ∈ cylinder_n α n := by {
  unfold cylinder_n
  simp
  use univ
  simp
}
lemma univ_cylinders (α : ℕ -> Type*) [mα : ∀n, MeasurableSpace (α n)] : univ ∈ cylinders α := by {
  unfold cylinders
  simp
  use 0
  exact univ_cylinder_n 0 α
}

def compose
  {α : I -> Type*} {J K : Set I}
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (∀i:K, α i)) (i : I) : α i :=
    if h : i ∈ J then
      ω₁ ⟨i,h⟩
    else if h: i ∈ K then
      ω₂ ⟨i,h⟩
    else default

def compose'
  {α : I -> Type*} {J K L : Set I}
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (∀i:K, α i)) := L.restrict (compose ω₁ ω₂)

def blowup
  {α : I -> Type*}
  {i : I}
  (a : α i)
  : (∀j : ({i} : Set I), α j) := by {
    intro j
    rw [j.2]
    exact a
  }
@[measurability]
lemma measurable_blowup
  {α : I -> Type*}
  [mα : ∀i, MeasurableSpace (α i)]
  {i : I}
  : Measurable (blowup (α := α) (i:=i)) := by {
    unfold blowup
    simp
    generalize_proofs h
    have h' : ∀j : ({i} : Set I), HEq (mα i) (mα j) := by aesop
    have h: ∀a, ∀j, cast (h j) a = MeasurableEquiv.cast (h j) (h' j) a := by {
      intro a j
      rfl
    }
    simp_rw [h]
    apply measurable_pi_lambda
    intro a
    generalize_proofs h1 h2
    exact MeasurableEquiv.measurable (MeasurableEquiv.cast h1 h2)
  }

def compapp
  {α : I -> Type*} {J L : Set I}
  {i : I}
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (α i))
  := L.restrict (compose ω₁ <| blowup ω₂)

lemma compapp_apply
  {α : I -> Type*} {J L : Set I}
  {i j : I}
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (α i))
  (h : j ∈ J)
  (h2 : j ∈ L)
  : compapp (L := L) ω₁ ω₂ ⟨j, h2⟩ = ω₁ ⟨j, h⟩ := by {
    simp [compapp, compose, blowup, *]
  }

@[measurability]
theorem measurable_compose
  {α : I -> Type*} {J K : Set I}
  [∀i, Inhabited (α i)]
  [∀n, MeasurableSpace (α n)]
  : Measurable fun ω : (⇑α J × ⇑α K) => compose ω.1 ω.2 := by {
    unfold compose
    apply measurable_pi_lambda
    intro i
    by_cases hJ : i ∈ J
    simp [hJ]
    apply Measurable.eval
    apply measurable_fst
    by_cases hK : i ∈ K
    simp [hJ, hK]
    apply Measurable.eval
    apply measurable_snd
    simp [hJ, hK]
  }
@[measurability]
theorem measurable_compose_snd
  {α : I -> Type*} {J K : Set I}
  [∀i, Inhabited (α i)]
  [∀n, MeasurableSpace (α n)]
  (ω₁ : (∀i:J, α i))
  : Measurable (compose (α := α) (K := K) ω₁) := by {
    unfold compose
    apply measurable_pi_lambda
    intro i
    by_cases hJ : i ∈ J
    simp [hJ]
    by_cases hK : i ∈ K
    simp [hJ, hK]
    apply measurable_pi_apply
    simp [hJ, hK]
  }
@[measurability]
theorem measurable_compose'
  {α : I -> Type*} {J K L : Set I}
  [∀i, Inhabited (α i)]
  [∀n, MeasurableSpace (α n)]
  : Measurable fun (ω : ⇑α J × ⇑α K) => (compose' (L:=L) (α := α) ω.1 ω.2) := by {
    unfold compose'
    apply Measurable.comp'
    exact measurable_restrict L
    exact measurable_compose
  }
@[measurability]
theorem measurable_compose'_fst
  {α : I -> Type*} {J K L : Set I}
  [∀i, Inhabited (α i)]
  [∀n, MeasurableSpace (α n)]
  (ω₂ : (∀i:K, α i))
  : Measurable fun x => (compose' (L:=L) (α := α) (J:=J) x ω₂) := by {
    -- let f := fun (x : ⇑α J × ⇑α K) => (compose' (L:=L) (α := α) x.1 x.2)
    suffices Measurable λ x => (uncurry compose') (x, ω₂) by exact this
    apply Measurable.comp'
    exact measurable_compose'
    apply Measurable.prod <;> simp only
    exact measurable_id
    exact measurable_const
  }

@[measurability]
lemma measurable_compapp_snd
  {α : I -> Type*} {J L : Set I}
  [∀i, Inhabited (α i)]
  [∀n, MeasurableSpace (α n)]
  (ω₁ : (∀i:J, α i))
  (i : I)
  : Measurable (compapp (L:=L) (i:=i) ω₁) := by {
    unfold compapp
    apply Measurable.comp'
    exact measurable_restrict L
    apply Measurable.comp'
    exact measurable_compose_snd ω₁
    apply measurable_blowup
  }

def compose₃
  {α : I -> Type*} {J K L M : Set I}
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (∀i:K, α i))
  (ω₃ : (∀i:L, α i))
  := M.restrict fun j =>
    if h : j ∈ J then
      ω₁ ⟨j,h⟩
    else if h: j ∈ K then
      ω₂ ⟨j,h⟩
    else if h: j ∈ L then
      ω₃ ⟨j,h⟩
    else
      default

def compapp₃
  {α : I -> Type*} {J K M : Set I}
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (∀i:K, α i))
  {i : I}
  (ω₃ : α i)
  := M.restrict fun j =>
    if h : j ∈ J then
      ω₁ ⟨j,h⟩
    else if h: j ∈ K then
      ω₂ ⟨j,h⟩
    else if h: j = i then
      cast (by aesop) ω₃
    else
      default

def restrict' {α : I -> Type*}
  [∀i, Inhabited (α i)]
  {J : Set I} (ω : (∀i:J, α i))
  (K : Set I)
  (k : K)
  : α k
  := if h : (k : I) ∈ J then
    ω ⟨k,h⟩
  else default

-- @[simp]
lemma compose₃_heq
  {α : I -> Type*}
  {J K L M : Set I}
  {J' K' L' M' : Set I}
  [∀i, Inhabited (α i)]
  (hJ : J=J')
  (hK : K=K')
  (hL : L=L')
  (hM : M=M')
  : HEq
    (compose₃ (α := α) (J:=J) (K:=K) (L:=L) (M:=M))
    (compose₃ (α := α) (J:=J') (K:=K') (L:=L') (M:=M')) := by {
      subst hJ hK hL hM
      rfl
    }

lemma compapp₃_heq
  {α : I -> Type*}
  {J K M : Set I}
  {J' K' M' : Set I}
  (i i' : I)
  [∀i, Inhabited (α i)]
  (hJ : J=J')
  (hK : K=K')
  (hM : M=M')
  (hi : i = i')
  : HEq
    (compapp₃ (α := α) (J:=J) (K:=K) (M:=M) (i:=i))
    (compapp₃ (α := α) (J:=J') (K:=K') (M:=M') (i:=i')) := by {
      subst hJ hK hM hi
      rfl
    }

lemma compose'_compapp_compapp₃
  {α : I -> Type*}
  {J K L M : Set I}
  (hL : J ∪ K ⊆ L)
  [∀i, Inhabited (α i)]
  (ω₁ : (∀i:J, α i))
  (ω₂ : (∀i:K, α i))
  {i : I}
  (hi : i ∈ L)
  (ω₃ : α i)
  : compose' ω₁ (compapp (L:=L) ω₂ ω₃) = compapp₃ (M:=M) ω₁ ω₂ ω₃ := by {
    have hJ : J ⊆ L := by aesop
    have hK : K ⊆ L := by aesop
    ext x
    simp [compose', compapp₃, compose, compapp]
    by_cases h : (x : I) ∈ J
    <;> by_cases h' : (x : I) ∈ K
    <;> by_cases h'' : (x : I) = i
    <;> simp [h,h']
    -- aesop
    intro g; exfalso; apply g; exact hK h'
    intro g; exfalso; apply g; exact hK h'
    have g : (x : I) ∈ L := by aesop
    simp [g, h'', hi]
    rfl
    simp only [↓reduceDIte, ite_self, h'']
  }

@[measurability]
lemma measurable_compapp₃_fst
  {α : I -> Type*}
  {J K M : Set I}
  [∀i, Inhabited (α i)]
  [∀n, MeasurableSpace (α n)]
  (ω₂ : (∀i:K, α i))
  {i : I}
  (ω₃ : α i)
  : Measurable fun ω₁ => (compapp₃ (M:=M) (J:=J) (α := α) ω₁ ω₂ ω₃) := by {
    unfold compapp₃
    apply Measurable.comp'
    exact measurable_restrict M
    apply measurable_pi_lambda
    intro j
    by_cases hJ: j ∈ J
    · simp only [hJ, ↓reduceDIte]
      apply measurable_pi_apply
    · by_cases hK: j ∈ K
      · simp only [hJ, ↓reduceDIte, hK, measurable_const]
      · by_cases hi: j = i
        · simp only [hJ, ↓reduceDIte, hK, measurable_const]
        · simp only [hJ, ↓reduceDIte, hK, hi, measurable_const]
  }
