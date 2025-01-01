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

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory

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

lemma ge0eq0 (i : {k | k <= n}) (h : ↑i ∉ {k | 0 < k ∧ k <= n}) : (i : ℕ) = 0 := by {
  simp at h
  by_contra hi
  have hi2 : (i : ℕ) > 0 := by exact Nat.zero_lt_of_ne_zero hi;
  specialize h hi2
  have hi3 : i < (i : ℕ) := calc i <= n := i.2
    _ < i := h
  exact (lt_self_iff_false ↑i).mp hi3
}

def equiv_2 {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  :(∀k : {k| k <= n}, α k) ≃ᵐ (α 0) × (∀k :{k | 0 < k ∧ k <= n}, α k) where
  toFun x := ⟨
    x ⟨0, by simp⟩,
    fun i : {k | 0 < k ∧ k <= n} =>
    x ⟨↑i, by obtain ⟨x,hx⟩ := i; simp at hx; simp; omega ⟩
    ⟩
  invFun := fun (x, y) => fun i => if hi : ↑i ∈ {k | 0 < k ∧ k <= n} then y ⟨↑i, hi⟩ else
    have hi0 : (i : ℕ) = 0 := ge0eq0 i hi
    have h : α 0 = α ↑i := by rw [hi0];
    have h' : HEq (mα (0)) (mα ↑i) := by rw [hi0]
    MeasurableEquiv.cast h h' x
  left_inv := by {
    -- simp
    intro x
    ext i
    by_cases hi : ↑i ∈ {k | 0 < k ∧ k <= n} <;> simp [hi]
    · rfl
    · have h := ge0eq0 i hi
      unfold MeasurableEquiv.cast
      simp
      rw [@cast_eq_iff_heq]
      generalize_proofs h0
      have hi2 : i = ⟨0,h0⟩ := by apply_fun (·.1); simp; assumption; exact Subtype.val_injective
      rw [hi2]
  }
  right_inv := by {
    intro x
    ext i
    · rfl
    · simp; rfl
  }
  measurable_toFun := by {
    -- measurability
    simp_all only [coe_setOf, mem_setOf_eq, Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, eq_mpr_eq_cast,
      Equiv.coe_fn_mk]
    apply Measurable.prod
    simp_all only
    apply measurable_pi_apply
    simp_all only [Int.reduceNeg]
    apply measurable_pi_lambda
    intro a
    simp_all only [Int.reduceNeg]
    obtain ⟨val, property⟩ := a
    simp_all only [Int.reduceNeg]
    apply measurable_pi_apply
  }
  measurable_invFun := by {
    simp
    apply measurable_pi_lambda
    intro i
    by_cases hi :  0 < (i: ℕ) ∧ (i:ℕ) <= n  <;> simp [hi]
    · -- measurability
      obtain ⟨val, property⟩ := i
      obtain ⟨left, right⟩ := hi
      simp_all only
      apply Measurable.eval
      simp_all only
      apply measurable_snd
    · -- measurability
      apply Measurable.comp
      apply MeasurableEquiv.measurable
      exact measurable_fst
  }

lemma not_le_n_is_n_add_one_0 {n : ℕ} {i : {k |0 < k ∧ k <= n+1}} (h : ¬(0 < (i :ℕ) ∧ i <= n)) : i = ⟨n+1, by simp⟩ := by {
  -- rw [Nat.not_le_eq] at h
  apply_fun (·.1)
  simp
  push_neg at h
  specialize h i.2.1
  have h2 : (i :ℕ) <= n + 1 := by exact i.2.2
  omega
  exact Subtype.val_injective
}

def equiv_3 {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  :(∀k : {k| 0 < k ∧ k <= n + 1}, α k) ≃ᵐ (∀k : {k | 0 < k ∧ k <= n}, α k) × (α (n+1)) where
  toFun x := ⟨fun i : {k | 0 < k ∧ k <= n} =>
    x ⟨↑i, by obtain ⟨x,hx⟩ := i; simp at hx; simp; omega ⟩,
    x ⟨n+1, by simp⟩⟩
  invFun := fun (x, y) => fun i => if hi : 0 < (i :ℕ) ∧ (i : ℕ) <= n then x ⟨↑i, hi⟩ else
    have h : α (n+1) = α ↑i := by rw [not_le_n_is_n_add_one_0 hi]
    have h' : HEq (mα (n+1)) (mα ↑i) := by rw [not_le_n_is_n_add_one_0 hi]
    MeasurableEquiv.cast h h' y
  left_inv := by {
    simp
    intro x
    ext i
    by_cases hi : 0 < (i : ℕ) ∧ i <= n <;> simp [hi]
    have h := not_le_n_is_n_add_one_0 hi
    subst h
    rfl
  }
  right_inv := by {
    intro x
    ext i
    · simp [show 0 < ↑i ∧ ↑i <= n from i.2]; rfl
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
      obtain ⟨left, right⟩ := property
      simp_all only [↓reduceDIte]
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

instance prod_equiv_2 {α : ℕ -> Type*} [∀n, MeasurableSpace (α n)] (n : ℕ)
  : ProdLikeM (∀k : {k| k <= n + 1 }, α k) (α 0) (∀(k : {k | 0 < k ∧ k <= n + 1}), α k) where
  equiv := equiv_2 (n+1)

instance prod_equiv_3 {α : ℕ -> Type*} [∀n, MeasurableSpace (α n)] (n : ℕ)
  : ProdLikeM (∀k : {k| 0 < k ∧ k <= n + 1 }, α k) (∀(k : {k | 0 < k ∧ k <= n}), α k) (α (n+1)) where
  equiv := equiv_3 (n)

class EquivalentMeasurableSpace (α : Type*) (β : Type*)
  [MeasurableSpace α] [MeasurableSpace β] where
  equiv : α ≃ᵐ β
def EquivalentMeasurableSpace.symm
  {α : Type*} {β : Type*}
  [MeasurableSpace α] [MeasurableSpace β]
  (e : EquivalentMeasurableSpace α β)
  : EquivalentMeasurableSpace β α
  := ⟨e.equiv.symm⟩

def convert_measure [MeasurableSpace α] [MeasurableSpace β]
  [e : EquivalentMeasurableSpace α β] (μ : Measure α) := μ.map e.equiv

def convert_kernel
[MeasurableSpace α] [MeasurableSpace β]
[MeasurableSpace γ] [MeasurableSpace δ]
  [e : EquivalentMeasurableSpace α γ]
  [f : EquivalentMeasurableSpace β δ]
  (K : Kernel α β)
  : Kernel γ δ
  :=
  have h : Measurable (e.equiv.symm)
    := MeasurableEquiv.measurable EquivalentMeasurableSpace.equiv.symm
  let K₁ := (K.map f.equiv)
  let K₂ := (K₁.comap e.equiv.symm h)
  K₂


instance isProb_convert [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α)
  [EquivalentMeasurableSpace α β] [IsProbabilityMeasure μ]
    : IsProbabilityMeasure (convert_measure μ : Measure β)  := by {
      unfold convert_measure
      apply isProbabilityMeasure_map
      apply Measurable.aemeasurable
      apply MeasurableEquiv.measurable
}


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

instance {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)]
(n : ℕ)
  : EquivalentMeasurableSpace (∀k : {k | n < k ∧ k <= n+1}, α k) (α (n+1)) where
  equiv :=
      let U : Unique {k | n < k ∧ k <= n+1} := by {
          rw [show {k | n < k ∧ k <= n+1} = {n+1} by ext;simp;omega]
          infer_instance
      }
      let τ := MeasurableEquiv.piUnique'
        (α := ({k | n < k ∧ k <= n+1})) (β := fun x => α ↑x) ⟨n+1, by simp⟩
      τ
instance [MeasurableSpace α] [MeasurableSpace β] [e : EquivalentMeasurableSpace α β]
: EquivalentMeasurableSpace β α where
  equiv := e.equiv.symm



def FiniteCompMeasureKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  -- (K : ∀m, Kernel (∀k ≤ m, α k) (α (m+1)))
  : (n : ℕ) -> Measure (∀k : {k|k <= n}, α k)
  | 0 => convert_measure μ
  | m + 1 => compProd' (FiniteCompMeasureKernelNat μ K m) (K m)

def FiniteCompKernelNat
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  : (n : ℕ) -> Kernel (α 0) (∀k : {k | 0 < k ∧ k <= n+1}, α k)
  | 0 => convert_kernel (K 0)
  | m + 1 =>
  let p : ProdLikeM ((k : ↑{k | k ≤ m + 1}) → α ↑k) (α 0) ((k : ↑{k | 0 < k ∧ k ≤ m + 1}) → α ↑k)
  := by {
    exact prod_equiv_2 m
  }
  -- let q : ProdLikeM ((k : ↑{k | 0 < k ∧ k ≤ m + 1 + 1}) → α ↑k) ((k : ↑{k | 0 < k ∧ k ≤ m + 1}) → α ↑k) (α (m + 1 + 1))
  -- := by {
  --   exact?
  -- }
  Kernel.compProd' (FiniteCompKernelNat K m) (K (m+1)) (p := p)

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
  : Measurable (kernel_slice K B (p := p)) := by {
    unfold kernel_slice ProdLikeM.slice
    let B' : Set (α × β) := @image γ (α × β) p.equiv B
    -- p.equiv '' B
    have hB' : MeasurableSet B' := by {
      unfold B'
      apply (MeasurableEquiv.measurableSet_image p.equiv).mpr ?_
      exact hB
    }
    have h : ∀a, {b | ProdLikeM.equiv.symm (a, b) ∈ B} = {b | (a, b) ∈ B'} := by {
      unfold B';
      intro a
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

lemma restrict_equiv_prod_fst
  (α : ℕ -> Type*)
  [∀m, MeasurableSpace (α m)]
  -- [∀m, Inhabited (α m)]
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
lemma restrict_prod_fst
  (α : ℕ -> Type*)
  [∀m, MeasurableSpace (α m)]
  -- [∀m, Inhabited (α m)]
  (n: ℕ)
  : restrict₂ (π := α) (le_to_subset <| Nat.le_add_right n 1)
    = ProdLikeM.fst
    := by rfl

lemma KernelLift
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  -- [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
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
    have heqm : ∀ (s : Set ((a : ↑{k | k ≤ m}) → α ↑a)), MeasurableSet s →
    (Measure.map (restrict₂ hresm) (FiniteCompMeasureKernelNat μ K (m + 1))) s
      = (FiniteCompMeasureKernelNat μ K m) s := by {
        intro s hs
        rw [restrict_prod_fst]
        unfold FiniteCompMeasureKernelNat
        rw [compProd'_fst_is_measure]
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

theorem measurable_compose
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

      -- let
      -- let Q n m ω' := sorry


      -- let Q : (n : ℕ) -> (∀k : {k | k <= n}, α k) -> (m : ℕ) -> Measure _
      --     :=  fun n ω m =>
      --       FiniteCompMeasureKernelNat (α := fun k => α (k-m)) (K n ω) (λ k => K (k-n)) m
      -- unfold AddContent.sContinuousInEmpty
      -- intro A
      -- intro hA
      -- intro _
      -- intro hAconv


      by_contra hcontra
      -- have hinf :
      simp at hcontra



    · unfold MeasureKernelSequenceContent
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

lemma test : ({0,1}:Set ℕ) = {k|k < 2} := by exact toFinset_inj.mp rfl

-- lemma test2 : (J : Set I) (hJ : Finite J) : Finset J :=

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
