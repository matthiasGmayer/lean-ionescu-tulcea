/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea.prodLike
import IonescuTulcea.inlinesimp
import Mathlib

set_option autoImplicit true
open Function Set Classical ENNReal


noncomputable section

/-!
This file defines canonical equivalences between measurable spaces
and for productlike structure.
-/
namespace IndexedFamilies

open MeasureTheory MeasurableSpace Measurable ProductLike

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike
instance project_coerce {I : Type*} : CoeFun (I -> Type _) (fun _ => Set I -> Type _) where
  coe α J := ∀k : J, α k
open ProbabilityTheory

class EquivalentMeasurableSpace (α : Type*) (β : Type*)
  [MeasurableSpace α] [MeasurableSpace β] where
  equiv : α ≃ᵐ β

instance EquivalentMeasurableSpace.refl [MeasurableSpace α]: EquivalentMeasurableSpace α α := ⟨MeasurableEquiv.refl α⟩
@[simp]
lemma EquivalentMeasurableSpace.refl_equiv [MeasurableSpace α]
  : (EquivalentMeasurableSpace.refl : EquivalentMeasurableSpace α α).equiv
    = MeasurableEquiv.refl α := by rfl

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

instance [MeasurableSpace α] [MeasurableSpace β] [e : EquivalentMeasurableSpace α β]
: EquivalentMeasurableSpace β α where
  equiv := e.equiv.symm

def MeasurableEquiv.unique {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I)
  : α default ≃ᵐ α i :=
    have h : α default = α i := by rw [Unique.default_eq i]
    MeasurableEquiv.cast h (by rw [Unique.default_eq i])

@[simp]
lemma MeasurableEquiv.unique_apply {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I) (x : α default)
  : MeasurableEquiv.unique α i x =
    have h : α default = α i := by rw [Unique.default_eq i]
    MeasurableEquiv.cast h (by rw [Unique.default_eq i]) x := by rfl

@[simp]
lemma MeasurableEquiv.unique_apply_inv {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I) (x : α i)
  : (MeasurableEquiv.unique α i).symm x =
    have h : α default = α i := by rw [Unique.default_eq i]
    (MeasurableEquiv.cast h (by rw [Unique.default_eq i])).symm x := by rfl

def MeasurableEquiv.piUnique' {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I)
  : (∀ i, α i) ≃ᵐ α i :=
    (MeasurableEquiv.piUnique α).trans
    (unique α i)

@[simp]
lemma MeasurableEquiv.piUnique'_apply {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I) (x : ∀i, α i)
  : MeasurableEquiv.piUnique' α i x = unique α i (MeasurableEquiv.piUnique α x) := by rfl

@[simp]
lemma MeausrableEquiv.piUnique'_apply_inv {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I) (x : α i)
  : (MeasurableEquiv.piUnique' α i).symm x =
    (MeasurableEquiv.piUnique α).symm ((MeasurableEquiv.unique α i).symm x) := by rfl

def MeasurableEquiv.piUnique'' {I : Type*} {J : Set I} [Unique J]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I)
  (hi : i ∈ J)
  : (∀ i : J, α i) ≃ᵐ α i :=
    MeasurableEquiv.piUnique' (fun i : J => α i) ⟨i,hi⟩

@[simp]
lemma MeasurableEquiv.piUnique''_apply {I : Type*} {J : Set I} [Unique J]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I) (hi : i ∈ J) (x : ∀i : J, α i)
  : MeasurableEquiv.piUnique'' α i hi x =
    MeasurableEquiv.piUnique' (fun i : J => α i) ⟨i,hi⟩ x := by rfl

@[simp]
lemma MeasurableEquiv.piUnique''_apply_inv {I : Type*} {J : Set I} [Unique J]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I) (hi : i ∈ J) (x : α i)
  : (MeasurableEquiv.piUnique'' α i hi).symm x =
    (MeasurableEquiv.piUnique' (fun i : J => α i) ⟨i,hi⟩).symm x := by rfl

instance set_le_0_unique : Unique {k | k <= 0} where
  default := ⟨0, by simp⟩
  uniq := by {
    intros x
    ext
    simp
    suffices (x :ℕ) <= 0 by omega
    exact x.2
  }

@[simp]
lemma default_le_0 : simp% (default : {k | k ≤ 0}) = ⟨0,by simp⟩ := by rfl

instance EquivMS_0 {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)]
  : EquivalentMeasurableSpace (⇑α {k | k <= 0}) (α 0) where
  equiv :=
      let τ := MeasurableEquiv.piUnique'
        (I := ({k | k <= 0})) (α := fun x => α ↑x) ⟨0, by simp⟩
      τ


@[simp]
lemma MeasurableEquiv.cast_apply {α β : Type u}
  [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  (h : α = β) (h' : HEq mα mβ) (x : α) : MeasurableEquiv.cast h h' x = cast h x := by rfl

@[simp]
lemma EquivMS_0_equiv_apply {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)]
  (x : ⇑α {k | k <= 0})
  : simp% (EquivMS_0.equiv x) = x ⟨0, by simp⟩ := by {
    unfold EquivalentMeasurableSpace.equiv EquivMS_0
    simp
    congr
  }

instance set_n_unique (n : ℕ) : Unique {k | n < k ∧ k <= n + 1} where
  default := ⟨n+1, by simp⟩
  uniq := by {
    intros x
    ext
    simp
    let h := x.2
    simp only [mem_setOf_eq] at h
    omega
}

@[simp]
lemma default_n : simp% (default : {k | n < k ∧ k <= n + 1}) = ⟨n+1, by simp⟩ := by {
  rfl
}


instance EquivMS_n {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)] (n : ℕ)
  : EquivalentMeasurableSpace (⇑α {k | n < k ∧ k <= n+1}) (α (n+1)) where
  equiv :=
      let τ := MeasurableEquiv.piUnique'
        (I := ({k | n < k ∧ k <= n+1})) (α := fun x => α ↑x) ⟨n+1, by simp⟩
      τ

@[simp]
lemma EquivMS_n_apply {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)] (n : ℕ)
  (x : ∀k : {k | n < k ∧ k <= n+1}, α k)
  : simp% ((EquivMS_n n).equiv x) = x ⟨n+1, by simp⟩ := by {
    unfold EquivalentMeasurableSpace.equiv EquivMS_n
    simp
    congr
}

@[simp]
lemma EquivMS_n_apply_inv {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)] (n : ℕ)
  (x : α (n+1))
  : simp% ((EquivMS_n n).equiv.symm x) = uniqueElim x := by {
    rfl
  }

def Equiv.pi_equiv
  {α : I -> Type*}
  {J K L : Set I}
  (h : L = J ∪ K)
  (h_disjoint : Disjoint J K)
  : (⇑α L) ≃ (⇑α J) × (⇑α K) where
  toFun x :=
    have hJ : J ⊆ L := by aesop
    have hK : K ⊆ L := by aesop
    ⟨J.restrict₂ hJ x, K.restrict₂ hK x⟩
  invFun := fun (x,y) => fun ⟨i, hi⟩ =>
    if hJ : i ∈ J then
      x ⟨i, hJ⟩
    else
      y ⟨i, by aesop⟩
  left_inv := by {
    intro x
    ext i
    by_cases hJ : (i : I) ∈ J <;> simp [hJ]
  }
  right_inv := by {
    intro x
    ext i <;> simp [i.2]
    have hJ : (i : I) ∉ J := by rw [@disjoint_right] at h_disjoint; aesop
    aesop
  }

@[simp]
lemma Equiv.pi_equiv_apply
  {α : I -> Type*}
  {J K L : Set I}
  (h : L = J ∪ K)
  (h_disjoint : Disjoint J K)
  (x : ⇑α L)
  : simp% (Equiv.pi_equiv h h_disjoint x)
  = (J.restrict₂ (by aesop) x, K.restrict₂ (by aesop) x) := by {
    rfl
  }
@[simp]
lemma Equiv.pi_equiv_apply_inv
  {α : I -> Type*}
  {J K L : Set I}
  (h : L = J ∪ K)
  (h_disjoint : Disjoint J K)
  (x : ⇑α J) (y : ⇑α K)
  : simp% ((Equiv.pi_equiv h h_disjoint).symm (x,y))
  = fun i : L => if hJ : (i : I) ∈ J then x ⟨i,hJ⟩ else y ⟨i, by aesop⟩ := by {
    rfl
  }

def MeasurableEquiv.pi_equiv
  {α : I -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  {J K L : Set I}
  (h : L = J ∪ K)
  (h_disjoint : Disjoint J K)
  : ⇑α L ≃ᵐ ⇑α J × ⇑α K where
  toEquiv := Equiv.pi_equiv h h_disjoint
  measurable_toFun := by {
    apply Measurable.prod
    all_goals {
      apply measurable_restrict₂
      aesop
    }
  }
  measurable_invFun := by {
    unfold Equiv.pi_equiv
    apply measurable_pi_lambda
    intro a
    by_cases hJ : (a : I) ∈ J <;> simp [hJ]
    rw [show (fun c : ⇑α J × ⇑α K => c.1 ⟨a, hJ⟩)
        = (fun c => c ⟨a, hJ⟩) ∘  fun c : ⇑α J × ⇑α K => c.1 by rfl]
    apply Measurable.comp
    apply measurable_pi_apply
    exact measurable_fst
    generalize_proofs hK
    rw [show (fun c : ⇑α J × ⇑α K => c.2 ⟨a, hK⟩)
        = (fun c => c ⟨a, hK⟩) ∘  fun c : ⇑α J × ⇑α K => c.2 by rfl]
    apply Measurable.comp
    apply measurable_pi_apply
    exact measurable_snd
  }
@[simp]
lemma MeasurableEquiv.pi_equiv_apply
  {α : I -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  {J K L : Set I}
  (h : L = J ∪ K)
  (h_disjoint : Disjoint J K)
  (x : ⇑α L)
  : simp% (MeasurableEquiv.pi_equiv h h_disjoint x)
  = (J.restrict₂ (by aesop) x, K.restrict₂ (by aesop) x) := by {
    rfl
  }
@[simp]
lemma MeasurableEquiv.pi_equiv_apply_inv
  {α : I -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  {J K L : Set I}
  (h : L = J ∪ K)
  (h_disjoint : Disjoint J K)
  (x : ⇑α J) (y : ⇑α K)
  : simp% ((MeasurableEquiv.pi_equiv h h_disjoint).symm (x,y))
  = fun i : L => if hJ : (i : I) ∈ J then x ⟨i,hJ⟩ else y ⟨i, by aesop⟩ := by {
    rfl
  }

def MeasurableEquiv.pi_insert_equiv
  {α : I -> Type*}
  [mα : ∀n, MeasurableSpace (α n)]
  {L J : Set I}
  {i : I}
  (h : L = insert i J)
  (hi : i ∉ J)
  : MeasurableEquiv (⇑α L) (⇑α J × α i) :=
    let K : Set I := {i}
    have h_disjoint : Disjoint J K := by aesop
    have h' : L = J ∪ K := by aesop
    let τ : ⇑α L ≃ᵐ (⇑α J × ⇑α K) := MeasurableEquiv.pi_equiv (α := α) h' h_disjoint
    have hi : i ∈ K := by aesop
    let τ₂ : ⇑α J × ⇑α K ≃ᵐ ⇑α J × α i
      := (MeasurableEquiv.refl (⇑α J)).prodCongr
          (MeasurableEquiv.piUnique'' α i hi)
    τ.trans τ₂

@[simp]
lemma MeasurableEquiv.pi_insert_equiv_apply
  {α : I -> Type*}
  [mα : ∀n, MeasurableSpace (α n)]
  {L J : Set I}
  {i : I}
  (h : L = insert i J)
  (hi : i ∉ J)
  (x : ⇑α L)
  : simp% (MeasurableEquiv.pi_insert_equiv h hi x)
  = ({k | k ∈ J}.restrict₂ (by aesop) x, x ⟨i, by aesop⟩) := by {
    rfl
  }

lemma MeasurableEquiv.trans_symm
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (e : MeasurableEquiv α β)
  (f : MeasurableEquiv β γ)
  : (e.trans f).symm = f.symm.trans e.symm := by rfl

@[simp]
lemma MeasurableEquiv.pi_insert_equiv_apply_inv
  {α : I -> Type*}
  [mα : ∀n, MeasurableSpace (α n)]
  {L J : Set I}
  {i : I}
  (h : L = insert i J)
  (hi : i ∉ J)
  (y : ⇑α J × α i)
  : simp% ((MeasurableEquiv.pi_insert_equiv h hi).symm y)
  =  fun j : L => (if hj : (j : I) ∈ J then y.1 ⟨j,hj⟩ else
    cast (show α i = α j by aesop) y.2 : α j) := by {
      rfl
  }


def MeasurableEquiv.insert_n_plus_1
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  : (⇑α {k| k <= n + 1}) ≃ᵐ (⇑α {k | k <= n}) × (α (n+1)) :=
    have h : {k | k <= n + 1} = insert (n+1) {k | k <= n} := by {
      ext; simp; omega
    }
    have hn : n+1 ∉ {k | k ≤ n} := by simp
    MeasurableEquiv.pi_insert_equiv h hn

@[simp]
lemma MeasurableEquiv.insert_n_plus_1_apply
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  (x : ⇑α {k| k <= n + 1})
  : simp% (MeasurableEquiv.insert_n_plus_1 n x)
  = ({k | k <= n}.restrict₂ (by simp; intro a h; omega) x, x ⟨n+1, by simp⟩) := by {
    rfl
  }

@[simp]
lemma MeasurableEquiv.insert_n_plus_1_apply_inv
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  (y : ⇑α {k | k <= n} × α (n+1))
  : simp% ((MeasurableEquiv.insert_n_plus_1 n).symm y)
  =  fun j : {k | k <= n+1} => (if hj : (j : ℕ) <= n then y.1 ⟨j,hj⟩ else
    cast
    (show α (n+1) = α j by {
      let h := j.2
      simp only [mem_setOf_eq] at h
      congr
      omega
    })
    y.2 : α j) := by {
      unfold insert_n_plus_1
      simp
      generalize_proofs h h2 h3 h4
      conv => lhs; apply pi_insert_equiv_apply_inv
      ext j
      by_cases h : (j : ℕ) <= n <;> simp [h]
  }

instance ProdLikeM.insert_n_plus_1
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  : ProdLikeM (⇑α {k| k <= n + 1}) (⇑α {k | k <= n}) (α (n+1))
  := ⟨ MeasurableEquiv.insert_n_plus_1 n ⟩

@[simp]
lemma ProdLikeM.insert_n_plus_1_apply
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  (x : ⇑α {k| k <= n + 1})
  : simp%((ProdLikeM.insert_n_plus_1 n).equiv x)
  = ({k | k <= n}.restrict₂ (by simp; intro a h; omega) x, x ⟨n+1, by simp⟩) := by {
    rfl
  }
@[simp]
lemma ProdLikeM.insert_n_plus_1_apply_inv
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  (y : ⇑α {k | k <= n} × α (n+1))
  : simp% ((ProdLikeM.insert_n_plus_1 n).equiv.symm y)
  =  fun j : {k | k <= n+1} => (if hj : (j : ℕ) <= n then y.1 ⟨j,hj⟩ else
    cast
    (show α (n+1) = α j by {
      let h := j.2
      simp only [mem_setOf_eq] at h
      congr
      omega
    })
    y.2 : α j) := by {
      simp [ProdLikeM.equiv]
  }

def MeasurableEquiv.insert_m {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n : ℕ) (m : ℕ)
  : ⇑α {k| k <= n+m} ≃ᵐ ⇑α {k | k <= n} × ⇑α {k | n < k ∧ k <= n+m} :=
    have h : {k | k <= n + m} = {k | k <= n} ∪ {k | n < k ∧ k <= n+m} := by {
      ext; simp; omega
    }
    have h_disjoint : Disjoint {k | k ≤ n} {k | n < k ∧ k <= n+m} := by {
      rw [@disjoint_iff_inter_eq_empty]
      ext; simp; omega
    }
    MeasurableEquiv.pi_equiv h h_disjoint

@[simp]
lemma MeasurableEquiv.insert_m_apply
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n : ℕ) (m : ℕ)
  (x : ⇑α {k| k <= n+m})
  : simp% (MeasurableEquiv.insert_m n m x)
  = ({k | k <= n}.restrict₂ (by simp; intro a h; omega) x, {k | n < k ∧ k <= n+m}.restrict₂ (by simp) x) := by {
    rfl
  }

@[simp]
lemma MeasurableEquiv.insert_m_apply_inv
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n : ℕ) (m : ℕ)
  (y : ⇑α {k | k ≤ n} × ⇑α {k | n < k ∧ k ≤ n+m})
  : simp% ((MeasurableEquiv.insert_m n m).symm y)
  = fun j : {k | k ≤ n+m} => if hj : (j : ℕ) ≤ n then y.1 ⟨j,hj⟩ else
    y.2 ⟨j, by aesop⟩ := by {
      unfold insert_m
      simp
      generalize_proofs h h2 h3 h4
      conv => lhs; tactic => apply pi_equiv_apply_inv
      ext j
      by_cases h : (j : ℕ) ≤ n <;> simp [h]
  }

instance ProdLikeM.insert_m {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n m : ℕ)
  : ProdLikeM (⇑α {k| k <= n+m}) (⇑α {k | k <= n}) (⇑α {k | n < k ∧ k <= n+m}) :=
  ⟨ MeasurableEquiv.insert_m n m ⟩

instance ProdLikeM.insert_m_plus_1 {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n m: ℕ)
  : ProdLikeM (⇑α {k| k <= n+m+1}) (⇑α {k | k <= n}) (⇑α {k | n < k ∧ k <= n+m+1}) :=
  ⟨ MeasurableEquiv.insert_m n (m+1)⟩

@[simp]
lemma ProdLikeM.insert_m_apply
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n : ℕ) (m : ℕ)
  (x : ⇑α {k| k <= n+m})
  : simp% ((ProdLikeM.insert_m n m).equiv x)
  = ({k | k <= n}.restrict₂ (by simp; intro a h; omega) x, {k | n < k ∧ k <= n+m}.restrict₂ (by simp) x) := by {
    rfl
  }

@[simp]
lemma ProdLikeM.insert_m_apply_inv
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n : ℕ) (m : ℕ)
  (y : ⇑α {k | k ≤ n} × ⇑α {k | n < k ∧ k ≤ n+m})
  : simp%((ProdLikeM.insert_m n m).equiv.symm y)
  = fun j : {k | k ≤ n+m} => if hj : (j : ℕ) ≤ n then y.1 ⟨j,hj⟩ else
    y.2 ⟨j, by aesop⟩ := by {
      simp [ProdLikeM.equiv]
  }

def MeasurableEquiv.ge_n_insert_m_plus_1 {α : ℕ -> Type*}
  [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  : ⇑α {k| n < k ∧ k <= n + m + 1} ≃ᵐ ⇑α {k | n < k ∧ k <= n + m} × (α (n + m + 1)) :=
    have h : {k | n < k ∧ k <= n + m + 1} = insert (n+m+1) {k | n < k ∧ k <= n+m} := by {
      ext; simp; omega
    }
    have hn : n+m+1 ∉ {k | n < k ∧ k ≤ n+m} := by simp
    MeasurableEquiv.pi_insert_equiv h hn

@[simp]
lemma MeasurableEquiv.ge_n_insert_m_plus_1_apply
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  (x : ⇑α {k| n < k ∧ k <= n + m + 1})
  : simp% (MeasurableEquiv.ge_n_insert_m_plus_1 n m x)
  = ({k | n < k ∧ k <= n + m}.restrict₂ (by simp; intro a h; omega) x, x ⟨n+m+1, by simp; omega⟩) := by {
    rfl
  }

@[simp]
lemma MeasurableEquiv.ge_n_insert_m_plus_1_apply_inv
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  (y : ⇑α {k | n < k ∧ k <= n + m} × α (n + m + 1))
  : simp% ((MeasurableEquiv.ge_n_insert_m_plus_1 n m).symm y)
  = fun j : {k | n < k ∧ k <= n + m + 1} => if hj : n < (j : ℕ) ∧ (j : ℕ) ≤ n + m then y.1 ⟨j, hj⟩ else
    cast
    (show α (n + m + 1) = α j by {
      let h := j.2
      simp only [mem_setOf_eq] at h
      congr
      omega
    }) y.2 := by {
      simp [ge_n_insert_m_plus_1]
      conv => lhs; apply pi_insert_equiv_apply_inv
      simp only [coe_setOf, mem_setOf_eq]
    }

instance ProdLikeM.ge_n_insert_m_plus_1 {α : ℕ -> Type*}
  [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  : ProdLikeM (⇑α {k| n < k ∧ k <= n + m + 1}) (⇑α {k | n < k ∧ k <= n + m}) (α (n + m + 1)) :=
  ⟨ MeasurableEquiv.ge_n_insert_m_plus_1 n m ⟩

instance ProdLikeM.ge_n_insert_m_plus_1_plus_1 {α : ℕ -> Type*}
  [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  : ProdLikeM (⇑α {k| n < k ∧ k <= n + (m + 1) + 1}) (⇑α {k | n < k ∧ k <= n + m + 1})
  (α (n + m + 1 + 1)) :=
  ⟨ MeasurableEquiv.ge_n_insert_m_plus_1 n (m+1) ⟩

@[simp]
lemma ProdLikeM.ge_n_insert_m_plus_1_apply
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  (x : ⇑α {k| n < k ∧ k <= n + m + 1})
  : simp% ((ProdLikeM.ge_n_insert_m_plus_1 n m).equiv x)
  = ({k | n < k ∧ k <= n + m}.restrict₂ (by simp; intro a h; omega) x, x ⟨n+m+1, by simp; omega⟩) := by {
    rfl
  }




@[simp]
lemma ProdLikeM.ge_n_insert_m_plus_1_apply_inv
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  (y :  (⇑α {k | n < k ∧ k <= n + m} × α (n + m + 1)))
  : simp% ((ProdLikeM.ge_n_insert_m_plus_1 (α := α) n m).equiv.symm y)
  = fun j : {k | n < k ∧ k <= n + m + 1} => if hj : n < (j : ℕ) ∧ (j : ℕ) ≤ n + m then y.1 ⟨j, hj⟩ else
    cast
    (show α (n + m + 1) = α j by {
      let h := j.2
      simp only [mem_setOf_eq] at h
      congr
      omega
    }) y.2 := by {
      simp only [coe_setOf, mem_setOf_eq, ProdLikeM.equiv,
        MeasurableEquiv.ge_n_insert_m_plus_1_apply_inv]
  }
#check ProdLikeM.ge_n_insert_m_plus_1_apply_inv


variable (α : ℕ -> Type*) (n m : ℕ) (J : Set ℕ )
  [mα : ∀n, MeasurableSpace (α n)]

def test1 : ProdLikeM (⇑α {k | k ≤ m + 1}) (⇑α {k | k ≤ m}) (α (m + 1))
  := by infer_instance

def test2 : ProdLikeM (⇑α {k | k ≤ n + m + 1}) (⇑α {k | k ≤ n})
  (⇑α {k | n < k ∧ k ≤ n + m + 1})
  := by infer_instance

def test3 : ProdLikeM (⇑α {k | n < k ∧ k ≤ n + (m + 1) + 1})
    (⇑α {k | n < k ∧ k ≤ n + m + 1}) (α (n + m + 1 + 1))
    := by infer_instance

-- #lint
