/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea.prodLike
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal

/- recommended whenever you define anything new. -/
noncomputable section


/- Now write definitions and theorems. -/

namespace IndexedFamilies
open MeasureTheory MeasurableSpace Measurable ProductLike

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory
class EquivalentMeasurableSpace (α : Type*) (β : Type*)
  [MeasurableSpace α] [MeasurableSpace β] where
  equiv : α ≃ᵐ β

instance [MeasurableSpace α]: EquivalentMeasurableSpace α α := ⟨MeasurableEquiv.refl α⟩

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

def MeasurableEquiv.piUnique' {I : Type*} [IU : Unique I]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I)
  : (∀ i, α i) ≃ᵐ α i :=
    (MeasurableEquiv.piUnique α).trans
    (unique α i)

def MeasurableEquiv.piUnique'' {I : Type*} {J : Set I} [Unique J]
  (α : I → Type*) [∀i, MeasurableSpace (α i)]
  (i : I)
  (hi : i ∈ J)
  : (∀ i : J, α i) ≃ᵐ α i :=
    MeasurableEquiv.piUnique' (fun i : J => α i) ⟨i,hi⟩

instance {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)]
  : EquivalentMeasurableSpace (∀k : {k | k <= 0}, α k) (α 0) where
  equiv :=
      let U : Unique {k | k <= 0} := by {
          simp; infer_instance
      }
      let τ := MeasurableEquiv.piUnique'
        (I := ({k | k <= 0})) (α := fun x => α ↑x) ⟨0, by simp⟩
      τ

instance {α : ℕ -> Type*} [∀m, MeasurableSpace (α m)] (n : ℕ)
  : EquivalentMeasurableSpace (∀k : {k | n < k ∧ k <= n+1}, α k) (α (n+1)) where
  equiv :=
      let U : Unique {k | n < k ∧ k <= n+1} := by {
          rw [show {k | n < k ∧ k <= n+1} = {n+1} by ext;simp;omega]
          infer_instance
      }
      let τ := MeasurableEquiv.piUnique'
        (I := ({k | n < k ∧ k <= n+1})) (α := fun x => α ↑x) ⟨n+1, by simp⟩
      τ

instance project_coerce {I : Type*} : CoeFun (I -> Type _) (fun _ => Set I -> Type _) where
  coe α J := ∀k : J, α k

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

def MeasurableEquiv.insert_n_plus_1
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  : (⇑α {k| k <= n + 1}) ≃ᵐ (⇑α {k | k <= n}) × (α (n+1)) :=
    have h : {k | k <= n + 1} = insert (n+1) {k | k <= n} := by {
      ext; simp; omega
    }
    have hn : n+1 ∉ {k | k ≤ n} := by simp
    MeasurableEquiv.pi_insert_equiv h hn

instance ProdLikeM.insert_n_plus_1
  {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)] (n : ℕ)
  : ProdLikeM (⇑α {k| k <= n + 1}) (⇑α {k | k <= n}) (α (n+1))
  := ⟨ MeasurableEquiv.insert_n_plus_1 n ⟩

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

instance ProdLikeM.insert_m {α : ℕ -> Type*} [mα : ∀n, MeasurableSpace (α n)]
  (n : ℕ) (m : ℕ)
  : ProdLikeM (⇑α {k| k <= n+m}) (⇑α {k | k <= n}) (⇑α {k | n < k ∧ k <= n+m}) :=
  ⟨ MeasurableEquiv.insert_m n m ⟩

def MeasurableEquiv.ge_n_insert_m_plus_1 {α : ℕ -> Type*}
  [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  : ⇑α {k| n < k ∧ k <= n + m + 1} ≃ᵐ ⇑α {k | n < k ∧ k <= n + m} × (α (n + m + 1)) :=
    have h : {k | n < k ∧ k <= n + m + 1} = insert (n+m+1) {k | n < k ∧ k <= n+m} := by {
      ext; simp; omega
    }
    have hn : n+m+1 ∉ {k | n < k ∧ k ≤ n+m} := by simp
    MeasurableEquiv.pi_insert_equiv h hn

instance ProdLikeM.ge_n_insert_m_plus_1 {α : ℕ -> Type*}
  [mα : ∀n, MeasurableSpace (α n)] (n m : ℕ)
  : ProdLikeM (⇑α {k| n < k ∧ k <= n + m + 1}) (⇑α {k | n < k ∧ k <= n + m}) (α (n + m + 1)) :=
  ⟨ MeasurableEquiv.ge_n_insert_m_plus_1 n m ⟩

-- instance ( α : ℕ -> Type*) : Coe (α 0) (∀k : {k | k <= 0}, α k) where
--   coe x n:= by {
--     rw [Nat.eq_zero_of_le_zero n.2]
--     exact x
--   }
