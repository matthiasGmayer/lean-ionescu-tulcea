import Mathlib

set_option autoImplicit true
open Function Set Classical
open ENNReal

noncomputable section

/-!
This file defines productlike measurable spaces
-/



namespace ProductLike
open MeasureTheory MeasurableSpace Measurable ProbabilityTheory MeasurableEquiv

section ProductLike

variable
  [MeasurableSpace F]
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace F']
  [MeasurableSpace γ]
  [MeasurableSpace δ]

class ProdLikeM
(γ : outParam Type*)
(α : Type*)
(β : Type*)
[MeasurableSpace γ] [MeasurableSpace α] [MeasurableSpace β] where
  equiv : γ ≃ᵐ α × β

instance : CoeSort (ProdLikeM F α β) (Type u) := ⟨fun _ => F⟩
instance (priority := low) : ProdLikeM (α × β) α β := ⟨MeasurableEquiv.refl (α × β)⟩

def ProdLikeM.symm (p : ProdLikeM F α β) : ProdLikeM F β α := ⟨MeasurableEquiv.trans p.equiv prodComm⟩

def ProdLikeM.fst_type (P : ProdLikeM F α β) := α
def ProdLikeM.snd_type (P : ProdLikeM F α β) := β

def ProdLikeM.fst [P : ProdLikeM F α β] (x : F) : α := (P.equiv x).fst
def ProdLikeM.snd [P : ProdLikeM F α β] (x : F) : β := (P.equiv x).snd

@[measurability]
def ProdLikeM.measurable_fst [p : ProdLikeM F α β]
  : Measurable (p.fst) := by {
    apply Measurable.comp ?_ (MeasurableEquiv.measurable equiv)
    exact _root_.measurable_fst
  }
@[measurability]
def ProdLikeM.measurable_snd [p : ProdLikeM F α β]
  : Measurable (p.snd) := by {
    apply Measurable.comp ?_ (MeasurableEquiv.measurable equiv)
    exact _root_.measurable_snd
  }


def change_left [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (K : Kernel α β) (τ : α ≃ᵐ γ) : Kernel γ β := K.comap τ.invFun τ.measurable_invFun

def change_right [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (K : Kernel α β) (τ : β ≃ᵐ γ) : Kernel α γ := K.map τ


def Kernel.compProd'
  (K : Kernel α β)
  (L : Kernel F γ)
  [p : ProdLikeM F α β]
  [q : ProdLikeM F' β γ]
  : Kernel α F' :=
  change_right (K ⊗ₖ (change_left L p.equiv)) q.equiv.symm


def ProdLikeM.slice
  [p : ProdLikeM γ α β]
  (B : Set γ)
  (a : α)
  : Set β :=  {b : β | p.equiv.symm (a,b) ∈ B}

@[measurability]
lemma ProdLikeM.slice_measurable
  (p : ProdLikeM γ α β)
  (B : Set γ)
  (hB : MeasurableSet B)
  (a : α)
  : MeasurableSet (ProdLikeM.slice (p:=p) B a) := by {
    unfold ProdLikeM.slice
    simp
    apply Measurable.comp'
    · simp_all only [measurable_mem]
    · apply Measurable.comp'
      · apply MeasurableEquiv.measurable
      · apply Measurable.prod
        · simp_all only [measurable_const]
        · simp_all only
          apply measurable_id'
  }

-- infixl:100 " ⊗ₖ'[" p "]" => Kernel.compProd' p


def compProd' (μ : Measure α) (K : Kernel α β) [p: ProdLikeM γ α β]
  : Measure γ := (μ ⊗ₘ K).map p.equiv.symm

infixl:100 " ⊗ₖ' " => Kernel.compProd'
infixl:100 " ⊗ₘ' " => compProd'

lemma compProd'_def (μ : Measure α) (K : Kernel α β) (p: ProdLikeM γ α β)
  :  μ ⊗ₘ' K = (μ.compProd K).map p.equiv.symm := rfl
lemma Kernel.compProd'_def (K : Kernel α β) (L : Kernel γ δ) [p: ProdLikeM γ α β] [q: ProdLikeM F β δ]
  : K ⊗ₖ' L  = change_right (K ⊗ₖ (change_left L p.equiv)) q.equiv.symm := rfl

lemma compProd'_apply (μ : Measure α) (K : Kernel α β) [p: ProdLikeM γ α β]
  (s : Set (α × β)) (hs : MeasurableSet s)
  : compProd' μ K (p := p) (p.equiv ⁻¹' s) = (μ ⊗ₘ K) s := by {
    rw [compProd'_def]
    rw [Measure.map_apply]
    simp
    exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
    apply MeasurableSet.preimage hs (MeasurableEquiv.measurable p.equiv)
  }
