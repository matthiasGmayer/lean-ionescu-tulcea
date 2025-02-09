import Mathlib
import IonescuTulcea.finiteCompProd
set_option autoImplicit true
open Function Set Classical ENNReal CompProdMeasures

noncomputable section

/-!
This file defines a strong recursion principle to construct a sequence of elements,
such that propositions about the projections on all {k <= n} are true.
-/

namespace StrongRec

def strong_rec_on_nat_aux
  {α : ℕ -> Type*} {h : ∀n (_ : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  (n : ℕ)
  : {ω : (∀k : {k | k <= n}, α k) | h n ω} :=
  match n with
  | 0 => ⟨ω₀, h₀⟩
  | n + 1 =>
    let ω := strong_rec_on_nat_aux h₀ ind n
    let ind' := ind n ω
    let ω' := choose ind'
    ⟨compapp ω.1 ω', choose_spec ind'⟩

def strong_rec_on_nat_proj
  {α : ℕ -> Type*} {h : ∀n (_ : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  (n : ℕ)
  : α n := (strong_rec_on_nat_aux h₀ ind n).1 ⟨n, by simp⟩

lemma strong_rec_on_nat_aux_restrict
  {α : ℕ -> Type*} {h : ∀n (_ : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  (n : ℕ)
  (n' : ℕ)
  (hnn' : n' <= n)
  : {k|k<=n'}.restrict₂ (le_to_subset hnn') (strong_rec_on_nat_aux h₀ ind n).1 = (strong_rec_on_nat_aux h₀ ind n').1 := by {
    induction n with
    | zero => {
      have h0 := Nat.eq_zero_of_le_zero hnn'
      subst h0
      rfl
    }
    | succ n hn => {
      by_cases hneqn' : n + 1 = n'
      subst hneqn'
      rfl
      have hn' : n' <= n := by omega
      specialize hn hn'
      rw [<- hn]
      ext k
      simp
      conv => lhs; unfold strong_rec_on_nat_aux
      simp
      apply compapp_apply
    }
  }
lemma strong_rec_on_nat_proj_restrict
  {α : ℕ -> Type*} {h : ∀n (_ : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  (n : ℕ)
  : {k|k<=n}.restrict (strong_rec_on_nat_proj h₀ ind) = strong_rec_on_nat_aux h₀ ind n := by {
    unfold strong_rec_on_nat_proj
    ext m
    simp
    rw [<- strong_rec_on_nat_aux_restrict]
    simp
    rfl
    exact m.2
  }
lemma strong_rec_on_nat_proj_prop
  {α : ℕ -> Type*} {h : ∀n (_ : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  : ∀n, h n <| {k | k <= n}.restrict (strong_rec_on_nat_proj h₀ ind) := by {
    intro n
    rw [strong_rec_on_nat_proj_restrict]
    exact (strong_rec_on_nat_aux h₀ ind n).2
  }
def strong_rec_on_nat
  {α : ℕ -> Type*}
  {h : ∀n (ω : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  : {ω | ∀n, h n ({k|k<=n}.restrict ω)} := ⟨strong_rec_on_nat_proj h₀ ind, strong_rec_on_nat_proj_prop h₀ ind⟩

def strong_rec_on_nat_existence
  {α : ℕ -> Type*} {h : ∀n (_ : ∀k : {k | k <= n}, α k), Prop}
  {ω₀ : ∀k : {k | k <= 0}, α k} (h₀ : h 0 ω₀)
  [∀n, Inhabited (α n)]
  (ind : ∀n (ω : {ω | h n ω}), ∃ω' : α (n+1), h (n+1) (compapp ω.1 ω'))
  : ∃ω, ∀n, h n ({k|k<=n}.restrict ω) := by {
    let ω := strong_rec_on_nat h₀ ind
    use ω.1
    exact ω.2
  }
