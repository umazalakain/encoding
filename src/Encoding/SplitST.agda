open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import Encoding.ST
module Encoding.SplitST where


private
  variable
    u : Univ
    Γ Δ Ξ Ω Θ : T⟦ ctx ⟧
    x y : T⟦ type ⟧

data _≔_+_ : ∀ {u} → T⟦ u ⟧ → T⟦ u ⟧ → T⟦ u ⟧ → Set₁ where
  left : {t : T⟦ session ⟧} → _≔_+_ {session} t t end
  right : {t : T⟦ session ⟧} → _≔_+_ {session} t end t
  pure : {A : Set} {a : A} → _≔_+_ (pure A , a) (pure A , a) (pure A , a)
  chan : ∀ {xₗ xᵣ yₗ yᵣ zₗ zᵣ}
       → _≔_+_ {session} xₗ yₗ zₗ
       → _≔_+_ {session} xᵣ yᵣ zᵣ
       → _≔_+_ {type} (chan (xₗ , xᵣ) , tt) (chan (yₗ , yᵣ) , tt) (chan (zₗ , zᵣ) , tt)
  [] : _≔_+_ {ctx} [] [] []
  _∷_ : ∀ {x y z : T⟦ type ⟧} {xs ys zs : T⟦ ctx ⟧}
      → _≔_+_ {type} x y z
      → _≔_+_ {ctx} xs ys zs
      → _≔_+_ {ctx} (x ∷ xs) (y ∷ ys) (z ∷ zs)


infix 3 _∋_▹_
data _∋_▹_ : ∀ {u} → T⟦ u ⟧ → Event u → T⟦ u ⟧ → Set₁ where
  receive : ∀ {t f}
          → (session ¿ t f) ∋ (receive t) ▹ (pair t f)
  send    : ∀ {t f}
          → (session ! t f) ∋ (send t) ▹ (pair t f)
  resume  : ∀ {t : Type} {f v}
          → (pair t f) ∋ (resume t v) ▹ (f v)
  erase   : ∀ {t : Type} {v}
          → (t , v) ∋ (erase t v) ▹ (0∙ t , 0∙⟦ t ⟧ v)
  chan⁺   : ∀ {x y z e}
          → x ∋ e ▹ y
          → (chan (x , z) , tt) ∋ (channel ⁺ e) ▹ (chan (y , z) , tt)
  chan⁻   : ∀ {x y z e}
          → x ∋ e ▹ y
          → (chan (z , x) , tt) ∋ (channel ⁻ e) ▹ (chan (z , y) , tt)
  zero    : ∀ {e} {x y : T⟦ type ⟧}
          → x ∋ e ▹ y
          → x ∷ Γ ∋ var zero e ▹ y ∷ Γ
  suc     : ∀ {Γ Δ : T⟦ ctx ⟧} {t : T⟦ type ⟧} {e n}
          → Γ ∋ var n e ▹ Δ
          → t ∷ Γ ∋ var (suc n) e ▹ t ∷ Δ


mutual
  record Branch (t : Type) (v : ⟦ t ⟧) (n : ℕ) (p : Polarity) (Δ : T⟦ ctx ⟧) : Set₁ where
    inductive
    constructor case_∶_
    field
      {Ψ} : T⟦ ctx ⟧
      resume-var : Δ ∋ var n (channel p (resume t v)) ▹ Ψ
      cont : Proc ((t , v) ∷ Ψ)


  infix 3 Proc
  data Proc : T⟦ ctx ⟧ → Set₁ where

    pure : (t : Set) (v : t)
         → let x = (pure t , v)
            in Proc (x ∷ Γ)
         → Proc Γ

    end : _≔_+_ {ctx} Γ Γ Γ
        → Proc Γ

    new : (s : SessionType)
        → let ch = chan (s , dual s) in
          Proc ((ch , tt) ∷ Γ)
        → Proc Γ

    par : {Γ Δ Ξ : T⟦ ctx ⟧}
        → _≔_+_ {ctx} Γ Δ Ξ
        → Proc Δ
        → Proc Ξ
        → Proc Γ

    send : ∀ {t p n m}
        → Γ ∋ var n (channel p (send t)) ▹ Δ
        → (v : ⟦ t ⟧)
        → Δ ∋ var m (erase t v) ▹ Ξ
        → Ξ ∋ var n (channel p (resume t v)) ▹ Ω
        → Proc Ω
        → Proc Γ

    recv : ∀ {t p n} {Δ : T⟦ ctx ⟧}
        → Γ ∋ var n (channel p (receive t)) ▹ Δ
        → ((v : ⟦ t ⟧) → Branch t v n p Δ)
        → Proc Γ

