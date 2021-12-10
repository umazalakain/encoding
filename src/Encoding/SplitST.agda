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
    s : Shape
    ctxshape : S⟦ ctx ⟧
    typeshape : S⟦ type ⟧
    sessionshape : S⟦ session ⟧
    Γ Δ Ξ Ω Θ : T⟦ ctxshape ⟧
    x y : T⟦ typeshape ⟧

data _≔_+_ : ∀ {u} {s : S⟦ u ⟧} → T⟦ s ⟧ → T⟦ s ⟧ → T⟦ s ⟧ → Set₁ where
  left : {s : S⟦ session ⟧} {t : T⟦ s ⟧} → _≔_+_ {session} t t end
  right : {s : S⟦ session ⟧} {t : T⟦ s ⟧} → _≔_+_ {session} t end t
  pure : {t : T⟦_⟧ {type} pure} → t ≔ t + t
  chan : ∀ {xₗ xᵣ yₗ yᵣ zₗ zᵣ}
       → _≔_+_ {session} xₗ yₗ zₗ
       → _≔_+_ {session} xᵣ yᵣ zᵣ
       → _≔_+_ {type} (chan (xₗ , xᵣ) , tt) (chan (yₗ , yᵣ) , tt) (chan (zₗ , zᵣ) , tt)
  [] : _≔_+_ {ctx} [] [] []
  _∷_ : ∀ {s : S⟦ type ⟧} {x y z : T⟦ s ⟧} {ss : S⟦ ctx ⟧} {xs ys zs : T⟦ ss ⟧}
      → _≔_+_ {type} x y z
      → _≔_+_ {ctx} xs ys zs
      → _≔_+_ {ctx} (x ∷ xs) (y ∷ ys) (z ∷ zs)


infix 3 _∋_▹_
data _∋_▹_ : ∀ {u} {s : S⟦ u ⟧} → T⟦ s ⟧ → Event u → T⟦ s ⟧ → Set₁ where
  receive : ∀ {s t f}
          → (session ¿ t f) ∋ (receive s t) ▹ (pair t f)
  send    : ∀ {s t f}
          → (session ! t f) ∋ (send s t) ▹ (pair t f)
  resume  : ∀ {s} {t : Type s} {f v}
          → (pair t f) ∋ (resume t v) ▹ (f v)
  erase   : ∀ {s} {t : Type s} {v}
          → (t , v) ∋ (erase t v) ▹ (0∙ t , 0∙⟦ t ⟧ v)
  chan⁺   : ∀ {x y z e}
          → x ∋ e ▹ y
          → (chan (x , z) , tt) ∋ (channel ⁺ e) ▹ (chan (y , z) , tt)
  chan⁻   : ∀ {x y z e}
          → x ∋ e ▹ y
          → (chan (z , x) , tt) ∋ (channel ⁻ e) ▹ (chan (z , y) , tt)
  zero    : ∀ {e} {x y : T⟦ typeshape ⟧}
          → x ∋ e ▹ y
          → x ∷ Γ ∋ var zero e ▹ y ∷ Γ
  suc     : ∀ {Γ Δ : T⟦ ctxshape ⟧} {t : T⟦ typeshape ⟧} {e n}
          → Γ ∋ var n e ▹ Δ
          → t ∷ Γ ∋ var (suc n) e ▹ t ∷ Δ


mutual
  data Branch (t : Type s) (v : ⟦ t ⟧) (n : ℕ) (p : Polarity) : ∀ {s : S⟦ ctx ⟧} → T⟦ s ⟧ → Set₁ where
    case_∶_ : Γ ∋ var n (channel p (resume t v)) ▹ Δ
            → Proc ((t , v) ∷ Δ)
            → Branch t v n p Δ


  infix 3 Proc
  data Proc : {s : S⟦ ctx ⟧} → T⟦ s ⟧ → Set₁ where

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

    par : {Γ Δ Ξ : T⟦ ctxshape ⟧}
        → _≔_+_ {ctx} Γ Δ Ξ
        → Proc Δ
        → Proc Ξ
        → Proc Γ

    send : ∀ {s t p n m}
        → Γ ∋ var n (channel p (send s t)) ▹ Δ
        → (v : ⟦ t ⟧)
        → Δ ∋ var m (erase t v) ▹ Ξ
        → Ξ ∋ var n (channel p (resume t v)) ▹ Ω
        → Proc Ω
        → Proc Γ

    recv : ∀ {s t p n} {Δ : T⟦ ctxshape ⟧}
        → Γ ∋ var n (channel p (receive s t)) ▹ Δ
        → ((v : ⟦ t ⟧) → Branch t v n p Δ)
        → Proc Γ

