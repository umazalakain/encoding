open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Base as List using (List; []; _∷_)

open import Encoding.ST
module Encoding.LeftoverST where


private
  variable
    Γ Δ Ξ Ω Θ : T⟦ ctx ⟧
    x y : T⟦ type ⟧


-- TODO: ergonomics
-- Covered can be made decidable if we restrict the types in pure to be those with decidable equality
-- The first field of Branch can be made decidable too

data Covered : ∀ {u} → T⟦ u ⟧ → T⟦ u ⟧ → Set₁ where
  unused : ∀ {t} → Covered {session} t t
  used : ∀ {t} → Covered {session} t end
  pure : {A : Set} {a : A} → Covered {type} (pure A , a) (pure A , a)
  chan : ∀ {s₁ s₂ t₁ t₂}
       → Covered s₁ s₂
       → Covered t₁ t₂
       → Covered (chan (s₁ , t₁) , tt) (chan (s₂ , t₂) , tt)
  []   : Covered {ctx} [] []
  _∷_  : ∀ {t₁ t₂ ts₁ ts₂}
       → Covered {type} t₁ t₂
       → Covered {ctx} ts₁ ts₂
       → Covered {ctx} (t₁ ∷ ts₁) (t₂ ∷ ts₂)


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
  record Branch (t : Type) (v : ⟦ t ⟧) (n : ℕ) (p : Polarity) (Δ Ω : T⟦ ctx ⟧) : Set₁ where
    inductive
    constructor case_∶_
    field
      {Ψ} : T⟦ ctx ⟧
      resume-var : Δ ∋ var n (channel p (resume t v)) ▹ Ψ
      cont : (t , v) ∷ Ψ ⊢▹ (0∙ t , 0∙⟦ t ⟧ v) ∷ Ω


  infix 3 _⊢▹_
  data _⊢▹_ : T⟦ ctx ⟧ → T⟦ ctx ⟧ → Set₁ where

    pure : (t : Set) (v : t)
        → let x = pure t , v
          in x ∷ Γ ⊢▹ x ∷ Δ
        →        Γ ⊢▹     Δ

    end : Γ ⊢▹ Γ

    new : (s : SessionType)
        → let x = (chan (s , dual s) , tt)
              y = (chan (end , end) , tt)
          in
          x ∷ Γ ⊢▹ y ∷ Δ
        →     Γ ⊢▹     Δ

    par : {Γ Δ Ξ : T⟦ ctx ⟧}
        → Γ ⊢▹ Δ
        → Covered {ctx} Γ Δ
        → Δ ⊢▹ Ξ
        → Covered {ctx} Δ Ξ
        → Γ ⊢▹ Ξ

    send : ∀ {t p n m}
        → Γ ∋ var n (channel p (send t)) ▹ Δ
        → (v : ⟦ t ⟧)
        → Δ ∋ var m (erase t v) ▹ Ξ
        → Ξ ∋ var n (channel p (resume t v)) ▹ Ω
        → Ω ⊢▹ Θ
        → Γ ⊢▹ Θ

    recv : ∀ {t p n} {Δ : T⟦ ctx ⟧}
        → Γ ∋ var n (channel p (receive t)) ▹ Δ
        → ((v : ⟦ t ⟧) → Branch t v n p Δ Ω)
        → Γ ⊢▹ Ω


-- open import Data.Nat as ℕ using (ℕ; zero; suc)
-- 
-- replicate : Action → Type s → ℕ → SessionType
-- replicate a t zero = end
-- replicate a t (suc n) = session a t (λ _ → replicate a t n)
-- 
-- 
-- receiving : ∀ v → Branch (pure ℕ) v zero ⁺ ((chan (pair (pure ℕ) (replicate ! (pure ⊤)) , end) , tt) ∷ []) ((chan (end , end) , tt) ∷ []) ((used , unused) ∷ [])
-- receiving zero = case zero (chan⁺ resume) ∶ end [ {!!} ]
-- receiving (suc v) = case zero (chan⁺ resume) ∶ recv {!!} {!!} [ {!!} ]
-- 
-- example₁ : [] ⊢▹ [] [ [] ]
-- example₁ = new
--   (session ¿ (pure ℕ) (replicate ! (pure ⊤)))
--   (par
--     (pure ℕ 2 (send (suc (zero (chan⁻ send))) 2 (zero erase) (suc (zero (chan⁻ resume))) (recv (suc (zero (chan⁻ receive))) (λ {tt → case suc (zero (chan⁻ resume)) ∶ (recv (suc (suc (zero (chan⁻ receive)))) λ {tt → case suc (suc (zero (chan⁻ resume))) ∶ end [ {!!} ]}) [ {!!} ]}))))
--     ((chan unused used) ∷ [])
--     (recv (zero (chan⁺ receive)) λ v → {!!})
--     {!!}
--   )
--   {!!}

open import Data.Bool using (Bool; true; false)

foo : Bool → SessionType
foo true = end
foo false = session ! (pure ℕ) (λ _ → end)

example₂ : [] ⊢▹ []
example₂ = new (session ¿ (pure Bool) foo)
  (par
    (pure Bool true (send (suc (zero (chan⁻ send))) true (zero erase) (suc (zero (chan⁻ resume))) end))
    (chan unused used ∷ [])
    (recv (zero (chan⁺ receive)) λ where
      true → case zero (chan⁺ resume) ∶ end
      false → case zero (chan⁺ resume) ∶ pure ℕ 2 (send (suc (suc (zero (chan⁺ send)))) 2 (zero erase) (suc (suc (zero (chan⁺ resume)))) end))
    (chan used unused ∷ [])
  )
