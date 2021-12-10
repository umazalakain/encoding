open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Base as List using (List; []; _∷_)

open import Encoding.ST
module Encoding.LeftoverST where

data Cover : Set₁ where
  used : Cover
  unused : Cover

TypeCover : Shape → Set₁
TypeCover pure = ⊤
TypeCover chan = Cover × Cover

C⟦_⟧ : ∀ {u} → S⟦ u ⟧ → Set₁
C⟦_⟧ {session} _ = Cover
C⟦_⟧ {type} = TypeCover
C⟦_⟧ {ctx} = All TypeCover


private
  variable
    s : Shape
    ctxshape : S⟦ ctx ⟧
    typeshape : S⟦ type ⟧
    sessionshape : S⟦ session ⟧
    Γ Δ Ξ Ω Θ : T⟦ ctxshape ⟧
    γ δ ξ ω θ β : C⟦ ctxshape ⟧
    x y : T⟦ typeshape ⟧
    c : C⟦ typeshape ⟧

constC : ∀ {u} → Cover → (s : S⟦ u ⟧) → C⟦ s ⟧
constC {u = session} c _ = c
constC {u = type} c pure = tt
constC {u = type} c chan = c , c
constC {u = ctx} c [] = []
constC {u = ctx} c (s ∷ ss) = constC c s ∷ constC c ss

_or_ : Cover → Cover → Cover
used or _ = used
unused or x = x

infixr 20 _⊎_
_⊎′_ : ∀ {u} {s : S⟦ u ⟧} → C⟦ s ⟧ → C⟦ s ⟧ → C⟦ s ⟧
_⊎′_ {session} x y = x or y
_⊎′_ {type} {pure} xs ys = tt
_⊎′_ {type} {chan} (fst , snd) (fst₁ , snd₁) = (fst or fst₁) , (snd or snd₁)
_⊎′_ {ctx} [] ys = []
_⊎′_ {ctx} (x ∷ xs) (y ∷ ys) = x ⊎′ y ∷ (_⊎′_ {ctx} xs ys)

_⊎_ : {s : S⟦ ctx ⟧} → C⟦ s ⟧ → C⟦ s ⟧ → C⟦ s ⟧
_⊎_ = _⊎′_ {u = ctx}


data Covered : ∀ {u} {s : S⟦ u ⟧} → C⟦ s ⟧ → T⟦ s ⟧ → Set₁ where
  pure : {A : Set} {a : A} → Covered {type} tt (pure A , a)
  used : Covered {session} used end
  unused : {s : S⟦ session ⟧} {x : T⟦ s ⟧} → Covered {session} unused x
  chan : ∀ {c₁ c₂ s₁ s₂}
       → Covered {session} c₁ s₁
       → Covered {session} c₂ s₂
       → Covered {type} (c₁ , c₂) (chan (s₁ , s₂) , tt)
  []   : Covered {ctx} [] []
  _∷_  : {s : S⟦ type ⟧} {c : C⟦ s ⟧} {t : T⟦ s ⟧}
       → {ss : S⟦ ctx ⟧} {cs : C⟦ ss ⟧} {ts : T⟦ ss ⟧}
       → Covered {type} c t
       → Covered {ctx} cs ts
       → Covered {ctx} (c ∷ cs) (t ∷ ts)


infix 3 _∋_▹_[_]
data _∋_▹_[_] : ∀ {u} {s : S⟦ u ⟧} → T⟦ s ⟧ → Event u → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where
  receive : ∀ {t f}
          → (session ¿ t f) ∋ (receive s t) ▹ (pair t f) [ used ]
  send    : ∀ {t f}
          → (session ! t f) ∋ (send s t) ▹ (pair t f) [ used ]
  resume  : ∀ {s} {t : Type s} {f v}
          → (pair t f) ∋ (resume t v) ▹ (f v) [ used ]
  erase   : ∀ {s} {t : Type s} {v}
          → (t , v) ∋ (erase t v) ▹ (0∙ t , 0∙⟦ t ⟧ v) [ (constC used s) ]
  chan⁺   : ∀ {x y z e c}
          → x ∋ e ▹ y [ c ]
          → (chan (x , z) , tt) ∋ (channel ⁺ e) ▹ (chan (y , z) , tt) [ c , unused ]
  chan⁻   : ∀ {x y z e c}
          → x ∋ e ▹ y [ c ]
          → (chan (z , x) , tt) ∋ (channel ⁻ e) ▹ (chan (z , y) , tt) [ unused , c ]
  zero    : ∀ {e} {x y : T⟦ typeshape ⟧} {c : C⟦ typeshape ⟧}
          → x ∋ e ▹ y [ c ]
          → x ∷ Γ ∋ var zero e ▹ y ∷ Γ [ c ∷ constC unused ctxshape ]
  suc     : ∀ {Γ Δ : T⟦ ctxshape ⟧} {σ : C⟦ ctxshape ⟧} {t : T⟦ typeshape ⟧} {e n}
          → Γ ∋ var n e ▹ Δ [ σ ]
          → t ∷ Γ ∋ var (suc n) e ▹ t ∷ Δ [ constC unused typeshape ∷ σ ]


mutual
  data Branch (t : Type s) (v : ⟦ t ⟧) (n : ℕ) (p : Polarity) : ∀ {s : S⟦ ctx ⟧} → T⟦ s ⟧ → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where
    case_∶_[_] : ∀ {tv}
               → Δ ∋ var n (channel p (resume t v)) ▹ Ξ [ ξ ]
               → (t , v) ∷ Ξ ⊢▹ tv ∷ Ω [ c ∷ ω ]
               → Covered c tv
               → Branch t v n p Δ Ω (ξ ⊎ ω)


  infix 3 _⊢▹_[_]
  data _⊢▹_[_] : ∀ {s : S⟦ ctx ⟧} → T⟦ s ⟧ → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where

    pure : (t : Set) (v : t)
        → let x = pure t , v
          in x ∷ Γ ⊢▹ x ∷ Δ [ c ∷ γ ]
        →        Γ ⊢▹     Δ [     γ ]

    end : Γ ⊢▹ Γ [ constC unused ctxshape ]

    new : (s : SessionType)
        → let x = (chan (s , dual s) , tt)
              y = (chan (end , end) , tt)
          in
          x ∷ Γ ⊢▹ y ∷ Δ [ (used , used) ∷ γ ]
        →     Γ ⊢▹     Δ [                 γ ]

    par : {Γ Δ Ξ : T⟦ ctxshape ⟧} {σ ϕ : C⟦ ctxshape ⟧}
        → Γ ⊢▹ Δ [ σ ]
        → Covered {ctx} σ Δ
        → Δ ⊢▹ Ξ [ ϕ ]
        → Covered {ctx} ϕ Ξ
        → Γ ⊢▹ Ξ [ σ ⊎ ϕ ]

    send : ∀ {s t p n m}
        → Γ ∋ var n (channel p (send s t)) ▹ Δ [ δ ]
        → (v : ⟦ t ⟧)
        → Δ ∋ var m (erase t v) ▹ Ξ [ ξ ]
        → Ξ ∋ var n (channel p (resume t v)) ▹ Ω [ ω ]
        → Ω ⊢▹ Θ [ θ ]
        → Γ ⊢▹ Θ [ δ ⊎ ξ ⊎ ω ⊎ θ ]

    recv : ∀ {s t p n} {Δ : T⟦ ctxshape ⟧}
        → Γ ∋ var n (channel p (receive s t)) ▹ Δ [ δ ]
        → ((v : ⟦ t ⟧) → Branch t v n p Δ Ω ξ)
        → Γ ⊢▹ Ω [ ξ ]


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

example₂ : [] ⊢▹ [] [ [] ]
example₂ = new (session ¿ (pure Bool) foo)
  (par
    (pure Bool true (send (suc (zero (chan⁻ send))) true (zero erase) (suc (zero (chan⁻ resume))) end))
    (chan unused used ∷ [])
    (recv (zero (chan⁺ receive)) λ where
      true → case zero (chan⁺ resume) ∶ end [ pure ]
      false → case zero (chan⁺ resume) ∶ pure ℕ 2 (send (suc (suc (zero (chan⁺ send)))) 2 (zero erase) (suc (suc (zero (chan⁺ resume)))) end) [ pure ])
    (chan used unused ∷ [])
  )
