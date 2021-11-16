

open import Function using (_∘_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

module SessionTypes where

data Action : Set where
  ! ¿ : Action

mutual

  data SessionType : Set₁ where
    end : SessionType
    session : Action → (t : Type) → (f : ⟦ t ⟧ → SessionType) → SessionType
    pair : (t : Type) → (f : ⟦ t ⟧ → SessionType) → SessionType

  data Type : Set₁ where
    pure : Set → Type
    chan : SessionType × SessionType → Type

  ⟦_⟧ : Type → Set
  ⟦ pure x ⟧ = x
  ⟦ chan _ ⟧ = ⊤

data Cover : Set₁ where
  fresh : Cover
  stale : Cover

TypeValue : Set₁
TypeValue = Σ Type ⟦_⟧


TVCover : TypeValue → Set₁
TVCover (pure _ , _) = ⊤
TVCover (chan _ , _) = Cover × Cover

dual : SessionType → SessionType
dual end = end
dual (session ! t f) = session ¿ t (dual ∘ f)
dual (session ¿ t f) = session ! t (dual ∘ f)
dual (pair t f) = pair t (dual ∘ f)


Ctx : Set₁
Ctx = List TypeValue

CtxCover : Ctx → Set₁
CtxCover = All TVCover

variable
  Γ Δ Ξ Ω Θ : Ctx
  s t r p : TypeValue
  σ ϕ : CtxCover Γ

data Polarity : Set where
  ⁺ ⁻ : Polarity


0∙ : Type → Type
0∙ (pure x) = pure x
0∙ (chan _) = chan (end , end)

0∙⟦_⟧ : ∀ t → ⟦ t ⟧ → ⟦ 0∙ t ⟧
0∙⟦ pure _ ⟧ v = v
0∙⟦ chan _ ⟧ v = v

data Univ : Set where
  session type ctx : Univ

U⟦_⟧ : Univ → Set₁
U⟦ session ⟧ = SessionType
U⟦ type ⟧ = TypeValue
U⟦ ctx ⟧ = Ctx

UCover : ∀ u → U⟦ u ⟧ → Set₁
UCover session _ = Cover
UCover type = TVCover
UCover ctx = CtxCover

_⇓_ : ∀ {u} → (t : U⟦ u ⟧) → UCover u t → U⟦ u ⟧
_⇓_ {session} st fresh = st
_⇓_ {session} st stale = end
_⇓_ {type} (pure x , v) c = pure x , v
_⇓_ {type} (chan (p , n) , v) (cp , cn) = chan (p ⇓ cp , n ⇓ cn) , v
_⇓_ {ctx} [] c = []
_⇓_ {ctx} (t ∷ ts) (c ∷ cs) = t ⇓ c ∷ ts ⇓ cs

constC : Cover → ∀ {u} → (t : U⟦ u ⟧) → UCover u t
constC c {session} t = c
constC c {type} (pure x , v) = tt
constC c {type} (chan x , v) = c , c
constC c {ctx} [] = []
constC c {ctx} (t ∷ ts) = constC c t ∷ constC c ts

data SEvent : Set₁ where
  receive : Type → SEvent
  send    : Type → SEvent
  resume  : (t : Type) → ⟦ t ⟧ → SEvent

data TVEvent : Set₁ where
  erase   : (t : Type) → ⟦ t ⟧ → TVEvent
  channel : Polarity → SEvent → TVEvent

data CtxEvent : Set₁ where
  var  : ℕ → TVEvent → CtxEvent


data STransition : SEvent → SessionType → SessionType → Set₁ where
  receive : ∀ {t f}
          → STransition (receive t) (session ¿ t f) (pair t f)
  send    : ∀ {t f}
          → STransition (send t) (session ! t f) (pair t f)
  resume  : ∀ {t f} {v : ⟦ t ⟧}
          → STransition (resume t v) (pair t f) (f v)

data TVTransition : TVEvent → TypeValue → (t : TypeValue) → TVCover t → Set₁ where
  erase : ∀ {t v} → TVTransition (erase t v) (t , v) (0∙ t , 0∙⟦ t ⟧ v) (constC stale {!!})
  chan⁺ : ∀ {x y z e} → STransition e x y → TVTransition (channel ⁺ e) (chan (x , z) , tt) (chan (y , z) , tt) (stale , fresh)
  chan⁻ : ∀ {x y z e} → STransition e x y → TVTransition (channel ⁻ e) (chan (z , x) , tt) (chan (z , y) , tt) (fresh , stale)

infix 3 _∋_▹_[_]
data _∋_▹_[_] : Ctx → CtxEvent → (Γ : Ctx) → CtxCover Γ → Set₁ where
  zero : ∀ {e x y c}
       → TVTransition e x y c
       → x ∷ Γ ∋ var zero e ▹ y ∷ Γ [ c ∷ constC fresh Γ ]

  suc : ∀ {e n}
      →     Γ ∋ var      n  e ▹     Δ [                  σ ]
      → t ∷ Γ ∋ var (suc n) e ▹ t ∷ Δ [ constC fresh t ∷ σ ]


infix 3 _⊢▹_[_]
data _⊢▹_[_] : Ctx → (Γ : Ctx) → CtxCover Γ → Set₁ where

  pure : (t : Set) (v : t)
       → let x = pure t , v
         in x ∷ Γ ⊢▹ x ∷ Δ [ constC stale x ∷ σ ]
       →        Γ ⊢▹     Δ [                  σ ]

  end : Γ ⊢▹ Γ [ constC fresh Γ ]

  new : (s : SessionType)
      → let c = chan (s , dual s) in
        (c , tt) ∷ Γ ⊢▹ (0∙ c , tt) ∷ Δ [ constC stale (0∙ c , tt) ∷ σ ]
      →            Γ ⊢▹               Δ [                            σ ]

  par : Γ     ⊢▹ Δ [ σ ]
      → Δ ⇓ σ ⊢▹ Ξ [ ϕ ]
      → Γ     ⊢▹ Ξ [ {!!} ]

  send : ∀ {t p n m}
       → Γ ∋ var n (channel p (send t)) ▹ Δ [ {!!} ]
       → (v : ⟦ t ⟧)
       → Δ ∋ var m (erase t v) ▹ Ξ [ {!!} ]
       → Ξ ∋ var n (channel p (resume t v)) ▹ Ω [ {!!} ]
       → Ω ⊢▹ Θ [ {!!} ]
       → Γ ⊢▹ Θ [ {!!} ]

  recv : ∀ {t p n}
       → Γ ∋ var n (channel p (receive t)) ▹ Δ [ {!!} ]
       → ((v : ⟦ t ⟧) → Σ[ Ξ ∈ Ctx ]
           Δ ∋ var n (channel p (resume t v)) ▹ Ξ [ {!!} ]
         × (t , v) ∷ Ξ ⊢▹ (0∙ t , 0∙⟦ t ⟧ v) ∷ Ω [ {!!} ])
       → Γ ⊢▹ Ω [ {!!} ]


open import Data.Nat as ℕ using (ℕ; zero; suc)

replicate : Action → Type → ℕ → SessionType
replicate a t zero = end
replicate a t (suc n) = session a t (λ _ → replicate a t n)



{-
example₁ : Process [] []
example₁ = new
  (session ¿ (pure ℕ) (replicate ! (pure ⊤)))
  (par
    (send ⁻ zero 1 pure ⁻ zero (recv ⁻ zero (λ v → _ , _ , ⁻ , zero , end)))
    (recv ⁺ zero {!!})
  )

-}

open import Data.Bool using (Bool; true; false)

foo : Bool → SessionType
foo true = end
foo false = session ! (pure ℕ) (λ _ → end)

example₂ : [] ⊢▹ [] [ [] ]
example₂ = new (session ¿ (pure Bool) foo)
  (par
    (pure Bool true (send (suc (zero (chan⁻ send))) true (zero erase) (suc (zero (chan⁻ resume))) end))
    (recv (zero (chan⁺ receive)) λ where
      true → _ , zero (chan⁺ resume) , end
      false → _ , zero (chan⁺ resume) , pure ℕ 2 (send (suc (suc (zero (chan⁺ send)))) 2 (zero erase) (suc (suc (zero (chan⁺ resume)))) end)))
