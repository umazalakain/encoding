

open import Function using (_∘_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

module LeftoverST where

data Action : Set where
  ! ¿ : Action

data Shape : Set where
  pure chan : Shape

mutual

  data SessionType : Set₁ where
    end : SessionType
    session : ∀ {s} → Action → (t : Type s) → (f : ⟦ t ⟧ → SessionType) → SessionType
    pair : ∀ {s} → (t : Type s) → (f : ⟦ t ⟧ → SessionType) → SessionType

  data Type : Shape → Set₁ where
    pure : Set → Type pure
    chan : SessionType × SessionType → Type chan

  ⟦_⟧ : ∀ {s} → Type s → Set
  ⟦ pure x ⟧ = x
  ⟦ chan _ ⟧ = ⊤

data Polarity : Set where
  ⁺ ⁻ : Polarity

data Cover : Set₁ where
  used : Cover
  unused : Cover

data Univ : Set where
  session type ctx : Univ

dual : SessionType → SessionType
dual end = end
dual (session ! t f) = session ¿ t (dual ∘ f)
dual (session ¿ t f) = session ! t (dual ∘ f)
dual (pair t f) = pair t (dual ∘ f)

TypeValue : Shape → Set₁
TypeValue s = Σ (Type s) ⟦_⟧

TypeCover : Shape → Set₁
TypeCover pure = ⊤
TypeCover chan = Cover × Cover

S⟦_⟧ : Univ → Set
S⟦ session ⟧ = ⊤
S⟦ type ⟧ = Shape
S⟦ ctx ⟧ = List Shape

T⟦_⟧ : ∀ {u} → S⟦ u ⟧ → Set₁
T⟦_⟧ {session} _ = SessionType
T⟦_⟧ {type} = TypeValue
T⟦_⟧ {ctx} = All TypeValue

C⟦_⟧ : ∀ {u} → S⟦ u ⟧ → Set₁
C⟦_⟧ {session} _ = Cover
C⟦_⟧ {type} = TypeCover
C⟦_⟧ {ctx} = All TypeCover

variable
  s : Shape
  ctxshape : S⟦ ctx ⟧
  typeshape : S⟦ type ⟧
  sessionshape : S⟦ session ⟧
  Γ Δ Ξ Ω Θ : T⟦ ctxshape ⟧
  γ δ ξ ω θ β : C⟦ ctxshape ⟧
  x y : T⟦ typeshape ⟧
  c : C⟦ typeshape ⟧


0∙ : Type s → Type s
0∙ (pure x) = pure x
0∙ (chan _) = chan (end , end)

0∙⟦_⟧ : (t : Type s) → ⟦ t ⟧ → ⟦ 0∙ t ⟧
0∙⟦ pure _ ⟧ v = v
0∙⟦ chan _ ⟧ v = v

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


data Event : Univ → Set₁ where
  receive : ∀ s → Type s → Event session
  send    : ∀ s → Type s → Event session
  resume  : (t : Type s) → ⟦ t ⟧ → Event session
  erase   : (t : Type s) → ⟦ t ⟧ → Event type
  channel : Polarity → Event session → Event type
  var     : ℕ → Event type → Event ctx


data Transition : ∀ {u} {s : S⟦ u ⟧} → Event u → T⟦ s ⟧ → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where
  receive : ∀ {t f} → Transition (receive s t) (session ¿ t f) (pair t f) used
  send    : ∀ {t f} → Transition (send s t) (session ! t f) (pair t f) used
  resume  : ∀ {s} {t : Type s} {f} {v : ⟦ t ⟧} → Transition (resume t v) (pair t f) (f v) used
  erase   : ∀ {s t v} → Transition {s = s} (erase t v) (t , v) (0∙ t , 0∙⟦ t ⟧ v) (constC used s)
  chan⁺   : ∀ {x y z e c} → Transition e x y c → Transition (channel ⁺ e) (chan (x , z) , tt) (chan (y , z) , tt) (c , unused)
  chan⁻   : ∀ {x y z e c} → Transition e x y c → Transition (channel ⁻ e) (chan (z , x) , tt) (chan (z , y) , tt) (unused , c)

infix 3 _∋_▹_[_]
data _∋_▹_[_] : ∀ {s : S⟦ ctx ⟧} → T⟦ s ⟧ → Event ctx → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where
  zero : ∀ {e} {x y : T⟦ typeshape ⟧} {c : C⟦ typeshape ⟧}
       → Transition e x y c
       → x ∷ Γ ∋ var zero e ▹ y ∷ Γ [ c ∷ constC unused ctxshape ]

  suc : ∀ {Γ Δ : T⟦ ctxshape ⟧} {σ : C⟦ ctxshape ⟧} {t : T⟦ typeshape ⟧} {e n}
      →     Γ ∋ var      n  e ▹     Δ [                          σ ]
      → t ∷ Γ ∋ var (suc n) e ▹ t ∷ Δ [ constC unused typeshape ∷ σ ]


mutual
  data Branch (t : Type s) (v : ⟦ t ⟧) (n : ℕ) (p : Polarity) : ∀ {s : S⟦ ctx ⟧} → T⟦ s ⟧ → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where
    case_∶_ : Δ ∋ var n (channel p (resume t v)) ▹ Ξ [ ξ ]
            → (t , v) ∷ Ξ ⊢▹ (0∙ t , 0∙⟦ t ⟧ v) ∷ Ω [ c ∷ ω ]
            → Branch t v n p Δ Ω (ξ ⊎ ω)


  infix 3 _⊢▹_[_]
  data _⊢▹_[_] : ∀ {s : S⟦ ctx ⟧} → T⟦ s ⟧ → T⟦ s ⟧ → C⟦ s ⟧ → Set₁ where

    pure : (t : Set) (v : t)
        → let x = pure t , v
          in x ∷ Γ ⊢▹ x ∷ Δ [ c ∷ γ ]
        →        Γ ⊢▹     Δ [     γ ]

    end : Γ ⊢▹ Γ [ constC unused ctxshape ]

    new : {ch' : T⟦ chan ⟧}
        → (s : SessionType)
        → let ch = chan (s , dual s) in
          (ch , tt) ∷ Γ ⊢▹ ch' ∷ Δ [ c ∷ γ ]
        → Covered c ch'
        →             Γ ⊢▹       Δ [     γ ]

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


open import Data.Nat as ℕ using (ℕ; zero; suc)

replicate : Action → Type s → ℕ → SessionType
replicate a t zero = end
replicate a t (suc n) = session a t (λ _ → replicate a t n)


receiving : ∀ v → Branch (pure ℕ) v zero ⁺ ((chan (pair (pure ℕ) (replicate ! (pure ⊤)) , end) , tt) ∷ []) ((chan (end , end) , tt) ∷ []) ((used , unused) ∷ [])
receiving zero = case zero (chan⁺ resume) ∶ end
receiving (suc v) = case zero (chan⁺ resume) ∶ recv {!!} {!!}

example₁ : [] ⊢▹ [] [ [] ]
example₁ = new
  (session ¿ (pure ℕ) (replicate ! (pure ⊤)))
  (par
    (pure ℕ 2 (send (suc (zero (chan⁻ send))) 2 (zero erase) (suc (zero (chan⁻ resume))) (recv (suc (zero (chan⁻ receive))) (λ {tt → case suc (zero (chan⁻ resume)) ∶ recv (suc (suc (zero (chan⁻ receive)))) λ {tt → case suc (suc (zero (chan⁻ resume))) ∶ end}}))))
    ((chan unused used) ∷ [])
    (recv (zero (chan⁺ receive)) λ v → {!!})
    {!!}
  )
  {!!}

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
      true → case zero (chan⁺ resume) ∶ end
      false → case zero (chan⁺ resume) ∶ pure ℕ 2 (send (suc (suc (zero (chan⁺ send)))) 2 (zero erase) (suc (suc (zero (chan⁺ resume)))) end))
    (chan used unused ∷ [])
  )
  (chan used used)
