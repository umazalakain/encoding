open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

module LinearPi.TypeSystem where


mutual
  data Channel : Set₁ where
    ℓ∅ : Channel
    ℓᵢ ℓₒ ℓᵢₒ # : Type → Channel

  data Type : Set₁ where
    pure : Set → Type
    prod : (T : Type) → (⟦ T ⟧ₜ → Type) → Type
    chan : Channel → Type

  ⟦_⟧ₜ : Type → Set
  ⟦ pure V ⟧ₜ = V
  ⟦ prod A B ⟧ₜ = Σ ⟦ A ⟧ₜ (⟦_⟧ₜ ∘ B)
  ⟦ chan _ ⟧ₜ = ⊤

TypedValue : Set₁
TypedValue = Σ Type ⟦_⟧ₜ

Ctx : Set₁
Ctx = List TypedValue


data Univ : Set where
  chan type ctx : Univ

⟦_⟧ᵤ : Univ → Set₁
⟦ chan ⟧ᵤ = Channel
⟦ type ⟧ᵤ = TypedValue
⟦ ctx ⟧ᵤ = Ctx


infixr 5 _∷_

data _≔_+_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set where
  ℓ∅        : ℓ∅ ≔ ℓ∅ + ℓ∅
  #         : ∀ {t} → # t ≔ # t + # t
  ℓᵢ-left   : ∀ {t} → ℓᵢ t ≔ ℓᵢ t + ℓ∅
  ℓᵢ-right  : ∀ {t} → ℓᵢ t ≔ ℓ∅ + ℓᵢ t
  ℓₒ-left   : ∀ {t} → ℓₒ t ≔ ℓₒ t + ℓ∅
  ℓₒ-right  : ∀ {t} → ℓₒ t ≔ ℓ∅ + ℓₒ t
  ℓᵢₒ-left  : ∀ {t} → ℓᵢₒ t ≔ ℓᵢₒ t + ℓ∅
  ℓᵢₒ-right : ∀ {t} → ℓᵢₒ t ≔ ℓ∅ + ℓᵢₒ t
  ℓᵢₒ       : ∀ {t} → ℓᵢₒ t ≔ ℓᵢ t + ℓₒ t
  ℓₒᵢ       : ∀ {t} → ℓᵢₒ t ≔ ℓₒ t + ℓᵢ t

  pure : ∀ {A a} → (pure A , a) ≔ (pure A , a) + (pure A , a)
  chan : ∀ {x y z} → x ≔ y + z → (chan x , tt) ≔ (chan y , tt) + (chan z , tt)
  prod-left : ∀ {A B a b} → (prod A B , (a , b)) ≔ (prod A B , (a , b)) + (pure ⊤ , tt)
  prod-right : ∀ {A B a b} → (prod A B , (a , b)) ≔ (pure ⊤ , tt) + (prod A B , (a , b))

  [] : _≔_+_ {ctx} [] [] []
  _∷_ : ∀ {a b c as bs cs}
      → _≔_+_ {type} a b c
      → _≔_+_ {ctx} as bs cs
      → _≔_+_ {ctx} (a ∷ as) (b ∷ bs) (c ∷ cs)


data _⊇_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set where
  ## : ∀ {t} → _⊇_ {chan} (# t) (# t)
  #∅ : ∀ {t} → _⊇_ {chan} (# t) ℓ∅
  #ᵢ : ∀ {t} → _⊇_ {chan} (# t) (ℓᵢ t)
  #ₒ : ∀ {t} → _⊇_ {chan} (# t) (ℓₒ t)
  ∅  :         _⊇_ {chan} ℓ∅ ℓ∅
  ᵢ  : ∀ {t} → _⊇_ {chan} (ℓᵢ t) (ℓᵢ t)
  ₒ  : ∀ {t} → _⊇_ {chan} (ℓₒ t) (ℓₒ t)
  ᵢₒ : ∀ {t} → _⊇_ {chan} (ℓᵢₒ t) (ℓᵢₒ t)

  pure : ∀ {A a} → (pure A , a) ⊇ (pure A , a)
  chan : ∀ {x y} → x ⊇ y → (chan x , tt) ⊇ (chan y , tt)
  prod : ∀ {A B a b A' B' a' b'} → (A , a) ⊇ (A' , a') → (B a , b) ⊇ (B' a' , b') → (prod A B , (a , b)) ⊇ (prod A' B' , (a' , b'))

  [] : _⊇_ {ctx} [] []
  _∷_ : ∀ {a b as bs}
      → _⊇_ {type} a b
      → _⊇_ {ctx} as bs
      → _⊇_ {ctx} (a ∷ as) (b ∷ bs)

data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  ℓ∅   : Null {u = chan} ℓ∅
  #    : ∀ {t} → Null {u = chan} (# t)
  pure : ∀ {A a} → Null (pure A , a)
  chan : ∀ {x} → Null x → Null (chan x , tt)
  []   : Null {u = ctx} []
  _∷_  : ∀ {x xs}
       → Null {u = type} x
       → Null {u = ctx} xs
       → Null {u = ctx} (x ∷ xs)


record _⊇_+_ {u} (x y z : ⟦ u ⟧ᵤ) : Set₁ where
  constructor _,_
  field
    {m} : ⟦ u ⟧ᵤ
    sum : m ≔ y + z
    sup : x ⊇ m


data _∋_ : Ctx → TypedValue → Set₁ where
  here : ∀ {x xs}
       → Null xs
       → (x ∷ xs) ∋ x
  there : ∀ {x x' xs}
        → Null x'
        → xs ∋ x
        → (x' ∷ xs) ∋ x


data Term : Ctx → TypedValue → Set₁ where
  var : ∀ {xs x} → xs ∋ x → Term xs x
  pure : ∀ {xs A} a → Null xs → Term xs (pure A , a)
  pair : ∀ {xs ys zs X Y x y}
       → xs ⊇ ys + zs
       → Term ys (X , x)
       → Term zs (Y x , y)
       → Term xs (prod X Y , (x , y))


data Process : Ctx → Set₁ where
  end : ∀ {xs}
      → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ⊇ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {xs} x
      → Process ((chan x , tt) ∷ xs)
      → Process xs
  rep : ∀ {xs}
      → Null xs
      → Process xs
      → Process xs
  send : ∀ {xs ys zs vs ws T t}
       → xs ⊇ ys + zs
       → Term ys (T , t)
       → zs ⊇ vs + ws
       → Term vs (chan (ℓₒ T) , tt)
       → Process ws
       → Process xs
  recv : ∀ {xs ys zs T}
       → xs ⊇ ys + zs
       → Term ys (chan (ℓᵢ T) , tt)
       → (∀ (t : ⟦ T ⟧ₜ ) → Process ((T , t) ∷ zs))
       → Process xs
  letprod : ∀ {xs ys zs A B a b}
          → xs ⊇ ys + zs
          → Term ys (prod A B , (a , b))
          → Process ((A , a) ∷ (B a , b) ∷ zs)
          → Process xs
