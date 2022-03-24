open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

module LinearPi.TypeSystem where


mutual
  data Linear : Set₁ where
    ℓ∅ : Linear
    ℓᵢ ℓₒ ℓᵢₒ : Type → Linear

  data Type : Set₁ where
    pure : Set → Type
    prod : (T : Type) → (⟦ T ⟧ₜ → Type) → Type
    line : Linear → Type
    unre : Type → Type

  ⟦_⟧ₜ : Type → Set
  ⟦ pure V ⟧ₜ = V
  ⟦ prod A B ⟧ₜ = Σ ⟦ A ⟧ₜ (⟦_⟧ₜ ∘ B)
  ⟦ line _ ⟧ₜ = ⊤
  ⟦ unre _ ⟧ₜ = ⊤

TypedValue : Set₁
TypedValue = Σ Type ⟦_⟧ₜ

Ctx : Set₁
Ctx = List TypedValue


data Univ : Set where
  linear type ctx : Univ

⟦_⟧ᵤ : Univ → Set₁
⟦ linear ⟧ᵤ = Linear
⟦ type ⟧ᵤ = TypedValue
⟦ ctx ⟧ᵤ = Ctx


infixr 5 _∷_

data _≔_+_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set where
  ℓ∅        : ℓ∅ ≔ ℓ∅ + ℓ∅
  ℓᵢ-left   : ∀ {t} → ℓᵢ t ≔ ℓᵢ t + ℓ∅
  ℓᵢ-right  : ∀ {t} → ℓᵢ t ≔ ℓ∅ + ℓᵢ t
  ℓₒ-left   : ∀ {t} → ℓₒ t ≔ ℓₒ t + ℓ∅
  ℓₒ-right  : ∀ {t} → ℓₒ t ≔ ℓ∅ + ℓₒ t
  ℓᵢₒ-left  : ∀ {t} → ℓᵢₒ t ≔ ℓᵢₒ t + ℓ∅
  ℓᵢₒ-right : ∀ {t} → ℓᵢₒ t ≔ ℓ∅ + ℓᵢₒ t
  ℓᵢₒ       : ∀ {t} → ℓᵢₒ t ≔ ℓᵢ t + ℓₒ t
  ℓₒᵢ       : ∀ {t} → ℓᵢₒ t ≔ ℓₒ t + ℓᵢ t
  -- TODO: augment with unrestricted channel types

  pure : ∀ {A a} → (pure A , a) ≔ (pure A , a) + (pure A , a)
  line : ∀ {x y z} → x ≔ y + z → (line x , tt) ≔ (line y , tt) + (line z , tt)
  unre : ∀ {x} → (unre x , tt) ≔ (unre x , tt) + (unre x , tt)
  prod-left : ∀ {A B a b} → (prod A B , (a , b)) ≔ (prod A B , (a , b)) + (pure ⊤ , tt)
  prod-right : ∀ {A B a b} → (prod A B , (a , b)) ≔ (pure ⊤ , tt) + (prod A B , (a , b))

  [] : _≔_+_ {ctx} [] [] []
  _∷_ : ∀ {a b c as bs cs}
      → _≔_+_ {type} a b c
      → _≔_+_ {ctx} as bs cs
      → _≔_+_ {ctx} (a ∷ as) (b ∷ bs) (c ∷ cs)



data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  ℓ∅   : Null {u = linear} ℓ∅
  pure : ∀ {A a} → Null (pure A , a)
  line : ∀ {x} → Null x → Null (line x , tt)
  unre : ∀ {x} → Null (unre x , tt)
  []   : Null {u = ctx} []
  _∷_  : ∀ {x xs}
       → Null {u = type} x
       → Null {u = ctx} xs
       → Null {u = ctx} (x ∷ xs)


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
       → xs ≔ ys + zs
       → Term ys (X , x)
       → Term zs (Y x , y)
       → Term xs (prod X Y , (x , y))


data New : TypedValue → Set₁ where
  line : ∀ t → New (line (ℓᵢₒ t) , tt)
  unre : ∀ t → New (unre t , tt)

data Process : Ctx → Set₁ where
  end : ∀ {xs}
      → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ≔ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {x xs}
      → New x
      → Process (x ∷ xs)
      → Process xs
  rep : ∀ {xs}
      → Null xs
      → Process xs
      → Process xs
  send-unre : ∀ {xs ys zs vs ws T t}
            → xs ≔ ys + zs
            → Term ys (T , t)
            → zs ≔ vs + ws
            → Term vs (unre T , tt)
            → Process ws
            → Process xs
  recv-unre : ∀ {xs ys zs T}
            → xs ≔ ys + zs
            → Term ys (unre T , tt)
            → (∀ (t : ⟦ T ⟧ₜ ) → Process ((T , t) ∷ zs))
            → Process xs
  send-line : ∀ {xs ys zs vs ws T t}
            → xs ≔ ys + zs
            → Term ys (T , t)
            → zs ≔ vs + ws
            → Term vs (line (ℓₒ T) , tt)
            → Process ws
            → Process xs
  recv-line : ∀ {xs ys zs T}
            → xs ≔ ys + zs
            → Term ys (line (ℓᵢ T) , tt)
            → (∀ (t : ⟦ T ⟧ₜ ) → Process ((T , t) ∷ zs))
            → Process xs
  letprod   : ∀ {xs ys zs A B a b}
            → xs ≔ ys + zs
            → Term ys (prod A B , (a , b))
            → Process ((A , a) ∷ (B a , b) ∷ zs)
            → Process xs
