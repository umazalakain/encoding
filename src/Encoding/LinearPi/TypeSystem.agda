open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

module LinearPi.TypeSystem where


data Usage : Set₁ where
  #0 #1 #ω : Usage

mutual
  data Type : Set₁ where
    pure : Set → Type
    prod : (T : Type) → (⟦ T ⟧ₜ → Type) → Type
    chan : Usage → Usage → Type → Type

  ⟦_⟧ₜ : Type → Set
  ⟦ pure V ⟧ₜ = V
  ⟦ prod A B ⟧ₜ = Σ ⟦ A ⟧ₜ (⟦_⟧ₜ ∘ B)
  ⟦ chan _ _ _ ⟧ₜ = ⊤


TypedValue : Set₁
TypedValue = Σ Type ⟦_⟧ₜ


Ctx : Set₁
Ctx = List TypedValue



data Univ : Set where
  usage type ctx : Univ

⟦_⟧ᵤ : Univ → Set₁
⟦ usage ⟧ᵤ = Usage
⟦ type ⟧ᵤ = TypedValue
⟦ ctx ⟧ᵤ = Ctx


infixr 5 _∷_

data _≔_+_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set where
  -- linear
  #0 : #0 ≔ #0 + #0
  #1-left : #1 ≔ #1 + #0
  #1-right : #1 ≔ #0 + #1
  prod-left : ∀ {A B a b} → (prod A B , (a , b)) ≔ (prod A B , (a , b)) + (pure ⊤ , tt)
  prod-right : ∀ {A B a b} → (prod A B , (a , b)) ≔ (pure ⊤ , tt) + (prod A B , (a , b))

  -- shared
  #ω : #ω ≔ #ω + #ω
  pure : ∀ {A a} → (pure A , a) ≔ (pure A , a) + (pure A , a)
  [] : _≔_+_ {ctx} [] [] []

  -- recursive
  chan : ∀ {ix iy iz ox oy oz T}
       → ix ≔ iy + iz
       → ox ≔ oy + oz
       → (chan ix ox T , tt) ≔ (chan iy oy T , tt) + (chan iz oz T , tt)
  _∷_ : ∀ {a b c as bs cs}
      → _≔_+_ {type} a b c
      → _≔_+_ {ctx} as bs cs
      → _≔_+_ {ctx} (a ∷ as) (b ∷ bs) (c ∷ cs)


data _⊆_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set₁ where
  -- linear
  #0 : _⊆_ {usage} #0 #0
  #1 : _⊆_ {usage} #1 #1
  prod : ∀ {A a B b} → (prod A B , (a , b)) ⊆ (prod A B , (a , b))

  --shared
  #ω : ∀ {m} → _⊆_ {usage} m #ω
  pure : ∀ {A a} → (pure A , a) ⊆ (pure A , a)
  [] : _⊆_ {ctx} [] []

  -- recursive
  chan : ∀ {il ol ir or : Usage} {s t}
       → il ⊆ ir
       → ol ⊆ or
       → s ≡ t
       → (chan il ol s , tt) ⊆ (chan ir or t , tt)
  _∷_ : ∀ {l r ls rs}
      → _⊆_ {type} l r
      → _⊆_ {ctx} ls rs
      → _⊆_ {ctx} (l ∷ ls) (r ∷ rs)


data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  #0 : Null {u = usage} #0
  #ω : Null {u = usage} #ω
  pure : ∀ {A a} → Null (pure A , a)
  chan : ∀ {i o : Usage} {t : Type}
       → Null i
       → Null o
       → Null (chan i o t , tt)
  [] : Null {u = ctx} []
  _∷_ : ∀ {x xs}
      → Null {u = type} x
      → Null {u = ctx} xs
      → Null {u = ctx} (x ∷ xs)


data _∋_ : Ctx → TypedValue → Set₁ where
  here : ∀ {x x' xs}
       → Null xs
       → x ⊆ x'
       → (x' ∷ xs) ∋ x
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


data Process : Ctx → Set₁ where
  end : ∀ {xs}
      → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ≔ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {xs} i o t
      → Process ((chan i o t , tt) ∷ xs)
      → Process xs
  rep : ∀ {xs}
      → Null xs
      → Process xs
      → Process xs
  send : ∀ {xs ys zs vs ws T t}
       → xs ≔ ys + zs
       → Term ys (T , t)
       → zs ≔ vs + ws
       → Term vs (chan #0 #1 T , tt)
       → Process ws
       → Process xs
  recv : ∀ {xs ys zs T}
       → xs ≔ ys + zs
       → Term ys (chan #1 #0 T , tt)
       → (∀ (t : ⟦ T ⟧ₜ ) → Process ((T , t) ∷ zs))
       → Process xs
  letprod : ∀ {xs ys zs A B a b}
          → xs ≔ ys + zs
          → Term ys (prod A B , (a , b))
          → Process ((A , a) ∷ (B a , b) ∷ zs)
          → Process xs
