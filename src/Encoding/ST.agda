open import Function using (_∘_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

module Encoding.ST where

data Action : Set where
  ! ¿ : Action

mutual

  data SessionType : Set₁ where
    end     : SessionType
    session : Action → (t : Type) → (f : ⟦ t ⟧ → SessionType) → SessionType
    pair    :          (t : Type) → (f : ⟦ t ⟧ → SessionType) → SessionType

  data Type : Set₁ where
    pure : Set → Type
    chan : SessionType × SessionType → Type

  ⟦_⟧ : Type → Set
  ⟦ pure x ⟧ = x
  ⟦ chan _ ⟧ = ⊤

data Polarity : Set where
  ⁺ ⁻ : Polarity

dual : SessionType → SessionType
dual end = end
dual (session ! t f) = session ¿ t (dual ∘ f)
dual (session ¿ t f) = session ! t (dual ∘ f)
dual (pair t f) = pair t (dual ∘ f)

TypeValue : Set₁
TypeValue = Σ Type ⟦_⟧

data Univ : Set where
  session type ctx : Univ

T⟦_⟧ : Univ → Set₁
T⟦_⟧ session = SessionType
T⟦_⟧ type = TypeValue
T⟦_⟧ ctx = List TypeValue

private
  variable
    Γ Δ Ξ Ω Θ : T⟦ ctx ⟧
    x y : T⟦ type ⟧

0∙ : Type → Type
0∙ (pure x) = pure x
0∙ (chan _) = chan (end , end)

0∙⟦_⟧ : (t : Type) → ⟦ t ⟧ → ⟦ 0∙ t ⟧
0∙⟦ pure _ ⟧ v = v
0∙⟦ chan _ ⟧ v = v

data Event : Univ → Set₁ where
  receive : Type → Event session
  send    : Type → Event session
  resume  : (t : Type) → ⟦ t ⟧ → Event session
  erase   : (t : Type) → ⟦ t ⟧ → Event type
  channel : Polarity → Event session → Event type
  var     : ℕ → Event type → Event ctx

