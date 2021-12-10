open import Function using (_∘_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

module Encoding.ST where

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

dual : SessionType → SessionType
dual end = end
dual (session ! t f) = session ¿ t (dual ∘ f)
dual (session ¿ t f) = session ! t (dual ∘ f)
dual (pair t f) = pair t (dual ∘ f)

TypeValue : Shape → Set₁
TypeValue s = Σ (Type s) ⟦_⟧

data Univ : Set where
  session type ctx : Univ

S⟦_⟧ : Univ → Set
S⟦ session ⟧ = ⊤
S⟦ type ⟧ = Shape
S⟦ ctx ⟧ = List Shape

T⟦_⟧ : ∀ {u} → S⟦ u ⟧ → Set₁
T⟦_⟧ {session} _ = SessionType
T⟦_⟧ {type} = TypeValue
T⟦_⟧ {ctx} = All TypeValue

private
  variable
    s : Shape
    ctxshape : S⟦ ctx ⟧
    typeshape : S⟦ type ⟧
    sessionshape : S⟦ session ⟧
    Γ Δ Ξ Ω Θ : T⟦ ctxshape ⟧
    x y : T⟦ typeshape ⟧

0∙ : Type s → Type s
0∙ (pure x) = pure x
0∙ (chan _) = chan (end , end)

0∙⟦_⟧ : (t : Type s) → ⟦ t ⟧ → ⟦ 0∙ t ⟧
0∙⟦ pure _ ⟧ v = v
0∙⟦ chan _ ⟧ v = v

data Event : Univ → Set₁ where
  receive : ∀ s → Type s → Event session
  send    : ∀ s → Type s → Event session
  resume  : (t : Type s) → ⟦ t ⟧ → Event session
  erase   : (t : Type s) → ⟦ t ⟧ → Event type
  channel : Polarity → Event session → Event type
  var     : ℕ → Event type → Event ctx

