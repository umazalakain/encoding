open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

mutual
  data Type : Set₁ where
    pure : Set → Type
    chan : Session → Type

  data Session : Set₁ where
    end : Session
    recv : (T : Type) → (⟦ T ⟧ₜ → Session) → Session
    send : (T : Type) → (⟦ T ⟧ₜ → Session) → Session

  ⟦_⟧ₜ : Type → Set
  ⟦ pure A ⟧ₜ = A
  ⟦ chan _ ⟧ₜ = ⊤

data DualSession : Session → Session → Set₁ where
  sendrecv : ∀ {T} {S R : ⟦ T ⟧ₜ → Session}
            → ((t : ⟦ T ⟧ₜ) → DualSession (S t) (R t))
            → DualSession (send T S) (recv T R)
  recvsend : ∀ {T} {S R : ⟦ T ⟧ₜ → Session}
            → ((t : ⟦ T ⟧ₜ) → DualSession (S t) (R t))
            → DualSession (recv T S) (send T R)


data Prefix (S : Session) : Session → Set₁ where
  end : Prefix S S
  send : ∀ {T C} → ((t : ⟦ T ⟧ₜ) → Prefix S (C t)) → Prefix S (send T C)
  recv : ∀ {T C} → ((t : ⟦ T ⟧ₜ) → Prefix S (C t)) → Prefix S (recv T C)


data BalancedSession : Session → Session → Set₁ where
  left : ∀ {S pS Ŝ} → Prefix S pS → DualSession S Ŝ → BalancedSession pS Ŝ
  right : ∀ {S pS Ŝ} → Prefix S pS → DualSession S Ŝ → BalancedSession Ŝ pS


TypedValue : Set₁
TypedValue = Σ Type ⟦_⟧ₜ


Ctx : Set₁
Ctx = List TypedValue


data Univ : Set where
  session type ctx : Univ

⟦_⟧ᵤ : Univ → Set₁
⟦ session ⟧ᵤ = Session
⟦ type ⟧ᵤ = TypedValue
⟦ ctx ⟧ᵤ = Ctx


data _≔_+_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set where
  left : {S : Session} → S ≔ S + end
  right : {S : Session} → S ≔ end + S

  pure : ∀ {A a} → (pure A , a) ≔ (pure A , a) + (pure A , a)
  chan : {x y z : Session}
       → x ≔ y + z
       → (chan x , tt) ≔ (chan y , tt) + (chan z , tt)

  [] : _≔_+_ {ctx} [] [] []
  _∷_ : {x y z : TypedValue} {xs ys zs : Ctx}
      → x ≔ y + z
      → xs ≔ ys + zs
      → (x ∷ xs) ≔ (y ∷ ys) + (z ∷ zs)


data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  end : Null {session} end
  pure : ∀ {A a} → Null (pure A , a)
  chan : ∀ {x} → Null x → Null (chan x , tt)
  [] : Null {ctx} []
  _∷_ : {x : TypedValue} {xs : Ctx} → Null x → Null xs → Null {ctx} (x ∷ xs)


data Action : Set₁ where
  exhaust : Action
  recv : TypedValue → Action
  send : TypedValue → Action


data _∋ₜ_▹_ : ∀ {u} → ⟦ u ⟧ᵤ → Action → ⟦ u ⟧ᵤ → Set₁ where
  recv : ∀ {T} {S : ⟦ T ⟧ₜ → Session} {t} → (recv T S) ∋ₜ (recv (T , t)) ▹ (S t)
  send : ∀ {T} {S : ⟦ T ⟧ₜ → Session} {t} → (send T S) ∋ₜ (send (T , t)) ▹ (S t)
  chan : ∀ {x α x'} → x ∋ₜ α ▹ x' → (chan x , tt) ∋ₜ α ▹ (chan x' , tt)
  exhaust-pure : ∀ {A a} → (pure A , a) ∋ₜ exhaust ▹ (pure A , a)
  exhaust-chan : ∀ {x} → (chan x , tt) ∋ₜ exhaust ▹ (pure ⊤ , tt)
  here : ∀ {x xs α x'}
       → _∋ₜ_▹_ {type} x α x'
       → _∋ₜ_▹_ {ctx} (x ∷ xs) α (x' ∷ xs)
  there : ∀ {x' xs xs' α}
        → _∋ₜ_▹_ {ctx} xs α xs'
        → _∋ₜ_▹_ {ctx} (x' ∷ xs) α (x' ∷ xs')
