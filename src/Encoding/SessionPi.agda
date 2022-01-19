open import Function using (_∘_)
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

dual : Session → Session
dual end = end
dual (recv T C) = send T (dual ∘ C)
dual (send T C) = recv T (dual ∘ C)


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
  exhaust : TypedValue → Action
  recv : (T : Type) (t : ⟦ T ⟧ₜ) (C : ⟦ T ⟧ₜ → Session) → Action
  send : (T : Type) (t : ⟦ T ⟧ₜ) (C : ⟦ T ⟧ₜ → Session) → Action


data _∋ₜ_▹_ : ∀ {u} → ⟦ u ⟧ᵤ → Action → ⟦ u ⟧ᵤ → Set₁ where
  recv : ∀ {T} {S : ⟦ T ⟧ₜ → Session} {t} → (recv T S) ∋ₜ recv T t S ▹ (S t)
  send : ∀ {T} {S : ⟦ T ⟧ₜ → Session} {t} → (send T S) ∋ₜ send T t S ▹ (S t)
  chan : ∀ {x α x'} → x ∋ₜ α ▹ x' → (chan x , tt) ∋ₜ α ▹ (chan x' , tt)
  exhaust-pure : ∀ {A a} → (pure A , a) ∋ₜ exhaust (pure A , a) ▹ (pure A , a)
  exhaust-chan : ∀ {x} → (chan x , tt) ∋ₜ exhaust (chan x , tt) ▹ (pure ⊤ , tt)
  here : ∀ {x xs α x'}
       → _∋ₜ_▹_ {type} x α x'
       → _∋ₜ_▹_ {ctx} (x ∷ xs) α (x' ∷ xs)
  there : ∀ {x' xs xs' α}
        → _∋ₜ_▹_ {ctx} xs α xs'
        → _∋ₜ_▹_ {ctx} (x' ∷ xs) α (x' ∷ xs')


data Process : Ctx → Set₁ where
  end : ∀ {xs} → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ≔ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {xs} S
      → Process ((chan S , tt) ∷ (chan (dual S) , tt) ∷ xs)
      → Process xs
  rep : ∀ {xs} → Null xs → Process xs → Process xs
  send : ∀ {xs ys zs T t C}
       → xs ∋ₜ exhaust (T , t) ▹ ys
       → ys ∋ₜ send T t C ▹ zs
       → Process zs
       → Process xs
  recv : ∀ {xs ys T C}
       → ((t : ⟦ T ⟧ₜ) → xs ∋ₜ recv T t C ▹ ys × Process ((T , t) ∷ ys))
       → Process xs

