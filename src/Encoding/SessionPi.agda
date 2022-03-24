open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

mutual
  data Type : Set₁ where
    pure : Set → Type
    sesh : Session → Type
    unre : Type → Type

  data Session : Set₁ where
    end : Session
    recv : (T : Type) → (⟦ T ⟧ₜ → Session) → Session
    send : (T : Type) → (⟦ T ⟧ₜ → Session) → Session

  ⟦_⟧ₜ : Type → Set
  ⟦ pure A ⟧ₜ = A
  ⟦ sesh _ ⟧ₜ = ⊤
  ⟦ unre _ ⟧ₜ = ⊤

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
  unre : ∀ {T t} → (unre T , t) ≔ (unre T , t) + (unre T , t)
  sesh : {x y z : Session}
       → x ≔ y + z
       → (sesh x , tt) ≔ (sesh y , tt) + (sesh z , tt)

  [] : _≔_+_ {ctx} [] [] []
  _∷_ : {x y z : TypedValue} {xs ys zs : Ctx}
      → x ≔ y + z
      → xs ≔ ys + zs
      → (x ∷ xs) ≔ (y ∷ ys) + (z ∷ zs)


data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  end : Null {session} end
  pure : ∀ {A a} → Null (pure A , a)
  unre : ∀ {x} → Null (unre x , tt)
  sesh : ∀ {x} → Null x → Null (sesh x , tt)
  [] : Null {ctx} []
  _∷_ : {x : TypedValue} {xs : Ctx} → Null x → Null xs → Null {ctx} (x ∷ xs)


data Action : Set₁ where
  at : ℕ → Action → Action
  exhaust : TypedValue → Action
  recv-sesh : (T : Type) (t : ⟦ T ⟧ₜ) (C : ⟦ T ⟧ₜ → Session) → Action
  send-sesh : (T : Type) (t : ⟦ T ⟧ₜ) (C : ⟦ T ⟧ₜ → Session) → Action
  is-type : (T : TypedValue) → Action


data _∋ₜ_▹_ : ∀ {u} → ⟦ u ⟧ᵤ → Action → ⟦ u ⟧ᵤ → Set₁ where
  is-type : ∀ {T} → _∋ₜ_▹_ {type} T (is-type T) T

  recv-sesh : ∀ {T t} {S : ⟦ T ⟧ₜ → Session} → (sesh (recv T S) , tt) ∋ₜ (recv-sesh T t S) ▹ (sesh (S t) , tt)
  send-sesh : ∀ {T t} {S : ⟦ T ⟧ₜ → Session} → (sesh (send T S) , tt) ∋ₜ (send-sesh T t S) ▹ (sesh (S t) , tt)

  exhaust-unre : ∀ {T t} → (unre T , t) ∋ₜ exhaust (unre T , t) ▹ (unre T , t)
  exhaust-pure : ∀ {A a} → (pure A , a) ∋ₜ exhaust (pure A , a) ▹ (pure A , a)
  exhaust-sesh : ∀ {x} → (sesh x , tt) ∋ₜ exhaust (sesh x , tt) ▹ (sesh end , tt)

  here : ∀ {x xs α x'}
       → _∋ₜ_▹_ {type} x α x'
       → _∋ₜ_▹_ {ctx} (x ∷ xs) (at zero α) (x' ∷ xs)
  there : ∀ {x' xs xs' n α}
        → _∋ₜ_▹_ {ctx} xs (at n α) xs'
        → _∋ₜ_▹_ {ctx} (x' ∷ xs) (at (suc n) α) (x' ∷ xs')


data New : TypedValue → TypedValue → Set₁ where
  sesh : ∀ S → New (sesh S , tt) (sesh (dual S) , tt)
  unre : ∀ t → New (unre t , tt) (unre t , tt)

data Process : Ctx → Set₁ where
  end : ∀ {xs} → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ≔ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {xs x y}
      → New x y
      → Process (x ∷ y ∷ xs)
      → Process xs
  rep : ∀ {xs} → Null xs → Process xs → Process xs
  send-sesh : ∀ {xs n ys m zs T t C}
            → xs ∋ₜ at n (exhaust (T , t)) ▹ ys
            → ys ∋ₜ at m (send-sesh T t C) ▹ zs
            → Process zs
            → Process xs
  recv-sesh : ∀ {xs n ys zs T C}
            → xs ∋ₜ at n (is-type (sesh (recv T C) , tt)) ▹ ys
            → ((t : ⟦ T ⟧ₜ) → xs ∋ₜ at n (recv-sesh T t C) ▹ zs × Process ((T , t) ∷ zs))
            → Process xs
  send-unre : ∀ {xs n ys m zs T t}
            → xs ∋ₜ at n (exhaust (T , t)) ▹ ys
            → ys ∋ₜ at m (is-type (unre T , tt)) ▹ zs
            → Process zs
            → Process xs
  recv-unre : ∀ {xs ys n T}
            → xs ∋ₜ at n (is-type (unre T , tt)) ▹ ys
            → ((t : ⟦ T ⟧ₜ) → Process ((T , t) ∷ ys))
            → Process xs

