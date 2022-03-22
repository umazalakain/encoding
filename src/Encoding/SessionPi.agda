open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

mutual
  data Type : Set₁ where
    pure : Set → Type
    sesh : Session → Type
    chan : Type → Type

  data Session : Set₁ where
    end : Session
    recv : (T : Type) → (⟦ T ⟧ₜ → Session) → Session
    send : (T : Type) → (⟦ T ⟧ₜ → Session) → Session
    cont : (T : Type) → (⟦ T ⟧ₜ → Session) → Session

  ⟦_⟧ₜ : Type → Set
  ⟦ pure A ⟧ₜ = A
  ⟦ sesh _ ⟧ₜ = ⊤
  ⟦ chan _ ⟧ₜ = ⊤

dual : Session → Session
dual end = end
dual (recv T C) = send T (dual ∘ C)
dual (send T C) = recv T (dual ∘ C)
dual (cont T C) = cont T C


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
  pure : ∀ {A a} → (pure A , a) ≔ (pure A , a) + (pure A , a)
  chan : ∀ {x} → (chan x , tt) ≔ (chan x , tt) + (chan x , tt)
  sesh-left : {S : Session} → (sesh S , tt) ≔ (sesh S , tt) + (sesh end , tt)
  sesh-right : {S : Session} → (sesh S , tt) ≔ (sesh end , tt) + (sesh S , tt)

  [] : _≔_+_ {ctx} [] [] []
  _∷_ : {x y z : TypedValue} {xs ys zs : Ctx}
      → x ≔ y + z
      → xs ≔ ys + zs
      → (x ∷ xs) ≔ (y ∷ ys) + (z ∷ zs)


data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  pure : ∀ {A a} → Null (pure A , a)
  chan : ∀ {x} → Null (chan x , tt)
  sesh-end : Null (sesh end , tt)
  [] : Null {ctx} []
  _∷_ : {x : TypedValue} {xs : Ctx} → Null x → Null xs → Null {ctx} (x ∷ xs)


data Action : Set₁ where
  at : ℕ → Action → Action
  recv send payload : (T : Type) (t : ⟦ T ⟧ₜ) → Action


data _∋ₜ_▹_ : ∀ {u} → ⟦ u ⟧ᵤ → Action → ⟦ u ⟧ᵤ → Set₁ where
  recv-sesh : ∀ {T t} {C : ⟦ T ⟧ₜ → Session} → (sesh (recv T C) , tt) ∋ₜ recv T t ▹ (sesh (C t) , tt)
  send-sesh : ∀ {T t} {C : ⟦ T ⟧ₜ → Session} → (sesh (send T C) , tt) ∋ₜ send T t ▹ (sesh (C t) , tt)
  recv-chan : ∀ {T t} → (chan T , tt) ∋ₜ recv T t ▹ (chan T , tt)
  send-chan : ∀ {T t} → (chan T , tt) ∋ₜ send T t ▹ (chan T , tt)

  payload-pure : ∀ A a → (pure A , a) ∋ₜ payload (pure A) a ▹ (pure A , a)
  payload-sesh : ∀ {x} → (sesh x , tt) ∋ₜ payload (sesh x) tt ▹ (sesh end , tt)
  payload-chan : ∀ {x} → (chan x , tt) ∋ₜ payload (chan x) tt ▹ (chan x , tt)

  here : ∀ {x xs α x'}
       → _∋ₜ_▹_ {type} x α x'
       → _∋ₜ_▹_ {ctx} (x ∷ xs) (at zero α) (x' ∷ xs)
  there : ∀ {x' xs xs' n α}
        → _∋ₜ_▹_ {ctx} xs (at n α) xs'
        → _∋ₜ_▹_ {ctx} (x' ∷ xs) (at (suc n) α) (x' ∷ xs')


data New : TypedValue → TypedValue → Set where
  chan : ∀ t → New (chan t , tt) (chan t , tt)
  sesh : ∀ s → New (sesh s , tt) (sesh (dual s) , tt)


data Process : Ctx → Set₁ where
  end : ∀ {xs} → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ≔ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {xs} {S T}
      → New S T
      → Process (S ∷ T ∷ xs)
      → Process xs
  rep : ∀ {xs} → Null xs → Process xs → Process xs
  send : ∀ {xs n ys m zs ws T t}
       → xs ∋ₜ at n (payload T t) ▹ ys
       → ys ∋ₜ at m (send T t) ▹ zs
       → Process ws
       → Process xs
  recv : ∀ {xs ys T}
       → (n : ℕ)
       → ((t : ⟦ T ⟧ₜ) → xs ∋ₜ at n (recv T t) ▹ ys × Process ((T , t) ∷ ys))
       → Process xs
