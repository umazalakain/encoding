
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem

module LinearPi.Weakening where


+-comm : ∀ {u} {x y z : ⟦ u ⟧ᵤ} → x ≔ y + z → x ≔ z + y
+-comm {chan} ℓ∅ = ℓ∅
+-comm {chan} # = #
+-comm {chan} ℓᵢ-left = ℓᵢ-right
+-comm {chan} ℓᵢ-right = ℓᵢ-left
+-comm {chan} ℓₒ-left = ℓₒ-right
+-comm {chan} ℓₒ-right = ℓₒ-left
+-comm {chan} ℓᵢₒ-left = ℓᵢₒ-right
+-comm {chan} ℓᵢₒ-right = ℓᵢₒ-left
+-comm {chan} ℓᵢₒ = ℓₒᵢ
+-comm {chan} ℓₒᵢ = ℓᵢₒ
+-comm {type} pure = pure
+-comm {type} (chan x) = chan (+-comm x)
+-comm {type} prod-left = prod-right
+-comm {type} prod-right = prod-left
+-comm {ctx} [] = []
+-comm {ctx} (x ∷ xs) = +-comm x ∷ +-comm xs

neutral : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ
neutral {chan} ℓ∅ = ℓ∅
neutral {chan} (ℓᵢ x) = ℓ∅
neutral {chan} (ℓₒ x) = ℓ∅
neutral {chan} (ℓᵢₒ x) = ℓ∅
neutral {chan} (# x) = # x
neutral {type} (pure A , a) = pure A , a
neutral {type} (prod _ _ , _) = pure ⊤ , tt
neutral {type} (chan x , _) = chan (neutral x) , _
neutral {ctx} [] = []
neutral {ctx} (x ∷ xs) = neutral x ∷ neutral xs

neutral-idempotent : ∀ {u} (x : ⟦ u ⟧ᵤ) → neutral (neutral x) ≡ neutral x
neutral-idempotent {chan} ℓ∅ = refl
neutral-idempotent {chan} (ℓᵢ x) = refl
neutral-idempotent {chan} (ℓₒ x) = refl
neutral-idempotent {chan} (ℓᵢₒ x) = refl
neutral-idempotent {chan} (# x) = refl
neutral-idempotent {type} (pure _ , _) = refl
neutral-idempotent {type} (prod _ _ , _) = refl
neutral-idempotent {type} (chan x , _) = cong (λ ● → chan ● , tt) (neutral-idempotent x)
neutral-idempotent {ctx} [] = refl
neutral-idempotent {ctx} (x ∷ xs) = cong₂ _∷_ (neutral-idempotent x) (neutral-idempotent xs)

neutral-null : ∀ {u} (x : ⟦ u ⟧ᵤ) → Null (neutral x)
neutral-null {chan} ℓ∅ = ℓ∅
neutral-null {chan} (ℓᵢ x) = ℓ∅
neutral-null {chan} (ℓₒ x) = ℓ∅
neutral-null {chan} (ℓᵢₒ x) = ℓ∅
neutral-null {chan} (# x) = #
neutral-null {type} (pure _ , _) = pure
neutral-null {type} (prod _ _ , _) = pure
neutral-null {type} (chan x , _) = chan (neutral-null x)
neutral-null {ctx} [] = []
neutral-null {ctx} (x ∷ xs) = neutral-null x ∷ neutral-null xs


+-idˡ : ∀ {u} (x : ⟦ u ⟧ᵤ) → x ≔ neutral x + x
+-idˡ {chan} ℓ∅ = ℓ∅
+-idˡ {chan} (# x) = #
+-idˡ {chan} (ℓᵢ x) = ℓᵢ-right
+-idˡ {chan} (ℓₒ x) = ℓₒ-right
+-idˡ {chan} (ℓᵢₒ x) = ℓᵢₒ-right
+-idˡ {type} (pure _ , _) = pure
+-idˡ {type} (prod _ _ , _) = prod-right
+-idˡ {type} (chan x , _) = chan (+-idˡ x)
+-idˡ {ctx} [] = []
+-idˡ {ctx} (x ∷ xs) = +-idˡ x ∷ +-idˡ xs


+-idʳ : ∀ {u} (x : ⟦ u ⟧ᵤ) → x ≔ x + neutral x
+-idʳ x = +-comm (+-idˡ x)

+-cancel : ∀ {u} {a b c : ⟦ u ⟧ᵤ} → a ≔ b + c → Null c → a ≡ b
+-cancel ℓ∅ null = refl
+-cancel # null = refl
+-cancel ℓᵢ-left null = refl
+-cancel ℓₒ-left null = refl
+-cancel ℓᵢₒ-left null = refl
+-cancel prod-left null = refl
+-cancel pure null = refl
+-cancel [] null = refl
+-cancel (chan x) (chan null) = cong (λ ● → chan ● , tt) (+-cancel x null)
+-cancel (spl ∷ spls) (null ∷ nulls) = cong₂ _∷_ (+-cancel spl null) (+-cancel spls nulls)

⊇-refl : ∀ {u} (x : ⟦ u ⟧ᵤ) → x ⊇ x
⊇-refl {chan} ℓ∅ = ∅
⊇-refl {chan} (ℓᵢ x) = ᵢ
⊇-refl {chan} (ℓₒ x) = ₒ
⊇-refl {chan} (ℓᵢₒ x) = ᵢₒ
⊇-refl {chan} (# x) = ##
⊇-refl {type} (pure x , _) = pure
⊇-refl {type} (prod L R , (l , r)) = prod (⊇-refl (L , l)) (⊇-refl (R l , r))
⊇-refl {type} (chan x , _) = chan (⊇-refl x)
⊇-refl {ctx} [] = []
⊇-refl {ctx} (x ∷ xs) = ⊇-refl x ∷ ⊇-refl xs

null-unrestr : ∀ {u} {xs : ⟦ u ⟧ᵤ} → Null xs → xs ≔ xs + xs
null-unrestr {xs = xs} null
  rewrite +-cancel (+-idˡ xs) null
  with spl ← +-idˡ (neutral xs)
  rewrite neutral-idempotent xs = spl

Null-∋ : ∀ {t xs} → Null t → xs ∋ t → Null xs
Null-∋ n (here n') = n ∷ n'
Null-∋ n (there n' x) = n' ∷ Null-∋ n x

Null-Term : ∀ {t xs} → Null t → Term xs t → Null xs
Null-Term n (var x) = Null-∋ n x
Null-Term n (pure _ x) = x

data InsertAt : ℕ → TypedValue → Ctx → Ctx → Set₁ where
  here : ∀ {x xs} → InsertAt zero x xs (x ∷ xs)
  there : ∀ {n x xs ys x'} → InsertAt n x xs ys → InsertAt (suc n) x (x' ∷ xs) (x' ∷ ys)

null-insert : ∀ {n x xs ys} → InsertAt n x xs ys → Null x → Null xs → Null ys
null-insert here nx nxs = nx ∷ nxs
null-insert (there ins) nx (nx' ∷ nxs) = nx' ∷ null-insert ins nx nxs

insert-null : ∀ {n t xs ys} → InsertAt n t xs ys → Null ys → Null t × Null xs
insert-null here (t-null ∷ xs-null) = t-null , xs-null
insert-null (there ins) (x-null ∷ xs-null) = Product.map₂ (x-null ∷_) (insert-null ins xs-null)

insert-⊇ : ∀ {n t xs ys xs'} → InsertAt n t xs ys → xs ⊇ xs' → Σ[ ys' ∈ Ctx ] InsertAt n t xs' ys' × ys ⊇ ys'
insert-⊇ here sup = _ , here , ⊇-refl _ ∷ sup
insert-⊇ (there ins) (sup ∷ sups) =
  let _ , ins' , sup' = insert-⊇ ins sups in _ , there ins' , sup ∷ sup'

extract : ∀ {n t zs ms ls rs} → InsertAt n t zs ms → ms ≔ ls + rs → Σ[ (x , y , xs , ys) ∈ (TypedValue × TypedValue × Ctx × Ctx) ] t ≔ x + y × zs ≔ xs + ys × InsertAt n x xs ls × InsertAt n y ys rs
extract here (spl ∷ spls) = _ , spl , spls , here , here
extract (there ins) (spl ∷ spls) =
  let _ , spl' , spls' , insl , insr = extract ins spls in
  _ , spl' , spl ∷ spls' , there insl , there insr

imtract : ∀ {xs ys zs x y z n ms} → xs ≔ ys + zs → x ≔ y + z → InsertAt n x xs ms → Σ[ (ls , rs) ∈ Ctx × Ctx ] ms ≔ ls + rs × InsertAt n y ys ls × InsertAt n z zs rs
imtract spl spl1 here = _ , spl1 ∷ spl , here , here
imtract (spl ∷ spls) spl1 (there ins) =
  let _ , spl2 , insl , insr = imtract spls spl1 ins in
  _ , spl ∷ spl2 , there insl , there insr

Var-null-insert : ∀ {x n xs ys t} → Null x → InsertAt n x xs ys → xs ∋ t → ys ∋ t
Var-null-insert null here vr = there null vr
Var-null-insert null (there ins) (here null') = here (null-insert ins null null')
Var-null-insert null (there ins) (there null' vr) = there null' (Var-null-insert null ins vr)

Term-null-insert : ∀ {x n xs ys t} → Null x → InsertAt n x xs ys → Term xs t → Term ys t
Term-null-insert null ins (var x) = var (Var-null-insert null ins x)
Term-null-insert null ins (pure a x) = pure a (null-insert ins null x)
Term-null-insert {x} null ins (pair (spl , sub) l r)
  with _ , ins' , sub' ← insert-⊇ ins sub
  with _ , spl1 , insl , insr ← imtract spl (+-idˡ x) ins'
  = pair (spl1 , sub') (Term-null-insert (neutral-null x) insl l) (Term-null-insert null insr r)

Process-null-insert : ∀ {x n xs ys} → Null x → InsertAt n x xs ys → Process xs → Process ys
Process-null-insert null ins (end x) = end (null-insert ins null x)
Process-null-insert {x} null ins (par (spl , sub) p q)
  with _ , ins' , sub' ← insert-⊇ ins sub
  with _ , spl1 , insl , insr ← imtract spl (+-idˡ x) ins'
  = par (spl1 , sub') (Process-null-insert (neutral-null x) insl p) (Process-null-insert null insr q)
Process-null-insert null ins (new x proc) = new x (Process-null-insert null (there ins) proc)
Process-null-insert null ins (rep x proc) = rep (null-insert ins null x) (Process-null-insert null ins proc)
Process-null-insert {x} null ins (send (spl-payload , sub-payload) payload (spl-channel , sub-channel) channel proc)
  with _ , ins' , sub-payload' ← insert-⊇ ins sub-payload
  with _ , spl1 , insl , insr ← imtract spl-payload (+-idˡ x) ins'
  with _ , insr' , sub-channel' ← insert-⊇ insr sub-channel
  with _ , spl2 , insrl , insrr ← imtract spl-channel (+-idˡ x) insr'
  = send
    (spl1 , sub-payload') (Term-null-insert (neutral-null x) insl payload)
    (spl2 , sub-channel') (Term-null-insert (neutral-null x) insrl channel)
    (Process-null-insert null insrr proc)
Process-null-insert {x} null ins (recv (spl-channel , sub-channel) channel cont)
  with _ , ins' , sub-channel' ← insert-⊇ ins sub-channel
  with _ , spl1 , insl , insr ← imtract spl-channel (+-idˡ x) ins'
  = recv (spl1 , sub-channel') (Term-null-insert (neutral-null x) insl channel) (Process-null-insert null (there insr) ∘ cont)
Process-null-insert {x} null ins (letprod (spl-prd , sub-prd) prd proc)
  with _ , ins' , sub-prd' ← insert-⊇ ins sub-prd
  with _ , spl1 , insl , insr ← imtract spl-prd (+-idˡ x) ins'
  = letprod (spl1 , sub-prd') (Term-null-insert (neutral-null x) insl prd) (Process-null-insert null (there (there insr)) proc)


Term-lift : ∀ {x xs t} → Null x → Term xs t → Term (x ∷ xs) t
Term-lift null = Term-null-insert null here

Process-lift : ∀ {x xs} → Null x → Process xs → Process (x ∷ xs)
Process-lift null = Process-null-insert null here
