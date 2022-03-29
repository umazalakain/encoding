
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem

module LinearPi.Weakening where


+-comm : ∀ {u} {x y z : ⟦ u ⟧ᵤ} → x ≔ y + z → x ≔ z + y
+-comm {linear} ℓ∅ = ℓ∅
+-comm {linear} ℓᵢ-left = ℓᵢ-right
+-comm {linear} ℓᵢ-right = ℓᵢ-left
+-comm {linear} ℓₒ-left = ℓₒ-right
+-comm {linear} ℓₒ-right = ℓₒ-left
+-comm {linear} ℓᵢₒ-left = ℓᵢₒ-right
+-comm {linear} ℓᵢₒ-right = ℓᵢₒ-left
+-comm {linear} ℓᵢₒ = ℓₒᵢ
+-comm {linear} ℓₒᵢ = ℓᵢₒ
+-comm {type} pure = pure
+-comm {type} (line x) = line (+-comm x)
+-comm {type} unre = unre
+-comm {type} prod-left = prod-right
+-comm {type} prod-right = prod-left
+-comm {ctx} [] = []
+-comm {ctx} (x ∷ xs) = +-comm x ∷ +-comm xs

neutral : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ
neutral {linear} x = ℓ∅
neutral {type} (unre x , _) = unre x , tt
neutral {type} (pure A , a) = pure A , a
neutral {type} (prod _ _ , _) = pure ⊤ , tt
neutral {type} (line x , _) = line (neutral x) , _
neutral {ctx} [] = []
neutral {ctx} (x ∷ xs) = neutral x ∷ neutral xs

neutral-idempotent : ∀ {u} (x : ⟦ u ⟧ᵤ) → neutral (neutral x) ≡ neutral x
neutral-idempotent {linear} x = refl
neutral-idempotent {type} (unre x , _) = refl
neutral-idempotent {type} (pure _ , _) = refl
neutral-idempotent {type} (prod _ _ , _) = refl
neutral-idempotent {type} (line x , _) = refl
neutral-idempotent {ctx} [] = refl
neutral-idempotent {ctx} (x ∷ xs) = cong₂ _∷_ (neutral-idempotent x) (neutral-idempotent xs)

neutral-null : ∀ {u} {x : ⟦ u ⟧ᵤ} → Null (neutral x)
neutral-null {linear} = ℓ∅
neutral-null {type} {unre _ , tt} = unre
neutral-null {type} {pure _ , _} = pure
neutral-null {type} {prod _ _ , _} = pure
neutral-null {type} {line x , _} = line (neutral-null {linear} {x})
neutral-null {ctx} {[]} = []
neutral-null {ctx} {x ∷ xs} = neutral-null ∷ neutral-null


go-right : ∀ {u} {x : ⟦ u ⟧ᵤ} → x ≔ neutral x + x
go-right {linear} {ℓ∅} = ℓ∅
go-right {linear} {ℓᵢ x} = ℓᵢ-right
go-right {linear} {ℓₒ x} = ℓₒ-right
go-right {linear} {ℓᵢₒ x} = ℓᵢₒ-right
go-right {type} {unre x , _} = unre
go-right {type} {pure _ , _} = pure
go-right {type} {prod _ _ , _} = prod-right
go-right {type} {line x , _} = line go-right
go-right {ctx} {[]} = []
go-right {ctx} {x ∷ xs} = go-right ∷ go-right


go-left : ∀ {u} {x : ⟦ u ⟧ᵤ} → x ≔ x + neutral x
go-left = +-comm go-right

+-cancel : ∀ {u} {a b c : ⟦ u ⟧ᵤ} → a ≔ b + c → Null c → a ≡ b
+-cancel ℓ∅ null = refl
+-cancel ℓᵢ-left null = refl
+-cancel ℓₒ-left null = refl
+-cancel ℓᵢₒ-left null = refl
+-cancel prod-left null = refl
+-cancel pure null = refl
+-cancel [] null = refl
+-cancel (line x) (line null) = cong (λ ● → line ● , tt) (+-cancel x null)
+-cancel unre null = refl
+-cancel (spl ∷ spls) (null ∷ nulls) = cong₂ _∷_ (+-cancel spl null) (+-cancel spls nulls)

null-unrestr : ∀ {u} {xs : ⟦ u ⟧ᵤ} → Null xs → xs ≔ xs + xs
null-unrestr {xs = xs} null
  rewrite +-cancel (go-right {x = xs}) null
  with spl ← go-right {x = neutral xs}
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
Term-null-insert {x} null ins (pair spl l r)
  with _ , spl1 , insl , insr ← imtract spl go-right ins
  = pair spl1 (Term-null-insert neutral-null insl l) (Term-null-insert null insr r)

Process-null-insert : ∀ {x n xs ys} → Null x → InsertAt n x xs ys → Process xs → Process ys
Process-null-insert null ins (end x) = end (null-insert ins null x)
Process-null-insert {x} null ins (par spl p q)
  with _ , spl1 , insl , insr ← imtract spl go-right ins
  = par spl1  (Process-null-insert neutral-null insl p) (Process-null-insert null insr q)
Process-null-insert null ins (new x proc) = new x (Process-null-insert null (there ins) proc)
Process-null-insert null ins (rep x proc) = rep (null-insert ins null x) (Process-null-insert null ins proc)
Process-null-insert {x} null ins (send-unre spl-payload payload spl-channel channel proc)
  with _ , spl1 , insl , insr ← imtract spl-payload go-right ins
  with _ , spl2 , insrl , insrr ← imtract spl-channel go-right insr
  = send-unre spl1 (Term-null-insert neutral-null insl payload) spl2 (Term-null-insert neutral-null insrl channel) (Process-null-insert null insrr proc)
Process-null-insert {x} null ins (send-line spl-payload payload spl-channel channel proc)
  with _ , spl1 , insl , insr ← imtract spl-payload go-right ins
  with _ , spl2 , insrl , insrr ← imtract spl-channel go-right insr
  = send-line spl1 (Term-null-insert neutral-null insl payload) spl2 (Term-null-insert neutral-null insrl channel) (Process-null-insert null insrr proc)
Process-null-insert {x} null ins (recv-line spl-channel channel cont)
  with _ , spl1 , insl , insr ← imtract spl-channel go-right ins
  = recv-line spl1 (Term-null-insert neutral-null insl channel) (Process-null-insert null (there insr) ∘ cont)
Process-null-insert {x} null ins (recv-unre spl-channel channel cont)
  with _ , spl1 , insl , insr ← imtract spl-channel go-right ins
  = recv-unre spl1 (Term-null-insert neutral-null insl channel) (Process-null-insert null (there insr) ∘ cont)
Process-null-insert {x} null ins (letprod spl-prd prd proc)
  with _ , spl1 , insl , insr ← imtract spl-prd go-right ins
  = letprod spl1 (Term-null-insert neutral-null insl prd) (Process-null-insert null (there (there insr)) proc)


Term-lift : ∀ {x xs t} → Null x → Term xs t → Term (x ∷ xs) t
Term-lift null = Term-null-insert null here

Process-lift : ∀ {x xs} → Null x → Process xs → Process (x ∷ xs)
Process-lift null = Process-null-insert null here
