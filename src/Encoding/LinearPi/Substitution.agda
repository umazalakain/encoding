open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem
open import LinearPi.Weakening

module LinearPi.Substitution where




reorient : ∀ {u} {xs ys zs as bs ps qs : ⟦ u ⟧ᵤ} → xs ≔ ys + zs → ys ≔ ps + qs → zs ≔ as + bs → Σ[ (ys' , zs') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] xs ≔ ys' + zs' × ys' ≔ ps + as × zs' ≔ qs + bs
reorient {linear} ℓ∅ ℓ∅ ℓ∅ = _ , ℓ∅ , ℓ∅ , ℓ∅
reorient {linear} ℓᵢ-left spl2 ℓ∅ = _ , spl2 , go-left , go-left
reorient {linear} ℓᵢ-right ℓ∅ spl3 = _ , spl3 , go-right , go-right
reorient {linear} ℓₒ-left spl2 ℓ∅ = _ , spl2 , go-left , go-left
reorient {linear} ℓₒ-right ℓ∅ spl3 = _ , spl3 , go-right , go-right
reorient {linear} ℓᵢₒ-left spl2 ℓ∅ = _ , spl2 , go-left , go-left
reorient {linear} ℓᵢₒ-right ℓ∅ spl3 = _ , spl3 , go-right , go-right
reorient {linear} ℓᵢₒ ℓᵢ-left ℓₒ-left = _ , ℓᵢₒ-left , ℓᵢₒ , ℓ∅
reorient {linear} ℓᵢₒ ℓᵢ-left ℓₒ-right = _ , ℓᵢₒ , ℓᵢ-left , ℓₒ-right
reorient {linear} ℓᵢₒ ℓᵢ-right ℓₒ-left = _ , ℓₒᵢ , ℓₒ-right , ℓᵢ-left
reorient {linear} ℓᵢₒ ℓᵢ-right ℓₒ-right = _ , ℓᵢₒ-right , ℓ∅ , ℓᵢₒ
reorient {linear} ℓₒᵢ ℓₒ-left ℓᵢ-left = _ , ℓᵢₒ-left , ℓₒᵢ , ℓ∅
reorient {linear} ℓₒᵢ ℓₒ-left ℓᵢ-right = _ , ℓₒᵢ , ℓₒ-left , ℓᵢ-right
reorient {linear} ℓₒᵢ ℓₒ-right ℓᵢ-left = _ , ℓᵢₒ , ℓᵢ-right , ℓₒ-left
reorient {linear} ℓₒᵢ ℓₒ-right ℓᵢ-right = _ , ℓᵢₒ-right , ℓ∅ , ℓₒᵢ
reorient {type} prod-left prod-left pure = _ , prod-left , prod-left , pure
reorient {type} prod-left prod-right pure = _ , prod-right , pure , prod-left
reorient {type} prod-right pure prod-left = _ , prod-left , prod-right , pure
reorient {type} prod-right pure prod-right = _ , prod-right , pure , prod-right
reorient {type} pure pure pure = _ , pure , pure , pure
reorient {type} unre unre unre = _ , unre , unre , unre
reorient {type} (line mid) (line left) (line right)
  with _ , mid' , left' , right' ← reorient mid left right
  = _ , line mid' , line left' , line right'
reorient {ctx} [] [] [] = _ , [] , [] , []
reorient {ctx} (x ∷ mid) (y ∷ left) (z ∷ right)
  with _ , x' , y' , z' ← reorient x y z
  with _ , mid' , left' , right' ← reorient mid left right
  = _ , x' ∷ mid' , y' ∷ left' , z' ∷ right'


data Occurs? : Ctx → TypedValue → TypedValue → Set₁ where
  yes : ∀ {xs x} → Null xs → Occurs? xs x x
  no  : ∀ {xs x y} → Null x → xs ∋ y → Occurs? xs x y

occurs? : ∀ {n t xs ys s} → InsertAt n t xs ys → ys ∋ s → Occurs? xs t s
occurs? here (here x) = yes x
occurs? here (there x ni) = no x ni
occurs? (there ins) (here x) =
  let t-null , xs-null = insert-null ins x in
  no t-null (here xs-null)
occurs? (there ins) (there x-null ni) with occurs? ins ni
... | yes xs-null = yes (x-null ∷ xs-null)
... | no t-null ni = no t-null (there x-null ni)


var-split : ∀ {xs x y z} → xs ∋ x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × ys ∋ y × zs ∋ z
var-split {_ ∷ xs} (here null) spl
  = _ , spl ∷ go-left , here null , here neutral-null
var-split {xs = x ∷ _} (there n vr) spl
  with _ , spl' , inl , inr ← var-split vr spl
  = _ , go-left ∷ spl' , there n inl , there neutral-null inr

term-split : ∀ {xs x y z} → Term xs x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × Term ys y × Term zs z
term-split (var x) spl
  with _ , spl1 , lvr , rvr ← var-split x spl
  = _ , spl1 , var lvr , var rvr
term-split {xs} (pure a x) pure
  = _ , null-unrestr x , pure a x , pure a x
term-split {xs} (pair spl1 lterm rterm) prod-left
  = _ , go-left , pair spl1 lterm rterm , pure tt neutral-null
term-split {xs} (pair spl1 lterm rterm) prod-right
  = _ , go-right , pure tt neutral-null , pair spl1 lterm rterm

redistribute : ∀ {orig left right n t elim enrich extra}
  → orig ≔ left + right
  → InsertAt n t elim orig
  → enrich ≔ extra + elim
  → Term extra t
  → Σ[ (as , bs , cs , ds , es , fs , a , b) ∈ Ctx × Ctx × Ctx × Ctx × Ctx × Ctx × TypedValue × TypedValue ]
    enrich ≔ as + bs
  × as ≔ cs + ds
  × bs ≔ es + fs
  × Term cs a
  × Term es b
  × InsertAt n a ds left
  × InsertAt n b fs right
redistribute orig ins enrich term
  with _ , tspl , cspl , insl , insr ← extract ins orig
  with _ , spl2 , lterm , rterm ← term-split term tspl
  with _ , spl' , lspl' , rspl' ← reorient enrich spl2 cspl
  = _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr

subst-var : ∀ {xs ys zs t n ws s}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → ws ∋ s
           → Term xs s
subst-var spl term ins ni with occurs? ins ni
... | yes zs-null rewrite +-cancel spl zs-null = term
... | no t-null zs∋s rewrite +-cancel (+-comm spl) (Null-Term t-null term) = var zs∋s

subst-term : ∀ {xs ys zs t n ws s}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → Term ws s
           → Term xs s
subst-term spl term ins (var x) = subst-var spl term ins x
subst-term spl term ins (pure a ws-null)
  with t-null , zs-null ← insert-null ins ws-null
  rewrite +-cancel spl zs-null
  = pure a (Null-Term t-null term)
subst-term spl term ins (pair spl1 l r)
  with _ , tspl , cspl , insl , insr ← extract ins spl1
  with _ , spl2 , lterm , rterm ← term-split term tspl
  with _ , spl' , lspl' , rspl' ← reorient spl spl2 cspl
  = pair spl' (subst-term lspl' lterm insl l) (subst-term rspl' rterm insr r)

subst-proc : ∀ {xs ys zs t n ws}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → Process ws
           → Process xs
subst-proc spl term ins (end ws-null)
  with t-null , zs-null ← insert-null ins ws-null
  rewrite +-cancel spl zs-null
  = end (Null-Term t-null term)
subst-proc spl term ins (par spl1 p q) 
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl1 ins spl term
  = par spl' (subst-proc lspl' lterm insl p) (subst-proc rspl' rterm insr q)
subst-proc spl term ins (new ∅ p) = new ∅ (subst-proc (line (go-right) ∷ spl) (Term-lift (line ℓ∅) term) (there ins) p)
subst-proc spl term ins (new (ᵢₒ t) p) = new (ᵢₒ t) (subst-proc (line (go-right) ∷ spl) (Term-lift (line ℓ∅) term) (there ins) p)
subst-proc spl term ins (new (unre t) p) = new (unre t) (subst-proc (unre ∷ spl) (Term-lift unre term) (there ins) p)
subst-proc spl term ins (rep ws-null p)
  with t-null , zs-null ← insert-null ins ws-null
  with refl ← +-cancel spl zs-null
  = rep (Null-Term t-null term) (subst-proc spl term ins p)
subst-proc spl term ins (send-line {ms} {ls} {rs} spl-payload payload spl-channel channel p)
  with _ , spl-payload2 , lspl-term , spl-rest2 , term-l , term-rest , ins-payload , ins-rest ← redistribute spl-payload ins spl term
  with _ , spl-channel2 , spl-term-chan , spl-term-cont , term-channel , term-cont , ins-channel , ins-cont ← redistribute spl-channel ins-rest spl-rest2 term-rest
  = send-line spl-payload2 (subst-term lspl-term term-l ins-payload payload)
  spl-channel2 (subst-term spl-term-chan term-channel ins-channel channel)
  (subst-proc spl-term-cont term-cont ins-cont p)
subst-proc spl term ins (send-unre {ms} {ls} {rs} spl-payload payload spl-channel channel p)
  with _ , spl-payload2 , lspl-term , spl-rest2 , term-l , term-rest , ins-payload , ins-rest ← redistribute spl-payload ins spl term
  with _ , spl-channel2 , spl-term-chan , spl-term-cont , term-channel , term-cont , ins-channel , ins-cont ← redistribute spl-channel ins-rest spl-rest2 term-rest
  = send-unre spl-payload2 (subst-term lspl-term term-l ins-payload payload)
  spl-channel2 (subst-term spl-term-chan term-channel ins-channel channel)
  (subst-proc spl-term-cont term-cont ins-cont p)
subst-proc spl term ins (recv-line {T = T} spl-channel channel cont)
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-channel ins spl term
  = recv-line spl' (subst-term lspl' lterm insl channel) λ t →
    subst-proc (go-right ∷ rspl') (Term-lift neutral-null rterm) (there insr) (cont t)
subst-proc spl term ins (recv-unre {T = T} spl-channel channel cont)
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-channel ins spl term
  = recv-unre spl' (subst-term lspl' lterm insl channel) λ t →
    subst-proc (go-right ∷ rspl') (Term-lift neutral-null rterm) (there insr) (cont t)
subst-proc spl term ins (letprod {A = A} {B} {a} {b} spl-prod prd p)
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-prod ins spl term
  = letprod spl' (subst-term lspl' lterm insl prd)
  (subst-proc (go-right ∷ go-right ∷ rspl') (Term-lift neutral-null (Term-lift neutral-null rterm)) (there (there insr)) p)
