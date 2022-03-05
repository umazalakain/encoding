open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem
open import LinearPi.Weakening

module LinearPi.Substitution where



⊆-var : ∀ {s t xs} → s ⊆ t → xs ∋ t → xs ∋ s
⊆-var sub (here x x₁) = here x (⊆-trans sub x₁)
⊆-var sub (there x vr) = there x (⊆-var sub vr)

⊆-term : ∀ {s t xs} → s ⊆ t → Term xs t → Term xs s
⊆-term sub (var x) = var (⊆-var sub x)
⊆-term pure (pure a x) = pure a x
⊆-term prod (pair spl l r) = pair spl (⊆-term (⊆-refl _) l) (⊆-term (⊆-refl _) r)

reorient : ∀ {u} {xs ys zs as bs ps qs : ⟦ u ⟧ᵤ} → xs ≔ ys + zs → ys ≔ ps + qs → zs ≔ as + bs → Σ[ (ys' , zs') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] xs ≔ ys' + zs' × ys' ≔ ps + as × zs' ≔ qs + bs
reorient {usage} #0 #0 #0 = _ , #0 , #0 , #0
reorient {usage} #1-left #1-left #0 = _ , #1-left , #1-left , #0
reorient {usage} #1-left #1-right #0 = _ , #1-right , #0 , #1-left
reorient {usage} #1-right #0 #1-left = _ , #1-left , #1-right , #0
reorient {usage} #1-right #0 #1-right = _ , #1-right , #0 , #1-right
reorient {usage} #ω #ω #ω = _ , #ω , #ω , #ω
reorient {type} prod-left prod-left pure = _ , prod-left , prod-left , pure
reorient {type} prod-left prod-right pure = _ , prod-right , pure , prod-left
reorient {type} prod-right pure prod-left = _ , prod-left , prod-right , pure
reorient {type} prod-right pure prod-right = _ , prod-right , pure , prod-right
reorient {type} pure pure pure = _ , pure , pure , pure
reorient {type} (chan imid omid) (chan ileft oleft) (chan iright oright)
  with _ , imid' , ileft' , iright' ← reorient imid ileft iright
  with _ , omid' , oleft' , oright' ← reorient omid oleft oright
  = _ , chan imid' omid' , chan ileft' oleft' , chan iright' oright'
reorient {ctx} [] [] [] = _ , [] , [] , []
reorient {ctx} (x ∷ mid) (y ∷ left) (z ∷ right)
  with _ , x' , y' , z' ← reorient x y z
  with _ , mid' , left' , right' ← reorient mid left right
  = _ , x' ∷ mid' , y' ∷ left' , z' ∷ right'

data Occurs? : Ctx → TypedValue → TypedValue → Set₁ where
  yes : ∀ {xs x y} → Null xs → y ⊆ x → Occurs? xs x y
  no  : ∀ {xs x y} → Null x → xs ∋ y → Occurs? xs x y

occurs? : ∀ {n t xs ys s} → InsertAt n t xs ys → ys ∋ s → Occurs? xs t s
occurs? here (here x sub) = yes x sub
occurs? here (there x ni) = no x ni
occurs? (there ins) (here x sub) =
  let t-null , xs-null = insert-null ins x in
  no t-null (here xs-null sub)
occurs? (there ins) (there x-null ni) with occurs? ins ni
... | yes xs-null sub = yes (x-null ∷ xs-null) sub
... | no t-null ni = no t-null (there x-null ni)

⊆-split : ∀ {u} {x y z x' : ⟦ u ⟧ᵤ} → x ≔ y + z → x ⊆ x' → Σ[ (y' , z') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] x' ≔ y' + z' × y ⊆ y' × z ⊆ z'
⊆-split {x' = x'} #0 sub = let _ , fill , fillnull = +-idʳ x' in _ , fill , sub , Null-#0⊆ fillnull
⊆-split {x' = x'} #1-left sub = let _ , fill , fillnull = +-idʳ x' in _ , fill , sub , Null-#0⊆ fillnull
⊆-split {x' = x'} #1-right sub = let _ , fill , fillnull = +-idˡ x' in _ , fill , Null-#0⊆ fillnull , sub
⊆-split prod-left prod = _ , prod-left , ⊆-refl _ , ⊆-refl _
⊆-split prod-right prod = _ , prod-right , ⊆-refl _ , ⊆-refl _
⊆-split #ω #ω = _ , #ω , #ω , #ω
⊆-split pure pure = _ , pure , pure , pure
⊆-split [] [] = _ , [] , [] , []
⊆-split (chan i o) (chan isub osub eq) =
  let _ , ispl , isubl , isubr = ⊆-split i isub in
  let _ , ospl , osubl , osubr = ⊆-split o osub in
  _ , chan ispl ospl , chan isubl osubl eq , chan isubr osubr eq
⊆-split (spl ∷ spls) (sub ∷ subs) =
  let _ , spl' , subl' , subr' = ⊆-split spl sub in
  let _ , spls' , subls' , subrs' = ⊆-split spls subs in
  _ , spl' ∷ spls' , subl' ∷ subls' , subr' ∷ subrs'

var-split : ∀ {xs x y z} → xs ∋ x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × ys ∋ y × zs ∋ z
var-split {_ ∷ xs} (here null lt) spl
  with _ , fill , fillnull ← +-idʳ xs
  with _ , spl1 , subl , subr ← ⊆-split spl lt
  = _ , spl1 ∷ fill , here null subl , here fillnull subr
var-split {xs = x ∷ _} (there n vr) spl
  with _ , fill , fillnull ← +-idʳ x
  with _ , spl' , inl , inr ← var-split vr spl
  = _ , fill ∷ spl' , there n inl , there fillnull inr

term-split : ∀ {xs x y z} → Term xs x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × Term ys y × Term zs z
term-split (var x) spl
  with _ , spl1 , lvr , rvr ← var-split x spl
  = _ , spl1 , var lvr , var rvr
term-split {xs} (pure a x) pure
  with _ , fill , fillnull ← +-idʳ xs
  = _ , null-unrestr x , pure a x , pure a x
term-split {xs} (pair spl1 lterm rterm) prod-left
  with _ , fill , fillnull ← +-idʳ xs
  = _ , fill , pair spl1 lterm rterm , pure tt fillnull
term-split {xs} (pair spl1 lterm rterm) prod-right
  with _ , fill , fillnull ← +-idˡ xs
  = _ , fill , pure tt fillnull , pair spl1 lterm rterm

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
... | yes zs-null s⊆t rewrite +-cancel spl zs-null = ⊆-term s⊆t term
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
subst-proc spl term ins (new i o t p)
  with _ , ispl , inull ← +-idˡ i
  with _ , ospl , onull ← +-idˡ o
  = new i o t (subst-proc (chan ispl ospl ∷ spl) (Term-lift (chan inull onull) term) (there ins) p)
subst-proc spl term ins (rep ws-null p)
  with t-null , zs-null ← insert-null ins ws-null
  with refl ← +-cancel spl zs-null
  = rep (Null-Term t-null term) (subst-proc spl term ins p)
subst-proc spl term ins (send {ms} {ls} {rs} spl-payload payload spl-channel channel p)
  with _ , spl-payload2 , lspl-term , spl-rest2 , term-l , term-rest , ins-payload , ins-rest ← redistribute spl-payload ins spl term
  with _ , spl-channel2 , spl-term-chan , spl-term-cont , term-channel , term-cont , ins-channel , ins-cont ← redistribute spl-channel ins-rest spl-rest2 term-rest
  = send spl-payload2 (subst-term lspl-term term-l ins-payload payload)
  spl-channel2 (subst-term spl-term-chan term-channel ins-channel channel)
  (subst-proc spl-term-cont term-cont ins-cont p)
subst-proc spl term ins (recv {T = T} spl-channel channel cont)
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-channel ins spl term
  = recv spl' (subst-term lspl' lterm insl channel) λ t →
    let _ , tright , tfill = +-idˡ (T , t)
    in subst-proc (tright ∷ rspl') (Term-lift tfill rterm) (there insr) (cont t)
subst-proc spl term ins (letprod {A = A} {B} {a} {b} spl-prod prd p)
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-prod ins spl term
  with _ , aright , afill ← +-idˡ (A , a)
  with _ , bright , bfill ← +-idˡ (B a , b)
  = letprod spl' (subst-term lspl' lterm insl prd)
  (subst-proc (aright ∷ bright ∷ rspl') (Term-lift afill (Term-lift bfill rterm)) (there (there insr)) p)
