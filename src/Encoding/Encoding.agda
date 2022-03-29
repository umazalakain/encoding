import Level
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)
open import Function using (_∘_; _$_; _|>_)
open import Function.Reasoning using (∋-syntax)

open import Data.Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Base as List

import SessionPi as S

module Encoding where

module L where
  open import LinearPi.TypeSystem public
  open import LinearPi.Weakening public
  open import LinearPi.Substitution public
  open import LinearPi.Exchange public


postulate EXTENSIONALITY : Extensionality Level.zero (Level.suc Level.zero)

infix 4 !_
pattern !_ x = _ , x


flip-chan : L.Linear → L.Linear
flip-chan L.ℓ∅ = L.ℓ∅
flip-chan (L.ℓᵢ x) = L.ℓₒ x
flip-chan (L.ℓₒ x) = L.ℓᵢ x
flip-chan (L.ℓᵢₒ x) = L.ℓᵢₒ x

mutual
  ⟦_⟧ₑ-type : S.Type → L.Type
  ⟦ S.pure x ⟧ₑ-type = L.pure x
  ⟦ S.sesh x ⟧ₑ-type = L.line ⟦ x ⟧ₑ-session
  ⟦ S.unre x ⟧ₑ-type = L.unre ⟦ x ⟧ₑ-type

  ⟦_⟧ₑ-session : S.Session → L.Linear
  ⟦ S.end ⟧ₑ-session = L.ℓ∅
  ⟦ S.send T C ⟧ₑ-session = L.ℓₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C))
  ⟦ S.recv T C ⟧ₑ-session = L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C))

  ⟦_⟧ₑ-typedvalue : S.TypedValue → L.TypedValue
  ⟦ T , t ⟧ₑ-typedvalue = ⟦ T ⟧ₑ-type , (encode T t)

  ⟦_⟧ₑ-ctx : S.Ctx → L.Ctx
  ⟦_⟧ₑ-ctx = List.map ⟦_⟧ₑ-typedvalue

  decode : ∀ T → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → S.⟦ T ⟧ₜ
  decode (S.pure A) x = x
  decode (S.sesh _) _ = tt
  decode (S.unre _) _ = tt

  encode : ∀ T → S.⟦ T ⟧ₜ → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ
  encode (S.pure A) x = x
  encode (S.sesh _) _ = tt
  encode (S.unre _) _ = tt

  encode-cont : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont T C = L.line ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

  encode-cont-flip : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont-flip T C = L.line ∘ flip-chan ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

decode-encode : ∀ T {t} → decode T (encode T t) ≡ t
decode-encode (S.pure x) = refl
decode-encode (S.sesh x) = refl
decode-encode (S.unre x) = refl

encode-decode : ∀ T {t} → encode T (decode T t) ≡ t
encode-decode (S.pure x) = refl
encode-decode (S.sesh x) = refl
encode-decode (S.unre x) = refl

⟦_⟧-null-typedvalue : ∀ {x} → S.Null x → L.Null ⟦ x ⟧ₑ-typedvalue
⟦ S.pure ⟧-null-typedvalue = L.pure
⟦ S.sesh S.end ⟧-null-typedvalue = L.line L.ℓ∅
⟦ S.unre ⟧-null-typedvalue = L.unre

⟦_⟧-null : ∀ {xs : S.Ctx} → S.Null xs → L.Null ⟦ xs ⟧ₑ-ctx
⟦ S.[] ⟧-null = L.[]
⟦ n S.∷ ns ⟧-null = ⟦ n ⟧-null-typedvalue L.∷ ⟦ ns ⟧-null


⟦_⟧-≔-+-typedvalue : ∀ {x y z} → x S.≔ y + z → ⟦ x ⟧ₑ-typedvalue L.≔ ⟦ y ⟧ₑ-typedvalue + ⟦ z ⟧ₑ-typedvalue
⟦ S.pure ⟧-≔-+-typedvalue = L.pure
⟦ S.sesh S.left ⟧-≔-+-typedvalue = L.line L.go-left
⟦ S.sesh S.right ⟧-≔-+-typedvalue = L.line L.go-right
⟦ S.unre ⟧-≔-+-typedvalue = L.unre

⟦_⟧-≔-+ : ∀ {xs ys zs} → xs S.≔ ys + zs → ⟦ xs ⟧ₑ-ctx L.≔ ⟦ ys ⟧ₑ-ctx + ⟦ zs ⟧ₑ-ctx
⟦ S.[] ⟧-≔-+ = L.[]
⟦ spl S.∷ spls ⟧-≔-+ = ⟦ spl ⟧-≔-+-typedvalue L.∷ ⟦ spls ⟧-≔-+

exhaust : ∀ {xs n zs T t} → xs S.∋ₜ S.at n (S.exhaust (T , t)) ▹ zs
        → Σ[ ys ∈ L.Ctx ] ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx × ys L.∋ (⟦ T ⟧ₑ-type , encode T t)
exhaust (S.here S.exhaust-pure) = _ , L.go-left L.∷ L.go-right , L.here L.neutral-null
exhaust (S.here S.exhaust-sesh) = _ , L.go-left L.∷ L.go-right , L.here L.neutral-null
exhaust (S.here S.exhaust-unre) = _ , L.unre L.∷ L.go-right , L.here L.neutral-null
exhaust (S.there x)
  with _ , spl , x' ← exhaust x
  = _ , L.go-right L.∷ spl , L.there L.neutral-null x'

unre : ∀ {xs n ys T}
      → xs S.∋ₜ S.at n (S.is-type T) ▹ ys
      → xs ≡ ys × Σ[ zs ∈ L.Ctx ] L.InsertAt n ⟦ T ⟧ₑ-typedvalue zs ⟦ xs ⟧ₑ-ctx
unre (S.here S.is-type) = refl , _ , L.here
unre (S.there x)
  with eq , _ , ins ← unre x
  = cong (_ ∷_) eq , _ , L.there ins


send-sesh : ∀ {n T t C zs ys}
        → ys S.∋ₜ S.at n (S.send-sesh T t C) ▹ zs
        → Σ[ xs ∈ L.Ctx ]
          L.InsertAt n (L.line (L.ℓₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C))) , tt) xs ⟦ ys ⟧ₑ-ctx
        × L.InsertAt n (encode-cont T C (encode T t) , tt) xs ⟦ zs ⟧ₑ-ctx
send-sesh {T = T} {t = t} (S.here S.send-sesh) rewrite decode-encode T {t} = _ , L.here , L.here
send-sesh (S.there x)
  with ! ins1 , ins2 ← send-sesh x
  = _ , L.there ins1 , L.there ins2

recv-sesh : ∀ {n T t C zs ys}
        → ys S.∋ₜ S.at n (S.recv-sesh T (decode T t) C) ▹ zs
        → Σ[ xs ∈ L.Ctx ]
          L.InsertAt n (L.line (L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C))) , tt) xs ⟦ ys ⟧ₑ-ctx
        × L.InsertAt n (encode-cont T C t , tt) xs ⟦ zs ⟧ₑ-ctx
recv-sesh (S.here S.recv-sesh) = _ , L.here , L.here
recv-sesh (S.there x)
  with ! ins1 , ins2 ← recv-sesh x
  = _ , L.there ins1 , L.there ins2


insert-+-var : ∀ {n t xs ys} → L.InsertAt n t xs ys → Σ[ (rs , zs) ∈ L.Ctx × L.Ctx ] ys L.≔ rs + zs × rs L.∋ t × L.InsertAt n (L.neutral t) xs zs
insert-+-var L.here = _ , L.go-left L.∷ L.go-right , L.here L.neutral-null , L.here
insert-+-var (L.there x) = let _ , spl , vr , ins = insert-+-var x in _ , L.go-right L.∷ spl , L.there L.neutral-null vr , L.there ins


mutual
  dual-flip-inverse : ∀ S → flip-chan ⟦ S.dual S ⟧ₑ-session ≡ ⟦ S ⟧ₑ-session
  dual-flip-inverse S.end = refl
  dual-flip-inverse (S.recv T C) = cong (λ ● → L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type ●)) (EXTENSIONALITY (cong L.line ∘ dual-flip-inverse ∘ C ∘ decode T))
  dual-flip-inverse (S.send T C) = cong (λ ● → L.ℓₒ (L.prod ⟦ T ⟧ₑ-type ●)) (EXTENSIONALITY (cong L.line ∘ dual-flip ∘ C ∘ decode T))

  dual-flip : ∀ S → ⟦ S.dual S ⟧ₑ-session ≡ flip-chan ⟦ S ⟧ₑ-session
  dual-flip S.end = refl
  dual-flip (S.recv T C) = cong (λ ● → L.ℓₒ (L.prod ⟦ T ⟧ₑ-type ●)) (EXTENSIONALITY (cong L.line ∘ dual-flip-inverse ∘ C ∘ decode T))
  dual-flip (S.send T C) = cong ((λ ● → L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type ●))) (EXTENSIONALITY (cong L.line ∘ dual-flip ∘ C ∘ decode T))

split-new : ∀ S → Σ[ t ∈ L.Linear ] L.New (L.line t , tt) × t L.≔ ⟦ S ⟧ₑ-session + ⟦ S.dual S ⟧ₑ-session
split-new S.end = _ , L.∅ , L.ℓ∅
split-new (S.recv T C) = _ , L.ᵢₒ _ , subst
  (λ ● → L.ℓᵢₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C)) L.≔ L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C)) + L.ℓₒ (L.prod ⟦ T ⟧ₑ-type ●))
  (EXTENSIONALITY (cong L.line ∘ sym ∘ dual-flip-inverse ∘ C ∘ decode T))
  L.ℓᵢₒ
split-new (S.send T C) = _ , L.ᵢₒ _ , subst
  (λ ● → L.ℓᵢₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)) L.≔ L.ℓₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)) + L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type ●))
  (EXTENSIONALITY (cong L.line ∘ sym ∘ dual-flip ∘ C ∘ decode T))
  L.ℓₒᵢ

insert-source-eq : ∀ {n t ys xs xs'} → L.InsertAt n t xs ys → L.InsertAt n t xs' ys → xs ≡ xs'
insert-source-eq L.here L.here = refl
insert-source-eq (L.there ins1) (L.there ins2) = cong (_ ∷_) (insert-source-eq ins1 ins2)

mutual
  ⟦_⟧ₚ : ∀ {Γ} → S.Process Γ → L.Process ⟦ Γ ⟧ₑ-ctx
  ⟦ S.end n ⟧ₚ = L.end ⟦ n ⟧-null
  ⟦ S.par s p q ⟧ₚ = L.par ⟦ s ⟧-≔-+ ⟦ p ⟧ₚ ⟦ q ⟧ₚ
  ⟦ S.rep n p ⟧ₚ = L.rep ⟦ n ⟧-null ⟦ p ⟧ₚ


  ⟦ S.new (S.unre t) p ⟧ₚ = L.new (L.unre ⟦ t ⟧ₑ-type) (L.new (L.unre ⟦ t ⟧ₑ-type) ⟦ p ⟧ₚ)
  ⟦ S.new (S.sesh S) p ⟧ₚ =
    let _ , new , spl = split-new S in
    L.new new (L.subst-proc (L.line spl L.∷ L.go-right) (L.var (L.here L.neutral-null)) L.here ⟦ p ⟧ₚ)


  ⟦ S.send-sesh {zs = Ξ} {T = T} {t = t} {C = C} v s p ⟧ₚ
    with _ , new , spl-new ← split-new (C t)
    with Γ , spv , tv ← exhaust v
    with Δ , ch , cont ← send-sesh s
    with (_ , Θ) , spl' , ch' , ins' ← insert-+-var ch
    rewrite decode-encode T {t}
    rewrite EXTENSIONALITY {B = λ ● → L.Type} (cong L.line ∘ sym ∘ dual-flip ∘ C ∘ decode T)
    = L.new new
    $ L.send-line {T = L.prod ⟦ T ⟧ₑ-type λ x → L.line ⟦ S.dual (C (decode T x)) ⟧ₑ-session}
      (L.line (L.+-comm spl-new) L.∷ spv)
      (L.pair
        (L.go-right L.∷ L.go-left)
        (L.var (L.there (L.line L.ℓ∅) tv))
        (L.var (subst (λ ● → (_ ∷ L.neutral Γ) L.∋ (L.line ⟦ S.dual (C ●) ⟧ₑ-session , tt)) (sym (decode-encode T)) (L.here L.neutral-null))))
      (L.go-right L.∷ spl')
      (L.var (L.there (L.line L.ℓ∅) ch'))

    $  ⟦ p ⟧ₚ                                             ∶ L.Process ⟦ Ξ ⟧ₑ-ctx
    |> L.exchange-proc cont L.here                        ∶ L.Process ((L.line ⟦ C t ⟧ₑ-session , tt) ∷ Δ)
    |> L.Process-null-insert (L.line L.ℓ∅) (L.there ins') ∶ L.Process ((L.line ⟦ C t ⟧ₑ-session , tt) ∷ Θ)

  ⟦ S.recv-sesh {ys = ys} {zs = Γ} {T = T} {C = C} s p ⟧ₚ
    with eq , Θ , ins ← unre s
    with (_ , Ξ) , spl , ni , insnull ← insert-+-var ins
    rewrite eq
    = L.recv-line spl (L.var ni) λ (t , tt) → continuation t
    where
      continuation : (t : L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ) → L.Process ((L.prod ⟦ T ⟧ₑ-type (encode-cont T C) , (t , tt)) ∷ Ξ)
      continuation t
        with recvc , proc-cont ← p (decode T t)
        with Δ , insch , inscont ← recv-sesh recvc
        rewrite insert-source-eq insch ins
        = L.letprod (L.go-left L.∷ L.go-right) (L.var (L.here L.neutral-null))

        $  ⟦ proc-cont ⟧ₚ                                                                               ∶ L.Process ⟦ (T , decode T t) ∷ Γ ⟧ₑ-ctx
        |> L.exchange-proc (L.there inscont) (L.there L.here)                                           ∶ L.Process (⟦ T , decode T t ⟧ₑ-typedvalue ∷ (encode-cont T C t , tt) ∷ Θ)
        |> L.Process-null-insert (L.line L.ℓ∅) (L.there (L.there L.here))                               ∶ L.Process (⟦ T , decode T t ⟧ₑ-typedvalue ∷ (encode-cont T C t , tt) ∷ (L.line L.ℓ∅ , tt) ∷ Θ)
        |> L.exchange-proc (L.there (L.there L.here)) (L.there (L.there insnull))                       ∶  L.Process (⟦ T , decode T t ⟧ₑ-typedvalue ∷ (encode-cont T C t , tt) ∷ Ξ)
        |> subst (λ ● → L.Process ((⟦ T ⟧ₑ-type , ●) ∷ (encode-cont T C t , tt) ∷ _)) (encode-decode T) ∶ L.Process ((⟦ T ⟧ₑ-type , t) ∷ (encode-cont T C t , tt) ∷ Ξ)
        |> L.Process-null-insert L.pure (L.there (L.there L.here))                                      ∶ L.Process ((⟦ T ⟧ₑ-type , t) ∷ (encode-cont T C t , tt) ∷ (L.pure ⊤ , tt) ∷ Ξ)

  ⟦ S.send-unre {T = T} {t = t} v c p ⟧ₚ
    with ! spv , tv ← exhaust v
    with eq , _ , insch ← unre c
    with (_ , ctx) , splch , nich , inschnull ← insert-+-var insch
    rewrite eq
    = L.send-unre spv (L.var tv) splch (L.var nich)
    $ L.exchange-proc insch inschnull
    $ ⟦ p ⟧ₚ

  ⟦ S.recv-unre {ys = ys} {T = T} c p ⟧ₚ
    with eq , _ , insch ← unre c
    with (_ , ctx) , splch , nich , inschnull ← insert-+-var insch
    rewrite eq
    = L.recv-unre splch (L.var nich) λ t
    → subst (λ ● → L.Process ((⟦ T ⟧ₑ-type , ●) ∷ ctx)) (encode-decode T)
    $ L.exchange-proc (L.there insch) (L.there inschnull)
    $ ⟦ p (decode T t) ⟧ₚ
