{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem
open import LinearPi.Weakening
open import LinearPi.Substitution

module LinearPi.Exchange where

insert-var : ∀ {t xs n ys} → Null xs → InsertAt n t xs ys → ys ∋ t
insert-var null here = here null
insert-var (xnull ∷ xsnull) (there ins) = there xnull (insert-var xsnull ins)

var-insert : ∀ {t n xs ys s} → Null t → InsertAt n t xs ys → xs ∋ s → ys ∋ s
var-insert null here ni = there null ni
var-insert null (there ins) (here null1) = here (null-insert ins null null1)
var-insert null (there ins) (there null1 ni) = there null1 (var-insert null ins ni)

exchange-var : ∀ {n t xs ys m zs s}
             → InsertAt n t xs ys
             → InsertAt m t xs zs
             → ys ∋ s
             → zs ∋ s
exchange-var ins1 ins2 vr with occurs? ins1 vr
exchange-var ins1 ins2 vr | yes null = insert-var null ins2
exchange-var ins1 ins2 vr | no null vr2 = var-insert null ins2 vr2

exchange-term : ∀ {n t xs ys m zs s}
              → InsertAt n t xs ys
              → InsertAt m t xs zs
              → Term ys s
              → Term zs s
exchange-term ins1 ins2 (var x) = var (exchange-var ins1 ins2 x)
exchange-term ins1 ins2 (pure a x) =
  let null1 , null2 = insert-null ins1 x in
  pure a (null-insert ins2 null1 null2)
exchange-term ins1 ins2 (pair (spl , sub) l r) =
  let _ , tspl1 , spl1 , lins1 , rins1 = extract ins1 {!spl!} in
  let _ , spl2 , lins2 , rins2 = imtract spl1 tspl1 ins2 in
  pair ({!!} , {!!}) (exchange-term lins1 lins2 l) (exchange-term rins1 rins2 r)

exchange-proc : ∀ {n t xs ys m zs}
              → InsertAt n t xs ys
              → InsertAt m t xs zs
              → Process ys
              → Process zs
exchange-proc ins1 ins2 (end ys-null) =
  let t-null , xs-null = insert-null ins1 ys-null in
  end (null-insert ins2 t-null xs-null)
exchange-proc ins1 ins2 (par spl p q) = {!!}
{-
  let _ , tspl1 , spl1 , lins1 , rins1 = extract ins1 spl in
  let _ , spl2 , lins2 , rins2 = imtract spl1 tspl1 ins2 in
  par spl2 (exchange-proc lins1 lins2 p) (exchange-proc rins1 rins2 q)
  -}
exchange-proc ins1 ins2 (new x p) =
  new x (exchange-proc (there ins1) (there ins2) p)
exchange-proc ins1 ins2 (rep ys-null p) =
  let t-null , xs-null = insert-null ins1 ys-null in
  rep (null-insert ins2 t-null xs-null) (exchange-proc ins1 ins2 p)
exchange-proc ins1 ins2 (send spl-payload payload spl-channel channel p) = {!!}
{-
  let _ , payload-tspl , payload-spl1 , payload-lins1 , payload-rins1 = extract ins1 spl-payload in
  let _ , payload-spl2 , payload-lins2 , payload-rins2 = imtract payload-spl1 payload-tspl ins2 in
  let _ , channel-tspl , channel-spl1 , channel-lins1 , channel-rins1 = extract payload-rins1 spl-channel in
  let _ , channel-spl2 , channel-lins2 , channel-rins2 = imtract channel-spl1 channel-tspl payload-rins2 in
  send
    payload-spl2 (exchange-term payload-lins1 payload-lins2 payload)
    channel-spl2 (exchange-term channel-lins1 channel-lins2 channel)
    (exchange-proc channel-rins1 channel-rins2 p)
    -}
exchange-proc ins1 ins2 (recv spl channel cont) = {!!}
{-
  let _ , tspl1 , spl1 , lins1 , rins1 = extract ins1 spl in
  let _ , spl2 , lins2 , rins2 = imtract spl1 tspl1 ins2 in
  recv
    spl2 (exchange-term lins1 lins2 channel)
    λ t → exchange-proc (there rins1) (there rins2) (cont t)
    -}
exchange-proc ins1 ins2 (letprod spl prd p) = {!!}
{-
  let _ , tspl1 , spl1 , lins1 , rins1 = extract ins1 spl in
  let _ , spl2 , lins2 , rins2 = imtract spl1 tspl1 ins2 in
  letprod
    spl2 (exchange-term lins1 lins2 prd)
    (exchange-proc (there (there rins1)) (there (there rins2)) p)
    -}
