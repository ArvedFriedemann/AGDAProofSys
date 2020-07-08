module util where


open import Agda.Primitive renaming (_⊔_ to _~U~_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_)
open Eq.≡-Reasoning using (begin_; step-≡; step-≡˘) renaming (_≡⟨⟩_ to _=<>_ ; _∎ to _end)

private
  variable
    l ll : Level

infixr 2 _=<_>_ _=^<_>_

_=<_>_ : forall {a} {A : Set a} (x {y z} : A) -> y === z -> x === y -> x === z
a =< b > c =  a ≡⟨ c ⟩ b

_=^<_>_ : forall {a} {A : Set a} (x {y z} : A) -> y === z -> y === x -> x === z
a =^< b > c =  a ≡˘⟨ c ⟩ b


data BOT {l} : Set l where

infix 3 ¬_
¬_ : Set l -> Set (lsuc l)
¬ prop = prop -> BOT

data Bool {l} : Set l where
  true : Bool {l}
  false : Bool {l}

not : Bool {l} -> Bool {l}
not true = false
not false = true

dub-not-id : forall {l} {b : Bool {l}} -> not (not b) === b
dub-not-id {l} {true} = refl
dub-not-id {l} {false} = refl

dub-not-id' : forall {l} {b : Bool {l}} -> b === not (not b)
dub-not-id' = sym dub-not-id

switch-not : forall {l} {b c : Bool {l}} -> not b === c -> b === not c
switch-not ¬b=c = trans dub-not-id' (cong not ¬b=c)

switch-not' : forall {l} {b c : Bool {l}} -> b === not c -> not b === c
switch-not' b=¬c = sym (switch-not (sym b=¬c))


_&&_ : Bool {l} -> Bool {ll} -> Bool {l ~U~ ll}
_&&_ true true = true
_&&_ _ _ = false

_||_ : Bool {l} -> Bool {ll} -> Bool {l ~U~ ll}
_||_ false false = false
_||_ _ _ = true

_->>_ : Bool {l} -> Bool {ll} -> Bool {l ~U~ ll}
_->>_ true false = false
_->>_ _ _ = true

data sigma (A : Set l) (B : A -> Set ll) : Set (l ~U~ ll) where
  <_,_> : (x : A) -> B x -> sigma A B

sigma-syntax = sigma
infix 2 sigma-syntax
syntax sigma-syntax A (\ x -> B) = exists x of A st B

infixr 1 _or_
data _or_ (A B : Set l) : Set l where
  left : A -> A or B
  right : B -> A or B

const : {A B : Set l} -> A -> B -> A
const x _ = x
