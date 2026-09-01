From Coq Require Import PeanoNat.

Inductive value : Type :=
| VConcrete : nat -> value
| VUndef    : value
| VUnalloc  : value.

Definition value_eq_dec :
  forall x y : value, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.
