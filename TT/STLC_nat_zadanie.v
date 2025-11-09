
(* ================================================================= *)
(** ** Zadanie: STLC s aritmetikou *)

(** Jednoducho typovaný λ-kalkul (STLC),
    rozšírime ho o konkrétny základný typ čísel a niekoľko
    konštánt a primitívnych operátorov. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Init.Nat.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.
From Coq Require Import String.
Open Scope string_scope.
Module STLCArith.

(** K typom pridáme základný typ prirodzených čísel (a pre stručnosť
    odstránime booleovské typy). *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty.

(** K termom pridáme konštanty prirodzených čísel, spolu s
    funkciami successor, predecessor, násobenie a testovaním nulovosti. *)

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0 : tm -> tm -> tm -> tm.

(* ================================================================= *)
(** * STLC rozšírený o aritmetiku *)
(** Termy:
       t ::= x                      (premenná)
           | \x:T,t                 (λ-abstrakcia)
           | t t                    (aplikácia)
           | n                      (konštanta prirodzeného čísla)
           | succ t                 (nasledovník)
           | pred t                 (predchodca)
           | t * t                  (násobenie)
           | if0 t then t else t    (podmienený výraz testujúci nulu)
   Typy:
       T ::= Nat | T -> T

   - T -> T - typový konštruktor funkcie.
   - Nat - základný typ prirodzených čísel.
   - Konštanty a operácie: n, succ, pred, *, if0. *)


Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

(** Konkrétna syntax *)
Notation "x" := x (in custom stlc_ty at level 0, x global) 
: stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := 
t (in custom stlc_ty at level 0, t custom stlc_ty) 
: stlc_scope.
Notation "S -> T" := 
(Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) 
: stlc_scope.

Notation "$( t )" := 
t (in custom stlc_ty at level 0, t constr) : stlc_scope.


Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Notation "'Nat'" := Ty_Nat (in custom stlc_ty at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc_tm at level 10,
                                     x custom stlc_tm at level 0) : stlc_scope.
Notation "'pred' x" := (tm_pred x) (in custom stlc_tm at level 10,
                                     x custom stlc_tm at level 0) : stlc_scope.
Notation "x * y" := (tm_mult x y) (in custom stlc_tm at level 95,
                                      right associativity) : stlc_scope.
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc_tm at level 0,
                    x custom stlc_tm at level 0,
                    y custom stlc_tm at level 0,
                    z custom stlc_tm at level 0) : stlc_scope.

Coercion tm_const : nat >-> tm.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.


(** Vašou úlohou dokončiť formalizáciu
definície a vlastností STLC rozšíreného o aritmetiku.

Konkrétne:
Vyplňte základné definície pre STLCArith, začínajúc pravidlami
a termami, ktoré sú rovnaké ako v STLC. Potom dokážte kľúčové
lemy a vety, ktoré poskytujeme. Budete musieť definovať a dokázať
pomocné lemy, ako predtým.

Bude potrebné doplniť aj "Reserved Notation", "Notation"
a "Hint Constructors".

Nápoveda: Ak sa vám zobrazí chyba "STLC.tm" namiesto termu "tm",
Rocq používa starú notáciu (napr. pre subst) namiesto novej
pre STLCArith, takže musíte prepísať starú notáciu predtým,
než ju budete môcť použiť.

Uistite sa, že Rocq akceptuje celý súbor pred odovzdaním. 
*)


(** ----------------------------------------------- **)
(** Úloha 1 ★ Doplnte definíciu substitúcie. *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm
(* NAHRADIŤ TENTO RIADOK S ":= vaša_definícia ." *). 
Admitted.
(** 
Po definícii funkcie je potrebné odstrániť bodku na konci 
a pridať nasledujúci riadok

where "'[' x ':=' s ']' t" := (subst x s t) (v custom stlc_tm).
*)

(** ----------------------------------------------- **)
(** Úloha 2 ★ Doplnte definíciu hodnoty. *)

Inductive value : tm -> Prop :=
  (* FILL IN HERE *)
.

Hint Constructors value : core.


Reserved Notation "t '-->' t'" (at level 40).

(** ----------------------------------------------- **)
(** Úloha 3 ★ Doplnte definíciu štrukturálnej operačnej sémantiky . *)

Inductive step : tm -> tm -> Prop :=
  (* DOPLNIT *)
where "t '-->' t'" := (step t t').

Inductive multistep : tm -> tm -> Prop :=
  | multi_refl : forall t, multistep t t  
  | multi_tran : forall t1 t2 t3,
      step t1 t2 ->  
      multistep t2 t3 ->
      multistep t1 t3.
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* Príklad *)
Example Nat_step_example : exists t,
<{(\x: Nat, \y: Nat, x * y ) $(3) $(2) }> -->* t.
Proof.  Admitted.


(* Typový systém *)
Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := 
        (t_update m x v)
        (at level 100, x constr, right associativity).

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Definition context := partial_map ty.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
(at level 0, Gamma custom stlc_tm at level 200, 
t custom stlc_tm, T custom stlc_ty).

(** ----------------------------------------------- **)
(** Úloha 4 ★ Doplnte definíciu substitúcie. *)

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>

(** DOPLNIT *)

where "<{ Gamma '|--' t '\in' T }>" := 
  (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.
Hint Constructors has_type : core.

(* Príklad *)
Example Nat_typing_example :
   <{ empty |-- ( \x: Nat, \y: Nat, x * y ) $(3) $(2) \in Nat }>.
Proof.
 Admitted.



(* ================================================================= *)
(** ** Vety *)

(** ----------------------------------------------- **)
(** Úloha 5 ★ Dokážte nasledujúcu vetu. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
Proof. 
 Admitted.




(** ----------------------------------------------- **)
(** Úloha 6 ★ Dokážte nasledujúcu vetu. *)

(* Zachovanie typu (Preservation) *)
(* Nápoveda: Bude potrebné definovať a dokázať tie isté pomocné vety, 
  ktoré sú dokazáné v STLC + Bool. *)
Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.
Proof with eauto. 
Admitted.



(** ----------------------------------------------- **)
(** Úloha 7 ★ Dokážte nasledujúcu vetu. *)

(* Progress *)
Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof with eauto.  
Admitted.


End STLCArith.
