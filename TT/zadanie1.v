(*********************************************)
(**       Zadanie k prednáške 1             **)
(*********************************************)
(**       Programovanie v Rocq              **)

(*
  Poznámka:
  Odporúčam stiahnuť a vytlačiť nasledujúce "cheatsheets":
  -https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf
  -https://www.cs.cornell.edu/courses/cs3110/
   2018sp/a5/coq-tactics-cheatsheet.html

  Poznámka:
  Ďalšiu odporúčanú literatúru nájdete 
  na stránke predmetu.
*)

(*
  Úloha 1.1
  Definujte modul cvicenieBool pre prácu s vlastným typom bool.
*)

Module cvicenieBool.

(*
  Úloha 1.2
  Definujte vlastný induktívny typ bool.
*)

(* tu príde definícia TODO *)
Inductive bool: Type :=
  | true : bool
  | false : bool
. 


(*
  Úloha 1.3
  Definujte funkcie pre nasledujúce operácie nad typom bool:
  - negácia
  - konjunkcia
  - disjunkcia
  - implikácia
  Pomenujte ich negb, andb, orb, implb. 
*)

(* definície funkcií TODO *)
Definition negb (b:bool) :bool := 
  match b with
  | true => false
  | false => true
  end. 


Definition andb (b1 b2:bool) :bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2:bool) :bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition implb (b1 b2:bool) :bool := 
  orb (negb b1) b2. 

(*
  Úloha 1.4
  Využitím Vernacular príkazov:
  - Check
  - Print
  - About
  vypíšte informácie o Vašich definíciách a 
  pouvažujte nad rozdielmi medzi nimi.
*)

(* príklady použitia: Check ..., Print ..., About ... TODO *)
Check andb.
Check orb.
Check implb.
Check negb.

Print andb.
Print orb.
Print implb.
Print negb.

About andb.
About orb.
About implb.
About negb.


(*
  Úloha 1.5
  Prostredníctvom Vernacular príkazu Compute 
  otestujte či sa Vaše funkcie negb, andb, orb, a implb 
  správajú podľa očakávania.
*)

(* 
TODO odkomentovať
*)
Compute (negb true).
Compute (negb false).

Compute (andb true true).
Compute (andb true false).
Compute (andb false true).
Compute (andb false false).

Compute (orb true true).
Compute (orb true false).
Compute (orb false true).
Compute (orb false false).

Compute (implb true true).
Compute (implb true false).
Compute (implb false true).
Compute (implb false false).
(**)

(*
  Úloha 1.6
  Aktuálne pre výpočet boolovských funkcií 
  je potrebné využívať prefixnú formu,
  čo je pre programátora neprirodzené. 
  
  Zaveďte notácie pre Vami definované
  funkcie (! negb, &&& andb, ||| orb, ---> implb), 
  uvažujte o priorite a asociativite jednotlivých
  operátorov.
*)

(* Notation ... TODO*)


(*
  Úloha 1.7
  Prostredníctvom Vernacular príkazu Compute otestujte
  implementáciu notácií.
*)

Notation "! a" := (negb a ) (at level 40).
Notation "a &&& b" := (andb a b) (at level 41, left associativity).
Notation "a ||| b" := (orb a b) (at level 42, left associativity).
Notation "a ---> b" := (implb a b) (at level 43, left associativity).
(*
  Predpokladáme, že máte definované:
  - funkciu negácie
  - konjunkciu
  - disjunkciu
  - implikáciu
  a zavedené notácie: !, &&&, |||, --->.
*)

(*
  Testovacie príklady pre zavedenú notáciu (!, &&&, |||, --->)
  Odkomentujte a otestujte:
*)
Compute (! true).            (* očak.: false *)
Compute (! false).           (* očak.: true  *)

Compute (true &&& true).     (* očak.: true  *)
Compute (true &&& false).    (* očak.: false *)
Compute (false &&& true).    (* očak.: false *)
Compute (false &&& false).   (* očak.: false *)

Compute (true ||| true).     (* očak.: true  *)
Compute (true ||| false).    (* očak.: true  *)
Compute (false ||| true).    (* očak.: true  *)
Compute (false ||| false).   (* očak.: false *)

Compute (true ---> true).    (* očak.: true  *)
Compute (true ---> false).   (* očak.: false *)
Compute (false ---> true).   (* očak.: true  *)
Compute (false ---> false).  (* očak.: true  *)



(*
  Úloha 1.8
  Otestujte implementáciu asociativity 
  a priority na vhodných príkladoch.
*)

(*
  Testy priorít a asociativity
  Odkomentujte a otestujte
*)

(* Negácia má najvyššiu prioritu *) 
Compute (! true &&& true).    
(* vyhodnotí sa ako ((! true) &&& true) → očak.: false *)

(* Konjunkcia  má najvyššiu než disjunkcia) *) 
Compute (true ||| true &&& false).  
(* vyhodnotí sa ako (true ||| (true &&& false)) → očak.: true *)
 
 
(* Implikácia má najnižšiu prioritu *)
Compute (true &&& false ---> true). 
(* vyhodnotí sa ako ((true &&& false) ---> true) → očak.: true *)


(* Asociativita disjunkcie *)
Compute ((true ||| false) ||| false).   (* očak.: true *)
Compute (true ||| (false ||| false)).   (* očak.: true *)


(* Asociativita konjunkcie *) 
Compute ((true &&& false) &&& true).    (* očak.: false *)
Compute (true &&& (false &&& true)).    (* očak.: false *)




(*
  Úloha 1.9
  Ukončite prácu v rámci modulu cvicenieBool.
*)

End cvicenieBool.

(*
  Úloha 1.10
  V rámci materiálov pre cvičenie a prednášku
  je prezentovaný kód pre definíciu typu
  nat a operácií sčítania a násobenia.

  Tento typ obsahuje štandardná knižnica systému Rocq.

  Zistite, ako je daný typ implementovaný v štandardnej knižnici 
  a aké operácie nad ním sú definované.
  
  TODO
*)

Check nat.
About nat.
Print nat.
Search nat.
Locate nat.

(*
  Úloha 1.11
  Definujte funkcie:
  - následovníka succesor
  - predchodcu pred
  - overenia nuly iszero
  s využitím typu nat zo štandardnej knižnice.
*)

(* TODO definície funkcií succesor, pred, iszero *)

Definition succesor (n:nat) : nat := n + 1.

Definition pred (n:nat) : nat := n - 1.

Definition iszero (n:nat) : bool :=
  match n with 
  | 0 => true
  | S _ => false
  end.
(*
Compute iszero 1.
Compute succesor 1.
Compute pred 1.
*)
(*
  Úloha 1.12
  Implementujte funkcie pre sčítanie 
  a násobenie podľa rekurzívnej definície
  z cvičenia 3 na stránke predmetu.
  Pomenujte ich plus_rec a times_rec
*)

(* TODO definície funkcií pre sčítanie a násobenie *)
Fixpoint plus_rec (m:nat) (n:nat) : nat := 
  match m with
  | 0 => n
  | S m' => plus_rec (m') (succesor n)
  end.

(*
Compute plus_rec 1 1.
*)

Fixpoint times_rec (m:nat) (n:nat) : nat :=
  match m with
  | 0 => 0
  | S m' => plus_rec n (times_rec m' n)
  end.
(*
Compute times_rec 6 8.
*)

(*********************************************)
(**             Zadanie                     **)
(*********************************************)
(**            Prvé dôkazy                  **)


(*
===============================================
     Príklady na precvičenie základných taktík
===============================================
*)

(*
 Úloha 2.1. 
 Dokážte, že každý boolean je rovný sám sebe.
*)
Theorem bool_self : forall b : bool, b = b.
Proof.
  intro b.
  reflexivity.
Qed.

(*
 Úloha 2.2. 
 Dokážte, že 4 + 0 = 4.
*)

Theorem four_plus_zero : 4 + 0 = 4.
Proof.
  simpl.
  reflexivity.
Qed.

(*
 Úloha 2.3.
*)
Theorem use_assumption :
  forall (n m : nat), n = m -> n = m.
Proof.
  intros n m H.
  simpl.
  assumption.
Qed.

(*
 Úloha 2.4. 
 Dokážte, že ak n = m, tak n + 2 = m + 2.
*)
Theorem plus_two :
  forall (n m : nat), n = m -> n + 2 = m + 2.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

(*
 Úloha 2.5. Rewrite s lemmou
 Najprv dokážte jednoduchú lemmu a potom ju použite 
 v plus_zero_example.
*)
Theorem add_zero_left : forall n, 0 + n = n.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_zero_example : forall n, 0 + n + 3 = n + 3.
Proof.
  intros n.
  rewrite add_zero_left.
  reflexivity.
Qed.

(*
 Úloha 2.6. 
 Dokážte, že b || true = true.
*)
(* Načítanie typu zo štandardnej knižnice *)
Require Import Coq.Bool.Bool.
Compute (true && true).  (*konjunjcia*)
Compute (true || true).  (*disjunkcia*)
Compute (negb true).     (*negácia*)

Theorem orb_true : forall b : bool, b || true = true.
Proof.
  intro b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

(*
 Úloha 2.7.
 Dokážte, že pre každé n : nat platí:
   1 + n = S n
*)

Theorem one_plus_n : forall n : nat, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


(*
 Úloha 2.8. 
 Dokážte: (n = m) -> (m = k) -> (n = k).
*)
Theorem trans_eq : forall n m k : nat, n = m -> m = k -> n = k.
Proof.
  intros .
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.
