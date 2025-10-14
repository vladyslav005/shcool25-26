(*********************************************)
(**       Zadanie k prednáške 2             **)
(*Import potrebných knižníc*)
Require Import Coq.Bool.Bool.
Require Import Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

(*
==================================================
Doplnok k prednáške:
==================================================
Základná tabuľka operátorov v Coq
==================================================

1 Porovnávacie operátory pre nat (vracajú bool)
--------------------------------------------------
  n =? m    : test rovnosti (true ak n = m, inak false)
  n <=? m   : menšie alebo rovné
  n <? m    : menšie
  n >=? m   : väčšie alebo rovné (rovnako ako m <=? n)
  n >? m    : väčšie (rovnako ako m <? n)
  n <>? m   : nerovnosť (negb (n =? m))

Príklady:
  Compute (3 <=? 5).  (* true *)
  Compute (5 =? 3).   (* false *)
  Compute (4 <? 4).   (* false *)
  Compute (4 >? 2).   (* true *)

--------------------------------------------------
2 Logické operátory pre bool
--------------------------------------------------
  negb b        : -
  andb b1 b2    : b1 && b2
  orb b1 b2     : b1 || b2
  xorb b1 b2    : -

Príklady:
  Compute (andb true false).   (* false *)
  Compute (orb true false).    (* true *)
  Compute (negb true).         (* false *)
  Compute (xorb true false).   (* true *)

--------------------------------------------------
3 Logické operátory pre Prop (dôkazy)
--------------------------------------------------
  P /\ Q        : P AND Q
  P \/ Q        : P OR Q
  ~ P           : NOT P
  P -> Q        : implikácia
  P <-> Q       : ekvivalencia

Poznámka: Prop je typ pre formálne tvrdenia a dôkazy,
          bool je typ programovo vyhodnocovateľný.

==================================================
*)

(*
==================================================
Rozdiel medzi bool a Prop pri porovnaniach
==================================================

V Rocq existujú dve “verzie” porovnania pre nat:

bool – programovo vyhodnocovateľná hodnota
  - Napr. n =? m alebo n <=? m vracia true/false (typu bool)
  - Používa sa pri výpočtoch, Compute, if vetveniach
  - Príklad: Compute (3 <=? 5).  (* true *)

Prop – logické tvrdenie
  - Napr. n = m alebo n <= m typu Prop
  - Používa sa pri dôkazoch, rewrite, indukcii
  - Príklad: forall n m : nat, n <= m -> ...

Otáznik (?):
  - n =? m, n <=? m, n <? m vracajú bool
  - Bez otázniku n = m... vracajú Prop, 
    ktoré nie je hodnotou
  - Bool verziu môžeme kombinovať 
    s andb, orb alebo if (vo výpočtoch)
  - Prop verziu používame v dôkazoch
==================================================
*)



(*********************************************)
(**           Dôkazy                        **)


(*********************************************)
(**       Zadanie k prednáške 2             **)
(*Import potrebných knižníc*)
Require Import Coq.Bool.Bool.
Require Import Init.Nat.
Require Import Coq.Arith.PeanoNat.
Local Open Scope nat_scope.

(*********************************************)
(**           Dôkazy                        **)

(* 
  Úloha 3.1: Dokážte, že n - n = 0
*)
Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

(* Úloha 3.2: Dokážte: n * 0 = 0 *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

(* Úloha 3.3: Dokážte: n * 1 = n *)
Theorem mult_n_1 : forall n, n * 1 = n.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

(* Úloha 3.4: Dokážte, že 1 + (n + m) = n + (1 + m) *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.

  induction n, m.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


Theorem plus_n_0 : forall n: nat,
  n + 0 = n.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
 
(* Úloha 3.5: Dokážte komutatívnosť sčítania *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
 
  induction n, m.
  reflexivity.
  
  simpl.
  rewrite plus_n_0.
  reflexivity.
  simpl.
  rewrite plus_n_0.
  reflexivity.
  simpl.
  rewrite IHn.
  simpl.
  rewrite plus_n_Sm.
  reflexivity.
Qed.

(* Úloha 3.6: Dokážte asociativnosť sčítania *)
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  induction m.
  simpl.
  rewrite plus_n_0.
  reflexivity.
  induction p.
  simpl.
  rewrite plus_n_0.
  rewrite plus_n_0.
  reflexivity.
  
  rewrite IHn.
  reflexivity.

Qed.

(* Definícia: Funkcia double zdvojnásobí argument *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Úloha 3.7: Dokážte, že double n = n + n *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  simpl.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.

(* Úloha 3.8
Jedným nepraktickým aspektom definície even 
zo štandardnej knižnice je 
rekurzívne volanie na n - 2. 
To sťažuje dôkazy indukciou, 
pretože môžeme potrebovať 
indukčný predpoklad pre n - 2. 
Nasledujúca lema poskytuje 
alternatívnu charakterizáciu even (S n).
*)
Print even.


Theorem neg_neg_b : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.
  
  
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  induction n.
  simpl.
  reflexivity.
  
  rewrite IHn.
  simpl.
  rewrite neg_neg_b.
  reflexivity.
Qed.  


(* Úloha 3.9: Zamiešanie sčítania *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite (add_comm n m).
  rewrite  add_assoc.
  reflexivity.
Qed.


Lemma mul_1 : forall n : nat ,
  n * 1 = n.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.





Theorem mul_0  : forall m n : nat,
    n * 0 = 0.
Proof.
  intros.
  induction n.
  simpl.
  
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem mul_0'  : forall m n : nat,
    0 * n = 0.
Proof.
  intros.
  induction n.
  simpl.
  
  reflexivity.
  simpl.
  reflexivity.
Qed.


Theorem mul_0_sm  : forall m n : nat,
    0 * S m = 0.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem mul_0_ssm  : forall m n : nat,
    0 * S(S m) = 0.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.


Theorem mult_Sn : forall n m : nat,
  n * S m = n * m + n.
Proof.
  intros n m.
  induction n as [| n' IH].
  - (* base case: n = 0 *)
    simpl. reflexivity.
  - (* inductive case: n = S n' *)
    simpl.
    rewrite IH.
    (* Now we must show: m + n' + S n' = (m + n') + S n' *)
    simpl.
    rewrite plus_n_Sm.
    rewrite plus_n_Sm.
    rewrite add_assoc.
    simpl.
     reflexivity.
Qed.
  

(* Úloha 3.10: Komutativnosť násobenia *)
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [| m IH]; simpl.
  - rewrite mul_0_r. reflexivity.
  - rewrite IH.
    rewrite mult_Sn.
    rewrite add_comm.
    reflexivity.
Qed.


(* Úloha 3.11: 
Ak má hypotéza tvar H: P → a = b, 
potom taktika rewrite H prepíše a na b 
v cieli a pridá P ako nový podcieľ. 

Použite to v indukčnom kroku tejto úlohy. *)
Check leb.
Print leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros.
  induction p.
  simpl.
  apply H.
  simpl.
  rewrite IHp.
  reflexivity.
Qed.

(* Úloha 3.12: Reflektivita leb *)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  apply IHn.
Qed.

(* Úloha 3.13: 0 sa nerovná 1 + n *)
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

(* Úloha 3.14: b && false = b *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

(* Úloha 3.15: 1+n sa nerovná 0 *)
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros .
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

(* Úloha 3.16: 1 * n = n *)
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros.
  rewrite <-mul_1.
  rewrite mul_comm.
  reflexivity.
Qed.

(* Úloha 3.17: Logická kombinácia orb/andb/negb *)
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros.
  induction b, c.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.


(* Úloha 3.18: Distribútivita násobenia 
cez sčítanie sprava *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n' IHn].
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- add_assoc.
    
    reflexivity.
Qed.


(* Úloha 3.19: Asociativnosť násobenia *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn].
  simpl.
  reflexivity.
  simpl.
  rewrite mult_plus_distr_r.
  rewrite IHn.
  reflexivity.
Qed.

(* Úloha 3.20: add_shuffle3' s replace *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc.
  rewrite ( add_comm n  m).
  reflexivity.
Qed.



