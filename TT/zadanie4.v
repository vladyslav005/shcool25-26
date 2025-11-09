(*********************************************)
(**       Zadanie k prednáške 4             **)
(*********************************************)

(*        Import potrebných knižníc         *) 

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Init.Nat.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(*-------------------------------------------*)
(** Úlohy:                                   *)
(*-------------------------------------------*)


(** Úloha 1 ★  
    Dokážte, že z `even p = true` vyplýva `odd (S p) = true`.*)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof. 
  intros p Hstep Hodd Heven.
  apply Hodd.
  apply Hstep.
  exact Heven.
Qed.

Lemma x :
  forall (l : list nat),
    l ++ [] = l.
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma append_assoc :
  forall (l1 l2 l3 : list nat),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


Lemma reverse_append :
  forall (l1 l2 : list nat),
    rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [| x xs IH].
  - simpl. rewrite x. reflexivity.
  - simpl. rewrite IH.
    rewrite append_assoc.  (* associate (reverse l2 ++ reverse xs) ++ [x] *)
    reflexivity.
Qed.


Theorem reverse_invol : forall (l : list nat),
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l IHl].
  - simpl. reflexivity.
  - simpl.                           (* reverse (append (reverse l) [n]) *)
    rewrite reverse_append.          (* = append (reverse [n]) (reverse (reverse l)) *)
    simpl.                           (* reverse [n] = [n] *)
    rewrite IHl.
    reflexivity.
Qed.

(** Úloha 2 ★  
    Dokážte, že ak `l = rev l'`, potom aj `l' = rev l`. *)
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof. 
  intros.
  rewrite H.
  rewrite reverse_invol.
  reflexivity.
Qed.


(** Úloha 3 ★  
    Dokážte, že z dvoch rovností zoznamov vyplýva `x = y`. *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof. 
  intros .
  subst j.
  injection H as Htl Hxz.
  rewrite Htl .
  rewrite Hxz.
  reflexivity.
Qed.


(** Úloha 4 ★  
    Dokážte, že zoznam `x :: y :: l` sa nemôže rovnať prázdnemu zoznamu. *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof. 
  intros.
  discriminate.
Qed.


(** Úloha 5 ★  
    Dokážte, že ak `n =? m = true`, potom `n = m`. *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof. 
  induction n as [| n IH]; intros m H.
  - destruct m; simpl in H; [reflexivity | discriminate].
  - destruct m; simpl in H; [discriminate | ].
    apply IH in H.
    subst.
    reflexivity.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  assert (H2 : n = pred (S n)) by reflexivity.
  rewrite H2. rewrite H. simpl. reflexivity.
Qed.


Lemma add_succ_r : forall n m, n + S m = S (n + m).
Proof.
  induction n as [| n IH]; intros m; simpl.
  - reflexivity.                         (* 0 + S m = S m = S (0 + m) *)
  - rewrite IH. reflexivity.             (* S n + S m = S (n + S m) → S (S (n + m)) *)
Qed.

(** Úloha 6 ★  
    Dokážte, že ak `n + n = m + m`, potom `n = m`. *)
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n m H.

  generalize dependent m.
  induction n as [| n IH]; intros m H; destruct m as [| m].
  - reflexivity.
  - simpl in H. discriminate.
  - simpl in H. discriminate.
  - simpl in H.
  injection H as H.
  rewrite add_succ_r in H.
  rewrite add_succ_r in H.
  apply (f_equal pred) in H. 
  simpl in H.
  apply IH in H.
  f_equal.
  apply H.
Qed.



(** Úloha 7 ★  
    Dokážte, že ak `length l = n`, potom `nth_error l n = None`. *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros.
  subst n.
  induction l as [| x l IH]; simpl.
  reflexivity.
  apply IH.
Qed.


(** Úloha 8 ★  
    Dokážte, že pre ľubovoľnú booleovskú funkciu `f` platí `f (f (f b)) = f b`. *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
 intros f b.
  destruct (f true)  eqn:E1;
  destruct (f false) eqn:E2;
  destruct b; repeat (rewrite E1 || rewrite E2); reflexivity.

Qed.


(** Úloha 9 ★  
    Dokážte symetriu `eqb`: `(n =? m) = (m =? n)`. *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
 induction n as [| n IH]; intros m.
  - destruct m; reflexivity.
  - destruct m; simpl; [reflexivity | apply IH].
Qed.


Lemma eqb_refl : forall p : nat, (p =? p) = true.
Proof.
  induction p as [|p IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(** Úloha 10 ★  
    Dokážte tranzitivitu `eqb`: ak `n =? m = true` a `m =? p = true`,
    potom `n =? p = true`. *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof. 
  intros n m p Hnm Hmp.
  (* turn booleans into equalities *)
  apply eqb_true in Hnm.     (* Hnm : n = m *)
  apply eqb_true in Hmp.     (* Hmp : m = p *)
  rewrite <- Hnm in Hmp.        (* Hmp : n = p *)
  rewrite Hmp.               (* goal: p =? p = true *)
  
  apply eqb_refl.
Qed.


(** Úloha 11 ★  
    Dokážte, že ak `filter test l = x :: lf`, tak `test x = true`. *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof. 
  intros X test x l lf H.
  generalize dependent x. generalize dependent lf.
  induction l as [| y l' IH]; intros lf x H; simpl in H.
  - discriminate.
  - destruct (test y) eqn:Hy.
    + injection H as Hhead Htail.
      subst y lf.
      exact Hy.
    + apply IH in H. exact H.
Qed.



(** Úloha 12 ★  
    Dokážte, že ak `n + m = 0`, potom `n = 0` a `m = 0`. *)
Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  destruct n as [| n']; destruct m as [| m']; simpl in H.
  - split; reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.


(** Úloha 13 ★  
    Dokážte komutatívnosť konjunkcie: `P /\ Q -> Q /\ P`. *)
Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof. 
  intros.
  destruct H.
  split.
  assumption.
  assumption.
Qed.


(** Úloha 14 ★  
    Dokážte asociativitu konjunkcie: `P /\ (Q /\ R) -> (P /\ Q) /\ R`. *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof. 
  intros.
  destruct H.
  split.
  destruct H0.
  split.
  assumption.
  assumption.
  destruct H0.
  assumption.
Qed.


(** Úloha 15 ★  
    Dokážte, že ak `n * m = 0`, potom `n = 0 \/ m = 0`. *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. 
  intros.
  destruct n.
  - left; reflexivity.
  - destruct m.
    + right; reflexivity.
    + simpl in H. discriminate H.
Qed.


(** Úloha 16 ★  
    Dokážte komutatívnosť disjunkcie: `P \/ Q -> Q \/ P`. *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof. 
  intros.
  destruct H.
  - right. exact H.
  - left. exact H.
Qed.


(** Úloha 17 ★  
    Dokážte kontrapozíciu: `(P -> Q) -> (~Q -> ~P)`. *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof. 
  intros P Q HPQ HnQ HP.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.


(** Úloha 18 ★  
    Dokážte, že nemožno mať `P` aj `~P` zároveň: `~ (P /\ ~P)`. *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P H.
  destruct H.
  contradiction.
Qed.


(** Úloha 19 ★  
    Dokážte De Morganov zákon: `~ (P \/ Q) -> ~P /\ ~Q`. *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H.
  split.
  - unfold not. intros HP. apply H. left. exact HP.
  - unfold not. intros HQ. apply H. right. exact HQ.
Qed.


(** Úloha 20 ★  
    Dokážte, že neplatí `forall n, S (pred n) = n`. *)
Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof. 
  unfold not.
  intros H.
  specialize (H 0).
  simpl in H.
  discriminate H.
Qed.


(** Úloha 21 ★  
    Dokážte, že prázdny zoznam nie je tvaru `x :: xs`. *)
Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof. 
  intros X x xs H.
  discriminate.
Qed.

(** Úloha 22 ★  
    Dokážte, že ekvivalencia je reflexívna: `P <-> P`. *)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof. 
  intros.
  split.
  intros H.
  apply H.
  intros H.
  apply H.
Qed.


(** Úloha 23 ★  
    Dokážte tranzitivitu ekvivalencie:  
    ak `P <-> Q` a `Q <-> R`, potom `P <-> R`. *)
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. 
  intros.
  destruct H.
  destruct H0.
  split.
  intros HP.
  apply H0.
  apply H.
  apply HP.
  intros HR.
  apply H1.
  apply H2.
  apply HR.
Qed.


(** Úloha 24 ★  
    Dokážte distribučný zákon: `P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)`. *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros H.
    destruct H as [HP | [HQ HR]].
    + split; left; exact HP.
    + split; [right; exact HQ | right; exact HR].
  - intros [H1 H2].
    destruct H1 as [HP | HQ].
    + left; exact HP.
    + destruct H2 as [HP | HR].
      * left; exact HP.
      * right; split; assumption.
Qed.


(** Úloha 25 ★  
    Dokážte, že ak `P x` platí pre všetky `x`, tak neexistuje `x`, pre ktorý `~P x`. *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros X P H.
  unfold not.
  intros [x HnotPx].
  apply HnotPx.
  apply H.
Qed.


(** Úloha 26 ★  
    Dokážte, že existencia disjunkcie sa rozdeľuje:  
    `(exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x)`. *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. 
   intros X P Q; split.
  - intros [x [HP | HQ]].
    + left;  exists x; exact HP.
    + right; exists x; exact HQ.
  - intros [HexP | HexQ].
    + destruct HexP as [x HP]. exists x. left;  exact HP.
    + destruct HexQ as [x HQ]. exists x. right; exact HQ.
Qed.



(** Úloha 27 ★  
    Dokážte, že ak `n <=? m = true`, potom existuje `x` s `m = n + x`. *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof. 
  intros n m H. generalize dependent m.
  induction n as [| n IH]; intros m H.
  - exists m. simpl. reflexivity.
  - destruct m as [| m'].
    + simpl in H. discriminate.
    + simpl in H.
      apply IH in H.
      destruct H as [x Hx].
      exists x.
      simpl. rewrite Hx. reflexivity.
Qed.


(** Úloha 28 ★  
    Dokážte, že ak `m = n + x` pre nejaké `x`, potom `n <=? m = true`. *)
Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros n m [x H]. subst m.
  revert n.
  induction x as [| x IH]; intros n.
  - induction n as [| n' IHn]; simpl; auto.
  - destruct n as [| n']; simpl.
    + reflexivity.
    + induction n' as [| k IHk]; simpl; auto.
Qed.

