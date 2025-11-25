(*********************************************)
(** 2. odovzdávka zadania: Jazyk NBL        **)
(*********************************************)

(*        Import potrebných knižníc         *) 

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Init.Nat.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.


(*============================================*)
(** NBL: Jazyk čísel a pravdivostných hodnôt **)
(*============================================*)
Module nbl.

(*--------------------------------------------*)
(** Syntax *)
Inductive nbl : Type := 
| tru : nbl
| fls : nbl
| zro : nbl
| iszro : nbl -> nbl
| prede : nbl -> nbl
| scc : nbl -> nbl
| ite : nbl -> nbl -> nbl -> nbl.

(*--------------------------------------------*)
(** Notácia pre konkrátnu syntax              *)

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := 
  (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := 
  false (at level 1): tm_scope.
Notation "'false'" := 
  (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := 
  e (e custom tm at level 99): tm_scope.
Notation "( x )" := 
  x (in custom tm, x at level 99): tm_scope.
Notation "x" := 
  x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := 
  (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 
  0 (at level 1): tm_scope.
Notation "'succ' x" := 
  (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := 
  (prede x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := 
  (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := 
  (ite c t e)
    (in custom tm at level 90, c custom tm at level 80,
    t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(*--------------------------------------------*)
(** Hodnoty jazyka NBL                        *)

Inductive bval : nbl -> Prop := 
| bvtrue : bval tru
| bvfalse : bval fls.

Inductive nval : nbl -> Prop := 
| nv0 : nval zro
| nvscc : forall t, nval t -> nval (scc t).

(** Normálna forma termov je hodnota *)
Definition value (t : nbl) := nval t \/ bval t.


(*-----------------------------------------------*)
(** Štrukturálna operačná sémantika ako relácia  *)

Reserved Notation "t '-->' t'" (at level 40).
Inductive smallstep : nbl -> nbl -> Prop :=
  | st_iftrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | st_iffalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | st_if : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | st_succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | st_pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | st_predsucc : forall v,
      nval v ->
      <{ pred (succ v) }> --> v
  | st_pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | st_iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | st_iszeronv : forall v,
       nval v ->
      <{ iszero (succ v) }> --> <{ false }>
  | st_iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
where "t '-->' t'" := (smallstep t t').
Hint Constructors smallstep : core.

(*---------------------------------------------*)
(** Reflexívno-tranzitívny uzáver (multi-step) *)

Inductive multistep : nbl -> nbl -> Prop :=
  | multi_refl : forall t, multistep t t  
  | multi_tran : forall t1 t2 t3,
      smallstep t1 t2 ->  
      multistep t2 t3 ->
      multistep t1 t3.

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Hint Constructors multistep : core.

(*--------------------------------------------*)
(** Normálne formy                            *)
Definition normal_form (t : nbl) : Prop :=
   ~exists t', smallstep t t'.


(*--------------------------------------------*)
(** Typový systém                             *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Declare Custom Entry ty.
Notation "'Nat'" := Nat (in custom ty).
Notation "'Bool'" := Bool (in custom ty).
Notation "x" := x (in custom ty, x global).

Reserved Notation "<{ '|--' t 'of' T }>"
            (at level 0, t custom tm, T custom ty).

Inductive typed : nbl -> ty -> Prop :=
  | t_true : 
       <{ |-- true of Bool }>
  | t_false :
       <{ |-- false of Bool }>
  | t_if : forall t1 t2 t3 T,
       <{ |-- t1 of Bool }> ->
       <{ |-- t2 of T }> ->
       <{ |-- t3 of T }> ->
       <{ |-- if t1 then t2 else t3 of T }>
  | t_0 :
       <{ |-- 0 of Nat }>
  | t_succ : forall t1,
       <{ |-- t1 of Nat }> ->
       <{ |-- succ t1 of Nat }>
  | t_pred : forall t1,
       <{ |-- t1 of Nat }> ->
       <{ |-- pred t1 of Nat }>
  | t_iszero : forall t1,
       <{ |-- t1 of Nat }> ->
       <{ |-- iszero t1 of Bool }>

where "<{ '|--' t 'of' T }>" := (typed t T).
Hint Constructors typed : core.


(*--------------------------------------------*)
(** Veta o jednoznačnosť typu                 *)

Theorem type_uniqueness: forall t T1 T2, 
        <{ |-- t of T1 }> /\ <{ |-- t of T2 }> -> T1 = T2.
Proof.
  intros.
  destruct H as [HT1 HT2].   
  (* rozdelíme konjunkciu na dva predpoklady *)
  induction t. 
  (* dôkaz indukciou podľa štruktúry termu t *)
  - (* prípad: t = true *)
    inversion HT1. inversion HT2. reflexivity.
    (** využitím vety o inverzii odvodíme, 
        že ak  <{ |-- true of T }>, tak T je Bool*)
  - (* prípad: t = false *)
    inversion HT1. inversion HT2. reflexivity.
    (** rovnaké zdôvodnenie ako vyššie *)
  - (* prípad: t = 0 *)
    inversion HT1. inversion HT2. reflexivity.
    (** nula má vždy typ [Nat]. *)
  - (* prípad: t = succ t1 *)
    inversion HT1. inversion HT2. reflexivity.
    (** inverzia na typovom pravidle pre iszero, 
        potom T musí Nat *)
  - (* prípad: t = pred t1 *)
    inversion HT1. inversion HT2. reflexivity.
    (** rovnaké zdôvodnenie ako vyššie *)
  - (* prípad: t = iszero t1 *)
    inversion HT1. inversion HT2. reflexivity.
    (** test [iszero] má vždy výsledok typu [Bool]. *)
  - (* prípad: t = if t1 then t2 else t3 *)
    inversion HT1; subst.
    inversion HT2; subst.
    apply IHt2; assumption.
Qed.

(*--------------------------------------------*)
(** Vety o kanonických hodnotách              *)

Lemma bool_canomical : forall t, 
      <{|-- t of Bool}> /\ value t -> bval t.
Proof.
  intros.
  unfold value in H.            
  (* rozbalíme definíciu hodnoty *)
  destruct H as [Ht Hbv].       
  (* rozdelíme konjunkciu typovej relácie
    a výroku, že t je hodnota *)
  destruct Hbv as [Hnv | Hbv].       
  (* hodnota môže byť nval alebo bval *)
  - inversion Hnv. subst.
    + inversion Ht.                  
    (* t = 0, ale 0 má typ Nat, nie Bool *)
    + subst. inversion Ht.
    (* t = succ t má typ Nat, nie Bool *)
  - apply Hbv.                       
  (* t boolean hodnota *)
Qed.


Lemma nat_canomical : forall t, 
      <{|-- t of Nat}> /\ value t -> nval t.
Proof.
  intros.
  destruct H as [Ha Hb].
  unfold value in Hb.
  destruct Hb as [Hnv | Hbv].
  - apply Hnv.                       
  (* ak je t číselná hodnota, hotovo *)
  - inversion Hbv. subst.
    inversion Ha. subst.
    inversion Ha.
Qed.


(*--------------------------------------------*)
(**     Dôkaz bezbečnosti jazyka NBL:         *)
(**     Veta o progresii a stabilite          *)


Theorem progress: forall t T, 
        <{ |-- t of T}> -> (value t) \/ exists t', (t --> t').
Proof.
intros.
(** Dôkaz indukciou nad typovou reláciou *)
induction H. 
  (** true *)
- left. unfold value. right. apply bvtrue.
  (** false *)
- left. unfold value. right. apply bvfalse.
  (** if t1 then t2 else t3  *)
- right. destruct IHtyped1. 
  + assert (Hb : bval t1).
    { apply (bool_canomical t1). split; assumption. } 
    inversion Hb. subst.  
    * exists t2. apply st_iftrue.
    * exists t3. apply st_iffalse.  
  + destruct H2 as [t1' Hstep]. 
    exists (<{if t1' then t2 else t3}>). 
    apply st_if. assumption.
  (** 0 *)
- left. unfold value. left. apply nv0.
  (** succ t1 *)
- destruct IHtyped. 
 + left. assert (nval t1) as Hn.
    { apply (nat_canomical t1). 
      split. apply H. apply H0. }
    unfold value. left. apply nvscc. apply Hn.
 + right. destruct H0 as [t' Hstep]. 
   exists (scc t'). 
   apply st_succ. apply Hstep.
  (** pred t1 *)
- destruct IHtyped as [Hv | [t' Hstep]]. 
  + destruct (nat_canomical t1). 
    split. assumption. assumption. 
    right. exists zro. apply st_pred0.   
    right. exists t. apply st_predsucc. assumption.
  + right. exists (prede t'). apply st_pred. assumption.
  (** iszero t1 *) 
- destruct IHtyped as [Hv | [t' Hstep]]. 
 + destruct (nat_canomical t1). split. 
    * assumption.
    * assumption.
    * right. exists tru. apply st_iszero0.
    * right. exists fls. apply st_iszeronv. assumption.
 + right. exists (iszro t'). apply st_iszero. assumption.
Qed.  


(** Indukcia na typovej relácii: *)
Theorem preservation: forall t t' T, 
        <{|-- t of T}> /\ (t-->t') ->  <{|-- t' of T}>.
intros.
destruct H. 
(** rozdelenie konjunkcie na typová a vyhodnocovaciu reláciu *)
generalize dependent t'.
induction H; intros t' Hstep; 
inversion Hstep; subst; try assumption.
(* if-true/false *)
- apply t_if.
  + apply IHtyped1. assumption.
  + assumption.
  + assumption.
(* succ *)
- apply t_succ. apply IHtyped in H1. assumption. 
(* pred 0 *)
- inversion H. assumption.
(* pred *)
- apply t_pred. apply IHtyped. assumption. 
(* true *)
- apply t_true. 
(* false *)
- apply t_false.
(* iszero *)
- apply t_iszero. apply IHtyped. apply H1.
Qed.


(*-------------------------------------------*)
(** Úlohy:                                   *)
(*-------------------------------------------*)

(** Úloha 1 ★ Dokážte, nasledujúcu teorému. *)
Theorem ex_smallstep : 
  multistep <{
    if (iszero 0) 
      then 
        (if true then pred 0 else succ 0) 
      else 
        if iszero (succ (pred 0)) then 0 else succ 0 }> <{0}>.
Proof.
  eapply multi_tran. {

      apply st_if. apply st_iszero0.
    }
    eapply multi_tran. {

      apply st_iftrue.
    }
    eapply multi_tran. {

      apply st_iftrue.
    }
    eapply multi_tran. {

      apply st_pred0.
    }
    (* done *)
    apply multi_refl.
Qed.

(** Úloha 2 ★ Dokážte, nasledujúcu teorému. *)
Theorem ex_well_typed: 
<{|-- if (iszero 0) 
        then 
          (if true then pred 0 else succ 0) 
        else 
          if iszero (succ (pred 0)) then 0 else succ 0  of Nat }>.
Proof.
 apply t_if.
  - 
    apply t_iszero. apply t_0.
  - 
    apply t_if.
    + apply t_true.
    + apply t_pred. apply t_0.
    + apply t_succ. apply t_0.
  -
    apply t_if.
    + apply t_iszero. apply t_succ. apply t_pred. apply t_0.
    + apply t_0.
    + apply t_succ. apply t_0.
Qed.

(** Úloha 3 ★ Dokážte, nasledujúcu teorému. *)
Theorem ex_not_well_typed: 
~ <{|-- if (iszero 0) 
        then 
          (if true then pred 0 else succ 0) 
        else 
          if iszero (succ (pred 0)) then 0 else succ 0  of Bool }>.
Proof.
  intro H.
  inversion H; subst.
  (* from the outer if: the then-branch must be Bool *)
  inversion H5; subst.
  (* now H8 : <{|-- pred 0 of Bool }> *)
  assert (Hnat : <{|-- pred 0 of Nat }>) by (apply t_pred, t_0).

  (* use type_uniqueness positionally, no named args *)
  pose proof (type_uniqueness <{ pred 0 }> Nat Bool (conj Hnat H8)) as Heq.
  inversion Heq.  (* or: discriminate Heq. *)
Qed.


(** Úloha 4 ★ 
Dokážte teorému o zachovaní typu indukciou na vyhodnocovacej relácii.
*)
Theorem preservation': forall t t' T, 
        <{|-- t of T}> /\ (t-->t') ->  <{|-- t' of T}>.
Proof.
   intros. destruct H as [Ht Hr].
  generalize dependent T.
  induction Hr; intros T HT; inversion HT; subst.
  - 
    assumption.
  - 
    assumption.
  - 
    apply t_if.
    + apply IHHr. assumption.
    + assumption.
    + assumption.
  - 
    apply t_succ. apply IHHr. assumption.
  - 
    apply t_0.
  - 
    match goal with
    | Hs : <{|-- succ _ of Nat }>|- _ =>
        inversion Hs; subst; assumption
    end.
  - 
    apply t_pred. apply IHHr. assumption.
  - 
    apply t_true.
  - 
    apply t_false.
  - 
    apply t_iszero. apply IHHr. assumption.
Qed.



(*================================================*)
(** Štrukturálna operačná sémantika  *)

(** 
V predchádzajúcej časti bola definovaná 
štrukturálná operačná sémantika pre jazyk NBL
ako relácia:

        t --> t'

Táto relácia popisuje jeden krok redukcie
(tzv. *small-step* sémantiku),
kde [t] sa redukuje na [t'] 
podľa niektorého z pravidiel definície [smallstep].

V tejto úlohe vytvoríte funkciu, 
ktorá sa správa ekvivalentne k relačnej definícii.
*)

(*---------------------------------*)
(** ** Pomocné funkcie: Hodnoty    *)
(*---------------------------------*)

Fixpoint isnumericval (t : nbl) : bool :=
  match t with
  | zro => true
  | scc t1 => isnumericval t1
  | _ => false
  end.

Definition isval (t : nbl) : bool :=
  match t with
  | tru => true
  | fls => true
  | _ => isnumericval t
  end.



(* Úloha 5 ★ Implementujte funkciu [evalsmallstep] *)

Fixpoint evalsmallstep (t : nbl) : option nbl :=
match t with
  | tru => None
  | fls => None
  | zro => None

  | scc t1 =>
      match evalsmallstep t1 with
      | Some t1' => Some (scc t1')
      | None => None
      end

  | prede t1 =>
      match t1 with
      | zro => Some zro                                  (* st_pred0 *)
      | scc v =>
          if isnumericval v then Some v                         (* st_predsucc *)
          else match evalsmallstep t1 with               (* st_pred *)
               | Some t1' => Some (prede t1')
               | None => None
               end
      | _ =>
          match evalsmallstep t1 with                    (* st_pred *)
          | Some t1' => Some (prede t1')
          | None => None
          end
      end

  | iszro t1 =>
      match t1 with
      | zro => Some tru                                  (* st_iszero0 *)
      | scc v =>
          if isnumericval v then Some fls                       (* st_iszeronv *)
          else match evalsmallstep t1 with               (* st_iszero *)
               | Some t1' => Some (iszro t1')
               | None => None
               end
      | _ =>
          match evalsmallstep t1 with                    (* st_iszero *)
          | Some t1' => Some (iszro t1')
          | None => None
          end
      end

  | ite c t2 t3 =>
      match c with
      | tru => Some t2                                   (* st_iftrue  *)
      | fls => Some t3                                   (* st_iffalse *)
      | _ =>
          match evalsmallstep c with                     (* st_if *)
          | Some c' => Some (ite c' t2 t3)
          | None => None
          end
      end
  end.
(*---------------------------------------------------------------*)
(** ** Testy a overenie                                           *)
(*---------------------------------------------------------------*)
Example test_eval1 :
  evalsmallstep <{ if true then 0 else (succ 0) }> = Some <{ 0 }>.
Proof.
  auto. 
Qed.

Example test_eval2 :
  evalsmallstep <{ pred (succ (succ 0)) }> = Some <{ succ 0 }>.
Proof.
auto.
Qed.

Example test_eval3 :
  evalsmallstep <{ iszero (succ 0) }> = Some <{ false }>.
Proof. 
auto.
Qed.

(** 
Po správnej implementácii by sa mala vaša funkcia 
správať ekvivalentne k relácii [smallstep]. 
*)

(** Bonusová úloha 1 ★ 

Dokážte, že vaša funkcia je ekvivalentná s relačnou definíciou:
*)
Theorem evalsmallstep_equiv : forall t t',
    (t --> t') <-> (evalsmallstep t = Some t').
Proof. 
Admitted.


(*===============================================================*)
(**       Prirodzená (big-step) operačná sémantika               *)
(*===============================================================*)

(** 
V tejto úlohe rozšírime náš jazyk o definíciu
prirodzenej operačnej sémantiky (big-step semantics).

Táto sémantika opisuje celý výpočet
(od vstupného termu až po výslednú hodnotu),
na rozdiel od štrukturálnej (small-step), 
ktorá opisuje iba jeden krok výpočtu.
*)

(*---------------------------------------------------------------*)
(** Vyhodnocovacia relácia (big-step)                         *)
(*---------------------------------------------------------------*)

(** Značenie vyhodnocovania:

        t ==> v

    znamená, že term [t] sa vyhodnotí na hodnotu [v]
    podľa pravidiel prirodzenej sémantiky.
*)

Reserved Notation "t '==>' t'" (at level 40).

(** Definujte induktívnu reláciu [bigstep : nbl -> nbl -> Prop],
    ktorá reprezentuje pravidlá prirodzenej operačnej sémantiky.

    Použite nasledujúce pravidlá:


    t ==> v₂
-------------- (b_value)
    v₁ ==> v₂


    t₁ ==> true     t₂ ==> v₃
------------------------------ (b_iftrue)
    if t₁ then t₂ else t₃ ==> v₃


    t₁ ==> false    t₃ ==> v₃
------------------------------ (b_iffalse)
    if t₁ then t₂ else t₃ ==> v₃


    t₁ ==> nv₁
----------------------- (b_succ)
    succ t₁ ==> succ nv₁


    t₁ ==> 0
----------------- (b_predzero)
    pred t₁ ==> 0


    t₁ ==> succ nv₁
--------------------- (b_predsucc)
    pred t₁ ==> nv₁


    t₁ ==> 0
--------------------- (b_iszerozero)
    iszero t₁ ==> true


    t₁ ==> succ nv₁
----------------------- (b_iszerosucc)
    iszero t₁ ==> false

*)

(** Úloha 6 ★
Doplňte definíciu relácie bigstep podľa vyššie uvedených pravidiel. 
- Ako názvy konštruktorov použite názvy pravidiel.
*)
Inductive bigstep : nbl -> nbl -> Prop :=
  | b_value : forall v,
      value v ->
      v ==> v
  | b_iftrue : forall t1 t2 t3 v3,
      t1 ==> tru ->
      t2 ==> v3 ->
      <{ if t1 then t2 else t3 }> ==> v3
  | b_iffalse : forall t1 t2 t3 v3,
      t1 ==> fls ->
      t3 ==> v3 ->
      <{ if t1 then t2 else t3 }> ==> v3
  | b_succ : forall t1 nv1,
      t1 ==> nv1 ->
      nval nv1 ->
      <{ succ t1 }> ==> <{ succ nv1 }>
  | b_predzero : forall t1,
      t1 ==> zro ->
      <{ pred t1 }> ==> zro
  | b_predsucc : forall t1 nv1,
      t1 ==> <{ succ nv1 }> ->
      nval nv1 ->
      <{ pred t1 }> ==> nv1
  | b_iszerozero : forall t1,
      t1 ==> zro ->
      <{ iszero t1 }> ==> tru
  | b_iszerosucc : forall t1 nv1,
      t1 ==> <{ succ nv1 }> ->
      nval nv1 ->
      <{ iszero t1 }> ==> fls
where "t '==>' t'" := (bigstep t t').

Hint Constructors bigstep : core.

(*---------------------------------------------------------------*)
(** ** Funkčná verzia: [evalbigstep]                             *)
(*---------------------------------------------------------------*)

(** 
Implementujte funkciu prirodzenej sémantiky [evalbigstep],
ktorá pre daný term [t] rekurzívne vyhodnotí 
celý výraz a vráti [Some v],
ak sa term vyhodnotí na hodnotu [v], inak [None].

Napríklad:

  evalbigstep <{ if true then 0 else (succ 0) }> = Some 0
  evalbigstep <{ pred (succ 0) }> = Some 0
*)

(** Úloha 7 ★ 
Doplňte definíciu funkcie evalbigstep podľa vyššie 
uvedených pravidiel.
    *)
Fixpoint evalbigstep (t : nbl) : option nbl :=
match t with
  | tru => Some tru
  | fls => Some fls
  | zro => Some zro

  | scc t1 =>
      match evalbigstep t1 with
      | Some v1 =>
          if isnumericval v1 then Some (scc v1)  (* b_succ *)
          else None
      | None => None
      end

  | prede t1 =>
      match evalbigstep t1 with
      | Some zro => Some zro              (* b_predzero *)
      | Some (scc v) =>
          if isnumericval v then Some v          (* b_predsucc *)
          else None
      | _ => None
      end

  | iszro t1 =>
      match evalbigstep t1 with
      | Some zro => Some tru              (* b_iszerozero *)
      | Some (scc v) =>
          if isnumericval v then Some fls        (* b_iszerosucc *)
          else None
      | _ => None
      end

  | ite c t2 t3 =>
      match evalbigstep c with
      | Some tru => evalbigstep t2        (* b_iftrue *)
      | Some fls => evalbigstep t3        (* b_iffalse *)
      | _ => None
      end
  end.

(*--------------------------------------*)
(** ** Testovanie                       *)
(*--------------------------------------*)

(** Otestujte správanie funkcie [evalbigstep] 
    na jednoduchých výrazoch. *)

Compute (evalbigstep <{ if true then 0 else (succ 0) }>).
(* Očakávaný výsledok: Some 0 *)

Compute (evalbigstep <{ pred (succ (succ 0)) }>).
(* Očakávaný výsledok: Some (succ 0) *)

Compute (evalbigstep <{ iszero (succ 0) }>).
(* Očakávaný výsledok: Some false *)

Example test_big1 :
  evalbigstep <{ if false then 0 else (succ 0) }> = Some <{ succ 0 }>.
Proof. 
auto.
Qed.

Example test_big2 :
  evalbigstep <{ pred (succ (succ 0)) }> = Some <{ succ 0 }>.
Proof. 
auto.
Qed.

Example test_big3 :
  evalbigstep <{ iszero (succ 0) }> = Some <{ false }>.
Proof.
auto.
Qed.

(** Bonusová úloha 2 ★ 
Dokážte ekvivalenciu medzi relačnou a funkčnou
verziou prirodzenej operačnej sémantiky (big-step). *)
Theorem evalbigstep_correct : forall t v,
  evalbigstep t = Some v <-> t ==> v.
Proof.
Admitted.

(*-----------------------------------*)
(** Ekvivalencia sémantických metód  *)
(*-----------------------------------*)

(** Bonusová úloha 3 ★ 
Dokážte, že prirodzená a štrukturálna operačná sémantika 
sú ekvivalentné:
*)
Theorem bigstep_smallstep_equiv :
forall t v,
    (t ==> v) <-> (t -->* v /\ isval v = true).
Admitted.

(*---------------------------------*)
(** Typový systém                  *)
(*---------------------------------*)

(** Úloha 8 ★ Definujte funkciu typedb, ktorá overí, 
či term je správne typovaný. 
*)

Fixpoint typedb (t : nbl) (T : ty) : bool :=
  match t with
  | tru =>
      match T with
      | Bool => true
      | _ => false
      end
  | fls =>
      match T with
      | Bool => true
      | _ => false
      end
  | zro =>
      match T with
      | Nat => true
      | _ => false
      end
  | scc t1 =>
      match T with
      | Nat => typedb t1 Nat
      | _ => false
      end
  | prede t1 =>
      match T with
      | Nat => typedb t1 Nat
      | _ => false
      end
  | iszro t1 =>
      match T with
      | Bool => typedb t1 Nat
      | _ => false
      end
  | ite c t2 t3 =>
      andb (typedb c Bool)
           (andb (typedb t2 T) (typedb t3 T))
  end.

(*--------------------------------------------*)
(** testy *)
Example typedb_example1 :
  typedb <{ if true then 0 else 0 }> Nat = true.
Proof. auto. Qed.

Example typedb_example2 :
  typedb <{ if true then 0 else false }> Nat = false.
Proof. auto. Qed.


(** Bonusová úloha 4 ★  
Dokážte ekvivalenciu medzi reláciou typed 
a funkciou typedb
*)
Theorem typing_Equal: 
forall t T, <{ |-- t of T }> <-> typedb t T = true.
Proof.
Admitted.  

End nbl.
