Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
Set Default Goal Selector "!".

(*============================================*)
(** STLC Syntax **)
(*============================================*)
Module STLC.

(* ================================================ *)
(** ** Typy *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================ *)
(** ** Termy *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

(** Zavedieme podporú konkrétnej syntaxe 
    prostredníctvom príkazu Notation *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

(** Notácia pre Typy *)
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

Notation "'Bool'" := 
Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.

(** Typy budeme uvádzať [<{{ ... }}>] zátvorkach: *)
Check <{{ Bool }}>.
Check <{{ Bool -> Bool }}>.
Check <{{ (Bool -> Bool) -> Bool }}>.


(** Notácia pre Termy *)
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

Notation "$( x )" := 
x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := 
x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := 
e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := 
x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := 
(tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Notation idB :=
  <{ \x:Bool, x }>.

Notation idBB :=
  <{ \x:Bool->Bool, x }>.

Notation idBBBB :=
  <{ \x: (Bool->Bool)->(Bool->Bool), x}>.

Notation k := 
    <{ \x:Bool, \y:Bool, x }>.

Notation notB := 
    <{ \x:Bool, if x then false else true }>.

(* ################################################ *)
(** === Hodnoty === *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value <{\x:T, t}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.


(* ################################################ *)
(**  Substitúcia *)

Reserved Notation "'[' x ':=' s ']' t" 
    (in custom stlc_tm at level 5, x global, 
    s custom stlc_tm, t custom stlc_tm at next level, 
    right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := 
    (subst x s t) (in custom stlc_tm).

(* ################################################ *)
(** Redukcia *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{[x:=v2]t1}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.


Inductive multistep : tm -> tm -> Prop :=
  | multi_refl : forall t, multistep t t  
  | multi_tran : forall t1 t2 t3,
      step t1 t2 ->  
      multistep t2 t3 ->
      multistep t1 t3.

Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(* ################################################ *)
(** * Typový systém *)

(* ================================================ *)
(** ** Kontext *)


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

(* ================================================ *)
(** ** Typová relácia *)

Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, 
  v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
(in custom stlc_tm at level 0, x constr at level 0, 
v custom stlc_ty) : stlc_scope.

Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
(at level 0, Gamma custom stlc_tm at level 200, 
t custom stlc_tm, T custom stlc_ty).

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
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
       <{ Gamma |-- t1 \in Bool }> ->
       <{ Gamma |-- t2 \in T1 }> ->
       <{ Gamma |-- t3 \in T1 }> ->
       <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := 
  (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.

(*===================================================*)
(** Pomocné vety o zobrazeniach                      *)
(*===================================================*)

(** ----------------------------------------------- **)
(** Úloha 1 ★ Dokážte, nasledujúcu teorému. *)
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
 intros A m x v. unfold t_update.
  destruct (String.eqb x x) eqn:E; [reflexivity|].
  (* druhá vetva je nemožná: x <> x *)
  apply String.eqb_neq in E; congruence.
Qed.
(** [] *)

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

(** ----------------------------------------------- **)
(** Úloha 2 ★ Dokážte, nasledujúcu teorému. *)
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v Hneq.
  unfold t_update.
  destruct (String.eqb x1 x2) eqn:E.
  - apply String.eqb_eq in E; contradiction.
  - reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.

From Coq Require Import Logic.FunctionalExtensionality.

(** ----------------------------------------------- **)
(** Úloha 3 ★ Dokážte, nasledujúcu teorému. *)
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
 intros A m x v1 v2.
  unfold t_update.
  apply functional_extensionality; intro x'.

  destruct (String.eqb x x') eqn:E; reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.


(** ----------------------------------------------- **)
(** Úloha 4 ★ Dokážte, nasledujúcu teorému. *)
Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 Hneq.
  apply functional_extensionality; intro x.
  unfold t_update.
  destruct (String.eqb x1 x) eqn:E1;
  destruct (String.eqb x2 x) eqn:E2; simpl; try reflexivity.
  apply String.eqb_eq in E1.
  apply String.eqb_eq in E2.
  exfalso.
  apply Hneq.
  rewrite E2. symmetry. exact E1.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.


(*===================================================*)
(** Vlastnosti STLC                                  *)
(*===================================================*)

(** * Kanonické formy

Prvým krokom je určiť možné kanonické formy (t. j. správne
typované hodnoty) pre jednotlivé typy.  
  - Pre [Bool]: hodnoty [true] a [false]  
  - Pre funkčný typ ([T1 -> T2]): lambda-abstrakcie.

Tieto vety platia pre termy, ktoré sú správne typované a 
zároveň uzavreté (v prázdnom kontexte). *)


Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

(* ################################################# *)
(** * Progress
Veta o progrese hovorí, že uzavreté, správne typované termy
„sa nezaseknú“: každý taký term je buď hodnota, alebo sa môže
redukovať o jeden krok.
*)


Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
(** * Dôkaz (Progres)  
    Dôkaz indukciouv na typovej relácii  [|-- t \in T].
 *)
Proof with eauto.
(** 
  Použitie [Proof with eauto]: 
  umožňuje automaticky aplikovať [eauto] 
  všade, kde je to vhodné, pomocou trojbodky [...].  
  Hodí sa najmä pri indukcii alebo slučkách, kde zvyšok dôkazu 
  môže vyriešiť automaticky.
*)
intros t T Ht.
(* Pomenovanie prázdneho kontextu [empty] ako [Gamma] 
   pre jednoduchšiu manipuláciu v dôkaze.*)
remember empty as Gamma.
induction Ht; subst Gamma; auto.
(* [auto] automaticky vyrieši všetky prípady, kde je [t] hodnota. *)

- (* T_Var *)
  (* kontradikcia: premenné nemôžu byť správne typované 
     v prázdnom kontexte. *)
  discriminate H.

- (* T_App *)
  (* [t] = [t1 t2]. [t1] je hodnota alebo sa môže redukovať *)
  right. destruct IHHt1...
  + (* t1 je hodnota *)
    destruct IHHt2...
    * (* t2 je tiež hodnota *)
      eapply canonical_forms_fun in Ht1; [|assumption].
      destruct Ht1 as [x [t0 H1]]. subst.
      exists (<{ [x:=t2]t0 }>). apply ST_AppAbs. assumption.
(** pre ukončenie predchadzajúcej vetvy 
    bolo dostačné použiť taktiku eauto v tvare ...  *)
    * (* t2 je možné redukovať *)
      destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...
  + (* t1 je možné redukovať *)
    destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

- (* T_If *)
  right. destruct IHHt1...
  + (* t1 je hodnota *)
    destruct (canonical_forms_bool t1); subst; eauto.
  + (* t1 je možné redukovať *)
    destruct H as [t1' Hstp]. 
    exists <{if t1' then t2 else t3}>...
Qed.


(** ----------------------------------------------- **)
(** Úloha 5 ★ Dokážte, nasledujúcu teorému. *)
(*
Ukážte, že vetu o progresii (progress) je možné dokázať aj
indukciou na termoch [t], namiesto indukcie na typovej relácii
  [|-- t \in T].

Nápoveda: pri indukcii na termoch budete rozdeľovať prípady 
podľa konštruktorov termov  (napr. [tvar], [tabs], [tapp], [tif]), 
potom použite indukčný predpoklad na podtermy a 
vety o kanonických formách.
*)

Theorem progress' : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
Proof.
  induction t; intros T HT; eauto.
  - (* tm_var *)
    inversion HT; subst.
    match goal with
    | Hget : empty _ = Some _ |- _ =>
        unfold empty in Hget; simpl in Hget; discriminate
    end.
  - (* tm_app *)
    inversion HT; subst.
    assert (has_type empty t1 (Ty_Arrow T2 T)) as Hfun by eauto.
    assert (has_type empty t2 T2)             as Harr by eauto.
    specialize (IHt1 _ Hfun).
    specialize (IHt2 _ Harr).
    destruct IHt1 as [Hv1 | [t1' Hs1]].
    + destruct IHt2 as [Hv2 | [t2' Hs2]].
      * destruct (canonical_forms_fun t1 T2 T Hfun Hv1) as [x [u Heq]].
        subst. right. exists <{ [x:=t2] u }>.
        apply ST_AppAbs. assumption.
      * right. exists <{ t1 t2' }>. apply ST_App2; assumption.
    + right. exists <{ t1' t2 }>. apply ST_App1; assumption.
  - 
    inversion HT; subst.
    assert (has_type empty t1 Ty_Bool) as Hcond by eauto.
    specialize (IHt1 _ Hcond).
    destruct IHt1 as [Hv1 | [t1' Hs1]].
    + (* condition is a value: must be true/false *)
      destruct (canonical_forms_bool t1 Hcond Hv1) as [-> | ->].
      * right. exists t2. apply ST_IfTrue.
      * right. exists t3. apply ST_IfFalse.
    + (* condition steps *)
      right. exists <{ if t1' then t2 else t3 }>.
      apply ST_If. exact Hs1.
Qed.

(* ################################################# *)
(** * Stabilita (zachovanie) typu (Preservation Theorem)

Druhá časť vlastnosti bezpečnosti typov je zachovanie typov počas
redukcie. Na to potrebujeme technické vety o premenných a substitúcii.

Stručný plán dôkazu:
  - *Preservation theorem*: dokazuje sa indukciou na odvodzovaní
    typov. Najzložitejší prípad je [ST_AppAbs], kde sa používa
    substitúcia, takže potrebujeme vedieť, že substitúcia zachováva typ.

  - *Substitution lemma*: substitúcia dobre typovaného, uzavretého
    termu [s] za premennú [x] v [t] zachováva typ [t]. Dôkaz ide
    indukciou na tvare [t].

  - *Weakening lemma*: typovanie sa zachováva pri rozširovaní kontextu [Gamma].
*)

(** Jednotlivé vety na seba nadväzujú v opačnom poradí. *)

(* ================================================================= *)
(** ** The Weakening Lemma *)
(** 
  Najprv ukážeme, že typovanie sa zachováva pri rozširovaní kontextu [Gamma].
*)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }>  ->
     <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

(* Helper: empty is included in every context *)
Lemma includedin_empty : forall (A:Type) (m: partial_map A),
  includedin (@empty A) m.
Proof.
  unfold includedin; intros A m x v H.
  unfold empty in H. simpl in H. discriminate.
Qed.

(** Následujúca veta je jednoduchým dôsledkom predchádzajúcej vety *)

(** ----------------------------------------------- **)
(** Úloha 6 ★ Dokážte, nasledujúcu teorému. *)
Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T Ht.
  eapply weakening; [apply includedin_empty | exact Ht].
Qed.

(* ================================================================= *)
(** ** Veta o substitúcii *)

(** Ak redukcia zachováva typy: potom substitúcia zachováva typy. *)

(** 
Veta o substitúcii hovorí, že ak máme term [t] s voľnou premennou [x] a
predpokladáme, že [x] má typ [U], a zároveň vieme, 
že [v] má typ [U], potom substitúciou [v] za [x] v [t] 
získáme nový term, ktorý má stále typ [T].

Veta: 
      Ak [x |-> U; Gamma |-- t ∈ T] a [|-- v ∈ U], 
      potom [Gamma |-- [x:=v] t ∈ T]. *)


Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.

(** 
Intuitívne: substitúciu a typovanie môžeme vykonať v ľubovoľnom poradí:
môžeme najprv priradiť typy termom [t] a [v] a potom ich spojiť substitúciou,
alebo najprv substituovať a potom určiť typ pre [[x:=v] t]; 
výsledok je rovnaký. *)

(** Dôkaz: indukciou podľa štruktúry [t]. Pre všetky [T] a [Gamma], ak
[x|->U; Gamma |-- t ∈ T] a [|-- v ∈ U], potom [Gamma |-- [x:=v] t ∈ T]. *)

(* 
- Ak je [t] premenná:
  - Ak [t = x], potom z [ x|-> U; Gamma |-- x ∈ T ] vyplýva [U = T].
    Potrebujeme ukázať, že [[x:=v]x = v] má typ [T] v [Gamma].
    To vyplýva z lemy o oslabení (weakening).
 
  - Ak [t = y] ≠ x, potom [y] má rovnaký typ 
    v [x|->U; Gamma] aj v [Gamma]. 
*)

(* 
- Ak je [t] abstrakcia [\y:S, t0], potom [T = S->T1].
  Indukčný predpoklad (IH) hovorí, že substitúcia zachováva typ pre t0
  v ľubovoľnom kontexte [Gamma'].

  Rôzne správanie substitúcie podľa toho, či x = y alebo nie:

  - Ak x = y, potom [[x:=v] t = t], stačí ukázať [Gamma |-- t ∈ T].

  - Ak x ≠ y, použijeme T_Abs a IH pre [t0] s kontextom [y|->S; Gamma]. *)

(* 
- Ak je [t] aplikácia [t1 t2], 
  výsledok nasleduje priamo z definície substitúcie a IH. *)

(* - Ostatné prípady sú podobné ako pri aplikácii. *)

Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* v každom poddôkaze potrebujeme inverziu H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst. 
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2. 
      -- auto. 
      -- auto. 
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(** ----------------------------------------------- **)
(** Úloha 7 ★ Dokážte, nasledujúcu teorému. *)
(*
Ukážte, že veta [substitution_preserves_typing] sa dá dokázať
aj indukciou na typovej relácii. *)

Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>   ->
  <{ Gamma |-- [x:=v]t \in T }>.
Proof.
 intros Gamma x U t v T Ht Hv.
 eapply substitution_preserves_typing; eauto.
Qed.
  

(* ================================================================= *)
(** ** Progres *)

Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.
(** Dôkaz: Indukciou na typovej relácii [|-- t ∈ T].
- [T_Var], [T_Abs], [T_True], [T_False] nie je možné redukovať.

- Ak je posledné pravidlo v redukcii [T_App], [t = t1 t2]:
  * [ST_App1]: [t1 --> t1'] → [t1' t2] má typ [T] podľa IH.
  * [ST_App2]: [t2 --> t2'] → [t1 t2'] má typ [T] podľa IH.
  * [ST_AppAbs]: [t1 = \x:T0,t0] → [[x:=t2]t0] 
      má typ [T] podľa lemy o substitúcii.

- Ak je posledné pravidlo v redukcii [T_If], [t = if t1 then t2 else t3]:
  * [ST_IfTrue]/[ST_IfFalse]: 
      výsledok je priamo, lebo [t2] alebo [t3] majú typ [T].
  * [ST_If]: t1 --> t1' → [if t1' then t2 else t3] 
      má typ [T] podľa IH. 
*)
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Väčšina prípadov nasleduje priamo z indukcie,
      a [eauto] ich automaticky vyrieši. *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2. 
      -- inversion HT1. subst. apply H1.
      -- assumption. 
Qed.


(** ----------------------------------------------- **)
(** Úloha 8 ★ Dokážte, nasledujúcu teorému. *)
(* Nie vždy platí opačná veta progresu:
  ak [t --> t'] a [empty |-- t' ∈ T], potom [empty |-- t ∈ T].
Dokažte to na protipríklade. *)

Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ <{ empty |-- t' \in T }> /\ ~ <{ empty |-- t \in T }>.
Proof.
exists <{ if true then true else (\x:Bool, x) }>.
  exists <{ true }>.
  exists <{{ Bool }}>.
  split.
  - 
    apply ST_IfTrue.
  - split.
    + 
      apply T_True.
    + 
      intro Hty.
      inversion Hty; subst.
     
      match goal with
      | Habs : has_type empty (tm_abs x Ty_Bool (tm_var x)) _ |- _ =>
          inversion Habs
      end.
Qed.


(* ################################################# *)
(** * Typová korektnosť (Type Soundness) *)

(** Skombinujte vlastnosti **progress** a **preservation** a ukážte, že správne
typovaný term "sa nikdy nezasekne". *)

Definition relation (X : Type) := X -> X -> Prop.
Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

(** ----------------------------------------------- **)
(** Úloha 9 ★ Dokážte, nasledujúcu teorému. *)
Corollary type_soundness : forall t t' T,
  <{ empty |-- t \in T }> ->
  t -->* t' ->
  ~(stuck t').
Proof.
intros t t' T HT Hmulti.

  assert (HT' : <{ empty |-- t' \in T }>) by
    (induction Hmulti; eauto using preservation).

  unfold stuck; intros [Hnf Hnotval].
  pose proof (progress t' T HT') as Hprog.
  destruct Hprog as [Hv | [t'' Hstep]].
  - 
    contradiction.
  - 
    apply Hnf. exists t''. exact Hstep.
Qed.

(* ################################################# *)
(** * Jedinečnosť typov (Uniqueness of Types) *)
(*
Vlastnosť STLC: typy sú jedinečné – daný term (v danom kontexte) 
má najviac jeden typ. 
*)

(** ----------------------------------------------- **)
(** Úloha 10 ★ Dokážte, nasledujúcu teorému. *)
Theorem unique_types : forall Gamma e T T',
  <{ Gamma |-- e \in T }> ->
  <{ Gamma |-- e \in T' }> ->
  T = T'.
Proof.
  intros Gamma e.
  revert Gamma.
  induction e; intros Gamma U1 U2 HT1 HT2;
    inversion HT1; inversion HT2; subst; try reflexivity.
  - (* var *)
    
    match goal with
    | Hget1 : Gamma _ = Some ?A,
      Hget2 : Gamma _ = Some ?B |- _ =>
        rewrite Hget1 in Hget2; inversion Hget2; reflexivity
    end.
  - 
    match goal with
    | Hf1 : has_type _ e1 (Ty_Arrow _ _),
      Hf2 : has_type _ e1 (Ty_Arrow _ _) |- _ =>
        specialize (IHe1 _ _ _ Hf1 Hf2);
        inversion IHe1; subst; reflexivity
    end.
  - 
    f_equal. eapply IHe; eauto.
  - (* if *)
    eapply IHe2; eauto.
Qed.


End STLC.

