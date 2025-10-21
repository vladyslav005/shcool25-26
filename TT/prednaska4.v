(* Prednáška 4

1. časť
Ďalšie taktiky

2. časť
Logika v Rocq
*)


(*===========================================*)
(**              I. časť                    **)
(*===========================================*)

(*===========================================*)

From Coq Require Import List.
Import ListNotations.
Require Import PeanoNat.


(*===========================================*)
(**     Taktiky apply a symmetry            **) 

(** Taktika apply
Často nastane situácia, keď záver možno dokázať
priamo z množiny predpokladov (kontextu).
*)

Theorem apply_ex1 : forall (n m : nat),
  n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.


(** Taktika symmetry
  Niekedy potrebujeme využiť predpoklad rovnosti, 
  ale jeho strany sú obrátené oproti cieľovej rovnosti.  

  Taktika symmetry transformuje cieľ tvrdenia `x = y`
  na ekvivalentný cieľ `y = x`. Tým umožní priamu aplikáciu
  dostupného predpokladu alebo vety.
*)

Theorem apply_ex2 : forall (n m : nat),
  m = n -> n = m.
Proof.
  intros n m eq. (* apply eq zlyhá*)
  symmetry.
  apply eq.
Qed.


(*===========================================*)
(** Taktiky transitivity a "apply with"     **)

(**
  Ukážka použitia tranzitívnosti rovnosti
*)

(* Manuálny dôkaz pomocou dvoch rewrite *)
Example transitivity_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
intros.
rewrite H. rewrite H0. reflexivity.
Qed.

(* Všeobecná veta o tranzitívnosti rovnosti *)
Theorem transitivity_eq : forall {X:Type} (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. rewrite  eq1. rewrite  eq2.
  reflexivity. 
Qed.

(* Použitie vlastnej vety s "apply with" *)
Example transitivity_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
intros.
apply transitivity_eq with (y:=[c;d]). 
- apply H.
- apply H0.
Qed.

(* Ekvivalentný dôkaz pomocou taktiky transitivity *)
Example transitivity_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
intros.
transitivity [c;d]. 
- apply H.
- apply H0.
Qed.


(*===========================================*)
(**  injection, discriminate, contradiction  **)
(**
  Injektivita a disjunktnosť konštruktorov

  Z definície prirodzených čísel:

     Inductive nat : Type :=
       | O
       | S (n : nat).

  vyplýva, že každý prvok je buď [O], alebo má tvar [S n].
  Okrem toho platí:
  - [S] je injektívny konštruktor: ak [S n = S m], tak [n = m].
  - [O] a [S n] sú disjunktné: [O ≠ S n] pre žiadne [n].

  Podobne pri iných induktívnych typoch:
  - pri zoznamoch je [cons] injektívny a [nil] 
    je odlišný od každého neprázdneho zoznamu,
  - pri [bool] sú [true] a [false] rôzne.
*)

Require Import Coq.Init.Nat.

(* Priamy dôkaz injektivity konštruktora S 
pomocou funkcie pred *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  assert (H2 : n = pred (S n)) by reflexivity.
  rewrite H2. rewrite H. simpl. reflexivity.
Qed.

(**
  Praktickejší spôsob je použiť taktiku [injection],
  ktorá automaticky využije injektívnosť konštruktora.
*)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


(** Taktika discriminate

  Disjunktnosť konštruktorov

  Princíp disjunktnosti hovorí, že žiadne dva rôzne konštruktory 
  (napr. [O] a [S], alebo [true] a [false]) nemôžu byť rovnaké.  


  Ak kontext obsahuje spor, môžeme z neho dokázať čokoľvek.
  Taktika discriminate tento princíp automatizuje:
  ak je v hypotéze rovnosť rôznych konštruktorov,
  cieľ je dokázaný.
*)
Require Import Coq.Bool.Bool.

(* Príklad: predpoklad spor false = true *)
Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra.
  discriminate contra.
Qed.

(* Príklad: protirečenie S n = O *)
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

(** Taktika contradiction

  Taktika [contradiction] sa používa vtedy, keď sa v kontexte
  nachádza zjavný spor – teda dve hypotézy, ktoré sa navzájom
  vylučujú.

  Príkladom je, ak máme v kontexte [H1 : P] a [H2 : ~P],
  alebo ak sa spor dá odvodiť z kombinácie viacerých hypotéz.

 Taktika [contradiction] automaticky prehľadá kontext a
  ak nájde dve protichodné hypotézy (napr. [P] a [~P]),
  alebo nemožnú rovnosť, dôkaz ukončí.

  Inými slovami: ak z hypotéz vyplýva [False],
  potom môžeme dokázať čokoľvek.

  - contradiction sa používa pri logických sporoch 
    v kontexte (napr. P a ~P, alebo hypotéza, 
    ktorá sama vedie k sporu).

  - discriminate sa používa pri rovnostiach 
    rôznych konštruktorov (napr. S n = O, true = false),
*)

(* Príklad: explicitný spor v kontexte *)
Theorem contradiction_ex1 : forall (P Q : Prop),
  P -> ~P -> Q.
Proof.
  intros P Q HP HnP.
  contradiction.
Qed.

(* Príklad: spor vyplývajúci z nemožnej rovnosti *)
Theorem contradiction_ex2 : forall (n : nat),
  S n = O -> 3 = 4.
Proof.
  intros n H.
  discriminate.
Qed.

(* Príklad: spor medzi pravdivostnými hodnotami *)
Theorem contradiction_ex3 : forall b : bool,
  b = true -> b = false -> 0 = 1.
Proof.
  intros b H1 H2.
  rewrite H1 in H2.
  discriminate H2.
Qed.

(**
  Tieto ukážky sú prejavom logického princípu nazývaného
  ex falso: zo sporu vyplýva čokoľvek.
*)


(*===========================================*)
(**     Použitie taktík na predpoklady      **)
(**
  Forward a backward reasoning

  Väčšina taktík pracuje so samotným cieľom a nemení kontext.
  Avšak mnohé taktiky majú aj variant pre prácu s hypotézami.

  - [simpl in H] zjednoduší hypotézu [H] v kontexte.
  - [apply L in H] použije implikáciu [L : X -> Y] 
    na hypotézu [H : X] a nahradí ju za [Y]. 
    To je tzv. *forward reasoning*.

  Naopak [apply L] je *backward reasoning*: 
  ak chceme dokázať [Y], stačí dokázať [X].
*)

(* Príklad s "simpl in H" *)
Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

(* Príklad s "apply ... in" = forward reasoning *)
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H.
  apply EQ in H.
  symmetry in H.
  apply H.
Qed.

(**
  - Forward reasoning: začíname z daných predpokladov 
    a odvodzujeme dôsledky, až kým nedosiahneme cieľ.
  - Backward reasoning: začíname od cieľa a zisťujeme, 
    čo ho implikuje, až kým sa neodvoláme 
    na dané predpoklady alebo známe fakty.
*)


(*===========================================*)
(**     Taktika specialize                  **)

(** 
  Taktika specialize umožňuje konkretizovať príliš všeobecnú
  hypotézu dosadením konkrétnej hodnoty do jej kvantifikátora.

  Ak máme [H : forall (x:T), P], potom
  [specialize H with (x := e)] nahradí [H] za [P[x:=e]].

  Vychádza zo zákona: 
    (∀x)P(x) => P(t), 
  kde t je akýkoľvek výraz.

  Je to v podstate kombinácia [assert] a [apply], ale
  často pôsobí prirodzenejšie.
*)

Search (1 * _). 
(* Nájdenie pomocnej vety PeanoNat.Nat.mul_1_l:
PeanoNat.Nat.mul_1_l: forall n : nat, 1 * n = n
*)

(* Príklad: dosadíme m := 1 *)
Theorem specialize_example: forall n,
     (forall m, m * n = 0) ->
     n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite PeanoNat.Nat.mul_1_l in H.
  apply H.
Qed.

(* Pomocná veta *)
Theorem trans_eq : 
  forall (X:Type) (x y z : X), x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(* Použitie specialize na globálnu vetu trans_eq *)
Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y := [c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. 
Qed.


(*===========================================*)
(**     Taktika unfold                      **) 

(**
  Ručné rozbalenie definícií ([unfold])

  Niekedy je potrebné manuálne rozbaliť definíciu, 
  aby bolo možné manipulovať s výrazom, ktorý predstavuje.
*)

(* Definícia funkcie square *)
Definition square n := n * n.

Search (_ * _ * _). (* veta PeanoNat.Nat.mul_assoc*)


(* Príklad dôkazu, kde je potrebný unfold *)
Lemma square_mult : 
forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl. 
(* simpl nezjednoduší výraz, je potrebné rozbaliť square *)
  unfold square.  (* manuálne rozbalenie definície *)
  rewrite PeanoNat.Nat.mul_assoc.
  assert (H: n * m * n = n * n * m).
    { rewrite PeanoNat.Nat.mul_comm. 
      apply PeanoNat.Nat.mul_assoc. }
  rewrite H. 
  rewrite PeanoNat.Nat.mul_assoc. 
  reflexivity.
Qed.

(* Automatické rozbalovanie jednoduchých funkcií *)
Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m. simpl. reflexivity.
Qed.

(* Komplikovanejšia funkcia s match *)
Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(* Riešenie pomocou destruct *)
Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Riešenie pomocou unfold + destruct *)
Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.  (* explicitné rozbalenie definície *)
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(*===========================================*)
(**     Taktika subst                      **) 

(**
  Nahradenie rovnosti ([subst])

  Taktika [subst] slúži na nahradenie premenných 
  ich známymi hodnotami podľa rovností v kontexte. 

  Ak sa v kontexte nachádza hypotéza 
  v tvare [x = t] alebo [t = x],
  príkaz [subst] automaticky nahradí všetky 
  výskyty [x] výrazom [t].
*)

(* Jednoduchý príklad *)
Lemma subst_example_1 :
  forall (x y : nat), x = y -> x + 1 = y + 1.
Proof.
  intros x y H.
  subst.  (* nahradí x výrazom y vo všetkých výskytoch *)
  reflexivity.
Qed.

(* Príklad, kde sa nahrádza aj viac rovností naraz *)
Lemma subst_example_2 :
  forall (a b c : nat),
    a = b -> b = c -> a + b = c + c.
Proof.
  intros a b c H1 H2.
  subst.  (* nahradí a aj b podľa dostupných rovností *)
  reflexivity.
Qed.

(* Niekedy môžeme kombinovať s inými taktikami *)
Lemma subst_example_3 :
  forall (n m : nat),
    n = m ->
    S (n * n) = S (m * m).
Proof.
  intros n m H.
  (* po subst sa výraz zjednoduší *)
  subst.
  reflexivity.
Qed.

(* Príklad, kde [subst] ušetrí prácu oproti 
  manuálnemu prepísaniu 
*)
Lemma subst_example_4 :
  forall (x y z : nat),
    x = y + 1 ->
    y = z ->
    x = z + 1.
Proof.
  intros x y z Hxy Hyz.
  subst.  (* nahradí y z a potom x *)
  reflexivity.
Qed.

(* Porovnanie: manuálne nahradenie bez subst *)
Lemma subst_example_4_manual :
  forall (x y z : nat),
    x = y + 1 ->
    y = z ->
    x = z + 1.
Proof.
  intros x y z Hxy Hyz.
  rewrite Hyz in Hxy.  (* manuálne nahradenie y za z *)
  rewrite Hxy.         (* manuálne nahradenie x *)
  reflexivity.
Qed.

(** Rozdiel medzi [rewrite] a [subst]:

  - [subst] automaticky nahradí všetky premenné 
    podľa rovností v kontexte (tvaru [x = t] alebo [t = x]), 
    tieto rovnosti odstráni a prepíše 
    aj premenné zavedené cez [intros].

  - [rewrite] pracuje len s jednou rovnosťou 
    a tú v kontexte ponechá.

  Použitie:
  - [subst]   → na rýchle zjednodušenie cieľa, 
                keď rovnosti už ďalej nepotrebujeme.
  - [rewrite] → ak chceme s rovnosťou ešte ďalej pracovať 
                (napr. ju použiť opakovane).
*) 

(*===========================================*)
(**     Taktika remember                    **) 

(**
  Zapamätanie výrazu pod menom ([remember])

  Taktika [remember t as x] slúži na „zamrznutie“ výrazu [t] 
  pod novým menom [x] a zároveň pridá rovnosť [x = t] do kontextu.

  Používa sa najmä v prípadoch, keď chceme sledovať vývoj výrazu 
  počas indukcie, alebo keď sa výraz opakovane mení a chceme ho 
  nahradiť menom pre lepšiu čitateľnosť.

  Príkaz [remember t as x]:
    - nahradí [t] výrazom [x] v cieľoch,
    - pridá hypotézu [x = t] do kontextu.
*)

(* Príklad: sledovanie výrazu počas indukcie *)
Lemma remember_example :
  forall (n : nat),
    n + 0 = n.
Proof.
  intros n.
  remember (n + 0) as k eqn:Hk.  (* nahradí výraz menom k *)
  rewrite  Hk. 
  apply Nat.add_0_r.
Qed.


(*===========================================*)
(**     Taktika generalize dependent       **) 

(**
  Všeobecnenie závislej premennej ([generalize dependent])

  Taktika [generalize dependent] slúži na „vrátenie“ 
  závislej premennej späť do cieľa ako univerzálne kvantifikovanej 
  premennej, čím umožňuje jej opätovné zavedenie v inom poradí 
  alebo v inom kontexte.

  Používa sa najmä v prípadoch, keď je potrebné zmeniť poradie 
  zavedenia premenných, napríklad pri dôkazoch pomocou 
  indukcie, kde niektoré premenné závisia od iných.

  Príkaz [generalize dependent x] spôsobí, že premenná [x] 
  sa odstráni z kontextu a pridá sa späť do cieľa ako 
  kvantifikovaná premenná.
*)

(* Príklad: príprava na indukciu *)
Lemma generalize_dependent_example_1 :
  forall (n : nat) (v : nat),
    v = n ->
    n + 0 = n.
Proof.
  intros n v H.
  generalize dependent v.  (* presunieme v späť do cieľa *)
  intros v H. apply Nat.add_0_r.
Qed.


(** Porovnanie s [remember] a [revert]:
  - [generalize dependent x] odstráni [x] z kontextu 
    a pridá ju späť do cieľa ako kvantifikovanú premennú.
  - [remember t as x] vytvorí novú premennú [x := t] 
    a zároveň uloží rovnosť [x = t] do kontextu.

  Použitie:
  - [generalize dependent]:
    ak potrebujeme zmeniť poradie 
    zavedenia premenných, najmä pred indukciou.
  - [remember]:
    ak chceme „zamraziť“ výraz a sledovať jeho vývoj.
*)


(*===========================================*)
(**     Taktika f_equal                     **) 

(**
  Aplikácia rovnosti na argumenty ([f_equal])

  Taktika [f_equal] slúži na dokazovanie rovnosti výrazov, 
  ktoré majú rovnaký vonkajší tvar (funkciu), 
  ale líšia sa v argumentoch.

  Ak máme rovnosť [x = y], potom [f_equal] 
  umožní dokázať [f x = f y].

  Formálne:
    f_equal : 
    forall (A B : Type) (f : A -> B) (x y : A), 
    x = y -> f x = f y

  Používa sa najmä v prípadoch, 
  keď cieľ má tvar [f x = f y] 
  a v kontexte máme dôkaz [x = y].
*)

(* Jednoduchý príklad *)
Lemma f_equal_example :
  forall (x y : nat),
    x = y ->
    S x = S y.
Proof.
  intros x y H.
  apply f_equal.  (* použije rovnosť na argumenty *)
  exact H.
Qed.

(** Porovnanie s [rewrite]:

  - [f_equal] sa používa, keď cieľ má tvar [f x = f y] 
    a máme dôkaz [x = y].

  - [rewrite] prepíše výskyt [x] na [y] v celom výraze.

  Použitie:
  - [f_equal]:
    keď chceme „zdvihnúť“ rovnosť argumentov 
    na rovnosť funkčných výrazov.
  - [rewrite]:
    keď chceme prepísať konkrétny výskyt 
    výrazu podľa rovnosti.
*)

(*===========================================*)
(**     Taktika admit                       **) 

(**
  Dočasné preskočenie časti dôkazu ([admit])

  Taktika [admit] slúži na dočasné „preskočenie“ časti dôkazu, 
  ktorú zatiaľ nevieme alebo nechceme dokázať.

  Používa sa najmä počas vývoja dôkazu, keď chceme pokračovať 
  v iných vetvách alebo častiach, a neskôr sa k nedokončenej 
  časti vrátiť.

  Pozor: [admit] zanechá otvorený cieľ bez dôkazu. 
  Dôkaz nebude úplný, kým sa [admit] 
  nenahradí korektným dôkazom.
*)

(* Príklad: rozdelenie prípadu pomocou destruct *)
Lemma admit_example :
  forall (b : bool),
    if b then 1 + 1 = 2 else 2 + 2 = 4.
Proof.
  intros b.
  destruct b.
  - (* vetva pre b = true *)
    admit.  (* túto časť dokážeme neskôr *)
  - (* vetva pre b = false *)
    simpl. reflexivity.
Admitted.


(*===========================================*)
(**     Taktika assumption                  **) 

(**
  Priama aplikácia známeho dôkazu ([assumption])

  Taktika [assumption] sa používa na vyriešenie cieľa,
  ak už existuje zodpovedajúci dôkaz v kontexte.

  Ak je cieľ rovnaký ako niektorá hypotéza, 
  [assumption] ju automaticky použije na jeho vyriešenie.

  Formálne:
    Ak máme v kontexte [H : P] a cieľ je [P], 
    potom [assumption] dokáže cieľ.

  Používa sa najmä v prípadoch, keď je cieľ priamo dostupný 
  ako hypotéza v kontexte.
*)

(* Jednoduchý príklad *)
Lemma assumption_example :
  forall (P Q : Prop),
    P ->
    Q ->
    P.
Proof.
  intros P Q HP HQ.
  assumption.  (* použije hypotézu HP na vyriešenie cieľa *)
Qed.

(*===========================================*)
(**     Taktika try assumption              **) 

(**
  Bezpečná aplikácia taktiky ([try])

  Taktika [try T] sa pokúsi aplikovať taktiku [T], 
  ale ak zlyhá, nezastaví dôkaz — jednoducho nič neurobí.

  Používa sa najmä v prípadoch, 
  keď chceme taktiku aplikovať len vtedy, 
  ak je to možné, napr. v automatizovaných dôkazoch 
  alebo v sekvenciách.

  Príklad:
    try assumption  
    (* pokúsi sa vyriešiť cieľ pomocou hypotézy *)
*)

(* Jednoduchý príklad *)
Lemma try_assumption_example :
  forall (P Q : Prop),
    P ->
    Q ->
    P.
Proof.
  intros P Q HP HQ.
  try assumption. 
Qed.



(*===========================================*)
(**     Taktika repeat                      **) 

(**
  Opakované aplikovanie taktiky ([repeat])

  Taktika [repeat T] slúži na opakované aplikovanie taktiky [T], 
  kým je to možné — teda kým [T] nezlyhá.

  Je užitočná pri dôkazoch, kde sa rovnaká taktika dá aplikovať 
  na viaceré podciele alebo viackrát za sebou.

  Formálne:
    repeat T : aplikuje Taktiku [T] opakovane, kým je úspešná.

  Používa sa najmä v prípadoch, keď máme viacero 
  podobných podcielov, napr. pri konjunkciách, disjunkciách,
  alebo pri automatizácii dôkazov.
*)

(* Jednoduchý príklad *)
Lemma repeat_example :
  forall n, (((n + 0) + 0) + 0) = n.
Proof.
  intros n.
  repeat rewrite PeanoNat.Nat.add_0_r.
  reflexivity.
Qed.

(*===========================================*)
(**     Taktika bodkočiarka (;)             **) 

(**
  Sekvenčné aplikovanie taktík ([;])

  Taktika [T1 ; T2] slúži na aplikovanie taktiky [T2] 
  na všetky podciele, ktoré vzniknú po aplikovaní [T1].

  Je to spôsob, ako reťaziť taktiky: prvá taktika rozdelí cieľ, 
  druhá sa automaticky aplikuje na každý podcieľ.

  Formálne:
    Ak [T1] vytvorí podciele [G1], [G2], ..., potom [T1 ; T2] 
    aplikuje [T2] na každý [Gi].

  Používa sa najmä v prípadoch, keď chceme rovnakým spôsobom 
  vyriešiť všetky podciele, 
  napr. pomocou [assumption], [auto], [simpl].
*)

(* Jednoduchý príklad *)
Lemma semicolon_simple :
  forall b : bool, (if b then true else false) = b.
Proof.
  intros b.
  destruct b; reflexivity.
Qed.
(** Príkaz [destruct b] rozdelí dôkaz na dve vetvy:
      1. prípad, keď [b = true]
      2. prípad, keď [b = false]

  - Taktický operátor [;] spôsobí, že nasledujúca taktika
    ([reflexivity]) sa automaticky aplikuje na obe vetvy.

  - Preto stačí napísať [reflexivity] len raz — 
    použije sa v oboch prípadoch a dôkaz sa uzavrie.
*)



(*===========================================*)
(**              II. časť                   **)
(*===========================================*)

(*===========================================*)
(**          Logika v Rocq                  **)
(*===========================================*)
(**
  V predchádzajúcich príkladoch bolo prezentovaných 
  mnoho príkladov výrokov (propositions) 
  a spôsobov, ako ich dokázať. 
  Najčastejšie to boli výroky v tvare:
  - rovnosti (e1 = e2),
  - implikácie (P -> Q),
  - kvantifikovaného tvrdenia (forall x, P).

  Rocq umožňuje prácu aj s inými tvarmi
  logického uvažovania.
*)

(*
==================================================
Základná tabuľka operátorov v Rocq
==================================================

1 Porovnávacie operátory pre nat (vracajú bool)
--------------------------------------------------
  n =? m    : test rovnosti (true ak n = m, inak false)
  n <=? m   : menšie alebo rovné
  n <? m    : menšie

Príklady:
  Compute (3 <=? 5).  (* true *)
  Compute (5 =? 3).   (* false *)
  Compute (4 <? 4).   (* false *)

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

Poznámka: - Prop je typ pre formálne tvrdenia a dôkazy,
          - bool je typ programovo vyhodnocovateľný.

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
  - Používa sa pri dôkazoch
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

(** Aj keď je výrok typu Prop, nemusí byť pravdivý: *)
Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check (forall n : nat, n = 2) : Prop.


(** 
    Výroky sa často používajú v teorémach, 
    vetach alebo príkladoch:
*)
Theorem plus_2_2_is_4 :
2 + 2 = 4.
Proof. reflexivity. Qed.

(** Výroky môžu mať priradené meno cez Definition: *)  
Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

(** 
    Takéto pomenované výroky je možné neskôr 
    použiť v teorémach: 
*)
Theorem plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.

(** 
    Výroky môžu byť parametrizované výroky, t.j. funkcie,
    ktoré vracajú Prop:
*)
Definition is_three (n : nat) : Prop := n = 3.
Check is_three : nat -> Prop.

(** Príklad polymorfnej vlastnosti – injektívna funkcia: *)
Definition injective {A B} (f : A -> B) : Prop :=
              forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
unfold injective. (* nie je nutné rozbaliť injective *)
intros x y H. 
injection H as H1. 
apply H1.
Qed.

(** Operátor = je polymorfná binárna funkcia vracajúca Prop *)  
Check @eq : forall A : Type, A -> A -> Prop.

(*===========================================*)
(**          Logické spojky                 **)

(** V tejto kapitole budú prezentované príklady
    použitia základných spojok logiky. 
*)

(*
       LOGICKÉ SPOJKY V Rocq
  ┌───────────────────────────┐
  │       Konjunkcia /\       │
  │   P /\ Q znamená P a Q    │
  │   Dôkaz: split; apply ... │
  │   Rozbitie v kontexte:    │
  │     destruct H as [HP HQ] │
  └───────────┬───────────────┘
              │
  ┌───────────▼───────────────┐
  │        Disjunkcia \/      │
  │   P \/ Q znamená P alebo Q│
  │   Dôkaz: left/right; apply│
  │   Rozbitie v kontexte:    │
  │     intros [HP | HQ]      │
  └───────────┬───────────────┘
              │
  ┌───────────▼───────────────┐
  │       Implikácia ->       │
  │   P -> Q znamená: ak P,   │
  │   potom Q                 │
  │   Dôkaz: intros; apply ...│
  │   Rozbitie v kontexte:    │
  │     apply H in HP         │
  └───────────┬───────────────┘
              │
  ┌───────────▼────────────────────┐
  │   Negácia a Absurdum           │
  │   ~P alebo False               │
  │   ~P = P -> False              │
  │   Dôkaz: intros H; destruct H  │
  │   Príklady:                    │
  │     False -> P                 │
  │     ~(a = b) -> a <> b         │
  └───────────┬────────────────────┘
              │
  ┌───────────▼───────────────┐
  │        Vérum True         │
  │   True je vždy pravda     │
  │   Dôkaz: apply I          │
  └───────────┬───────────────┘
              │
  ┌───────────▼───────────────┐
  │       Ekvivalencia <->    │
  │   P <-> Q znamená: P -> Q │
  │   a Q -> P                │
  │   Dôkaz: split; apply ... │
  └───────────┬───────────────┘
              │
  ┌───────────▼───────────────┐
  │ Existenčný kvantifikátor  │
  │     exists n, P n         │
  │ Dôkaz: exists n; apply ...│
  │ Príklady použitia:        │
  │ 1) Existencia v kontexte: │
  │      destruct H as [x Hx] │
  │      (* Hx: P x *)        │
  │ 2) Existencia v cieli:    │
  │      exists x; apply H    │

  └───────────────────────────┘
*)


(*-------------------------------------------*)
(** Konjunkcia (AND, /\) *)

Lemma and_example : forall P Q : Prop,
  P -> Q -> P /\ Q.
Proof.
  intros P Q HP HQ.
  split.
  - apply HP.
  - apply HQ.
Qed.

(* ----------------------------------------------------------- *)
(** ** Konjunkcia v kontexte – eliminácia ľavej časti *)

(**
Lemma `and_elim_left` ukazuje, ako pracovať s konjunkciou `P /\ Q`
v **kontexte** (teda medzi predpokladmi).

Ak máme hypotézu `H : P /\ Q`, vieme, že platí **oboje**: `P` aj `Q`.
Pomocou `destruct` môžeme túto konjunkciu „rozbiť“
na dve samostatné hypotézy, napríklad `HP : P` a `HQ : Q`. 
Potom môžeme použiť `apply HP` na dokázanie `P`.
*)

Lemma and_elim_left : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].  (* rozbieme konjunkciu *)
  apply HP.                (* použijeme ľavú časť *)
Qed.


(*-------------------------------------------*)
(** Disjunkcia (OR, \/) *)

Lemma or_example_left : forall P Q : Prop,
  P -> P \/ Q.
Proof.
  intros P Q HP.
  left.
  apply HP.
Qed.

Lemma or_example_right : forall P Q : Prop,
  Q -> P \/ Q.
Proof.
  intros P Q HQ.
  right.
  apply HQ.
Qed.

(* ----------------------------------------------------------- *)
(** ** Disjunkcia v kontexte *)

(**
Ak máme `H : P \/ Q`, znamená to, že platí buď `P`, alebo `Q`.
Musíme teda dokázať cieľ **v oboch prípadoch**.
Na to použijeme `destruct H as [HP | HQ].`

`destruct` na disjunkcii vytvorí dve vetvy dôkazu — 
jednu pre každý prípad.
*)

Lemma disj_in_context : 
forall P Q R : Prop, P \/ Q -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R H HPtoR HQtoR.
  destruct H as [HP | HQ].   
  (* rozdelíme prípady podľa disjunkcie *)
  - apply HPtoR. exact HP.
  - apply HQtoR. exact HQ.
Qed.

(*-------------------------------------------*)
(** Implikácia (->) *)

Lemma impl_example : forall P Q : Prop,
  (P -> Q) -> P -> Q.
Proof.
  intros P Q H HP.
  apply H.
  apply HP.
Qed.

(*-------------------------------------------*)
(** Negácia a absurdum (not (~), False) *)

(* V Rocq je negácia definovaná ako implikácia do False:
   ~P znamená P -> False. *)

Lemma not_example : forall P : Prop,
  (P -> False) -> ~P.
Proof.
  intros P H HP.
  apply H.
  apply HP.
Qed.

(* Lemma absurd_example demonštruje princíp explózie:
   ak máme False v kontexte, môžeme dokázať čokoľvek. *)

Lemma absurd_example : forall P : Prop, False -> P.
Proof.
  intros P H.
  destruct H.
Qed.

Lemma absurd_example' : forall P : Prop, False -> P.
Proof.
  intros P H.
  contradiction.
Qed.


(*-------------------------------------------*)
(** Vérum (True) *)

(* V Rocq je True typ Prop, ktorý je vždy pravdivý. 
   Konštruktor I je dôkazom True. *)

Lemma true_example : True.
Proof.
  apply I.
Qed.

(*-------------------------------------------*)
(** Ekvivalencia (iff, <->) *)

Lemma iff_example : forall P Q : Prop,
  (P -> Q) -> (Q -> P) -> (P <-> Q).
Proof.
  intros P Q H1 H2.
  split.
  - apply H1.
  - apply H2.
Qed.

(*-------------------------------------------*)
(** Existenčný kvantifikátor (exists) *)

Lemma exists_example : forall P : nat -> Prop,
  P 0 -> exists n, P n.
Proof.
  intros P H.
  exists 0.
  apply H.
Qed.

Lemma exists_example2 : exists n : nat, n = 3.
Proof.
  exists 3.
  reflexivity.
Qed.

(* ----------------------------------------------------------- *)
(** ** Existenčný kvantifikátor v kontexte *)

(**
Ak máme v kontexte `H : exists x, P x`,
znamená to, že **existuje konkrétny prvok** `x`, pre ktorý platí `P x`.

Aby sme túto informáciu mohli použiť,
musíme ju „rozbaliť“ pomocou:
- `destruct H as [x Hx].`

Tým získame:
- konkrétnu hodnotu `x`
- dôkaz `Hx : P x`
*)


Lemma exists_simple_example :
  (exists n : nat, n = 3) -> 2 + 1 = 3.
Proof.
  intros H.
  destruct H as [x Hx].   (* rozbalíme existenciu *)
  rewrite <- Hx.          (* nahradíme cieľ podľa rovnosti n = 3 *)
  simpl.
  symmetry.               (* zjednodušíme výraz *)
  assumption.
Qed.

(* ########################################################### *)
(** * Negácia, exfalso, contradiction pri False v kontexte     *)
(* ########################################################### *)

(**
Intuitívne:
- Negácia `~P` znamená "P nie je pravdivé", 
  teda "ak by platilo P, viedlo by to k rozporu".
- V Rocq je negácia definovaná ako `not P := P -> False`.
- Ak teda máme `P` aj `~P`, môžeme odvodiť `False`.
- Z `False` potom môžeme dokázať čokoľvek 
  (taktiky `exfalso`, `contradiction`).

Formálne:
    Definition not (P : Prop) := P -> False.
*)

(* ----------------------------------------------------------- *)
(** ** unfold not *)

Lemma not_example1 : forall P : Prop, ~P -> P -> False.
Proof.
  intros P HnotP HP.
  unfold not in HnotP.    (* rozbalíme definíciu not: P -> False *)
  apply HnotP.
  exact HP.
Qed.


(* ----------------------------------------------------------- *)
(** ** unfold not pre zložitejší výraz *)

Lemma not_example2 : 
      forall P Q : Prop, ~(P /\ Q) -> P -> Q -> False.
Proof.
  intros P Q HnotPQ HP HQ.
  unfold not in HnotPQ.   
  (* rozbalíme ~(P /\ Q) na (P /\ Q) -> False *)
  apply HnotPQ.
  split; assumption.
Qed.

(* ----------------------------------------------------------- *)
(** ** exfalso *)

(**
Taktika `exfalso` mení aktuálny cieľ na `False`.
Teda ak dokážeme, že cieľ by viedol k rozporu, môžeme sa “prepnuť” na dokazovanie `False`.
*)

Lemma exfalso_example : forall P Q : Prop, P -> ~P -> Q.
Proof.
  intros P Q HP HnotP.
  unfold not in HnotP.
  exfalso.          (* meníme cieľ Q na cieľ False *)
  apply HnotP.
  exact HP.
Qed.

(* ----------------------------------------------------------- *)
(** ** contradiction s False v kontexte *)

Lemma false_in_context : forall P : Prop, False -> P.
Proof.
  intros P Hfalse.
  contradiction.     (* z False ide dokázať čokoľvek *)
Qed.

(* Alternatíva s exfalso *)

Lemma false_in_context_alt : forall P : Prop, False -> P.
Proof.
  intros P Hfalse.
  exfalso. exact Hfalse.
Qed.

(* ----------------------------------------------------------- *)
(** ** Negácia rovnosti (a <> b) *)

(**
V Rocq je `a <> b` len skratka za `~(a = b)`,
čo je teda `(a = b) -> False`.
Preto aj tu môžeme použiť `unfold not`.
*)

Lemma neq_unfold_example : forall (A : Type) (a b : A),
  a <> b -> a = b -> False.
Proof.
  intros A a b Hneq Heq.
  unfold not in Hneq.   
  (* rozbalíme a <> b na (a = b) -> False *)
  apply Hneq.
  exact Heq.
Qed.

(* ----------------------------------------------------------- *)
(** ** Použitie negácie rovnosti v dôkaze *)

Lemma neq_contradiction_example : forall (n m : nat),
  n <> m -> n = m -> 2 + 2 = 5.
Proof.
  intros n m Hneq Heq.
  unfold not in Hneq.
  exfalso.           (* chceme ukázať, že sme v rozpore *)
  apply Hneq.
  exact Heq.
Qed.


(*===========================================*)
(**   Programovanie s výrokmi               **)

(*----------------------------------------------*)
(** Rekurzívna definícia výroku: x je v liste l *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl. intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(*-------------------------------------------*)
(** In map: zachovanie vlastnosti pri mapovaní *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IH].
  - simpl. intros []. (* nil case *)
  - simpl. intros [H | H].
    + left. rewrite H. reflexivity.
    + right. apply IH. apply H.
Qed.


(*===========================================*)
(**   Klasická vs konštruktívna logika      **)

(* Konštruktívna logika: 
v konštruktívnej logike na ktorej je Rocq založený
neplatí zákon vylúčeného tretieho *)


Definition P := forall n : nat, n = n. 
(* ľubovoľná konštrukcia, vždy pravdivé *)
Check P : Prop.
(* Klasická logika: 
    ak chceme použiť zákon vylúčeného tretieho, 
    musíme ho zaviesť ako axiómu 
*)

Require Import Coq.Logic.Classical. 
(* Klasické axiomy *)

(* Zavolanie zákona vylúčeného tretieho *)
Check classic : forall P : Prop, P \/ ~P.

(* Príklad použitia *)
Lemma excluded_middle_example : forall Q : Prop, Q \/ ~Q.
Proof.
  intros Q.
  apply classic. (* použijeme klasickú axiómu *)
Qed.


(**
===========================================
           Prehľad nových taktik
===========================================

  V tejto prednáške boli zavedené nové taktiky
  na prácu s rovnosťami, logickými spojkami a
  manipuláciou s kontextom.

-------------------------------------------
           ZÁKLADNÉ TAKTIKY
-------------------------------------------

apply
  - použije existujúci dôkaz (implikáciu, rovnosť)
  - backward reasoning: cieľ sa nahradí predpokladom
  - Príklad:  apply H.

apply ... with (...)
  - umožňuje explicitne zadať argumenty do univerzálne
    kvantifikovanej vety
  - Príklad: apply transitivity_eq with (y := [c;d]).

symmetry
  - obráti smer rovnosti v cieli (z x = y na y = x)
  - Príklad: symmetry. apply H.

transitivity
  - využije tranzitivitu rovnosti (alebo inej relácie)
  - Príklad: transitivity [c;d].

reflexivity
  - ukončí cieľ, ak sú obe strany rovnosti identické
  - Príklad: reflexivity.

-------------------------------------------
          KONŠTRUKTORY A SPORY
-------------------------------------------

injection
  - využije injektívnosť konštruktora
  - ak S n = S m, tak z toho plynie n = m
  - Príklad: injection H as H1.

discriminate
  - automaticky ukončí dôkaz pri spore medzi
    rôznymi konštruktormi (napr. true = false)
  - Príklad: discriminate H.

contradiction
  - nájde spor v kontexte (napr. P a ~P)
  - použiteľné pri logických sporoch
  - Príklad: contradiction.

-------------------------------------------
          PRÁCA S KONTEXTOM
-------------------------------------------

simpl
  - zjednoduší cieľ výpočtom, redukciou alebo unfoldom
  - Príklad: simpl.

simpl in H
  - zjednoduší výraz priamo v hypotéze H
  - Príklad: simpl in H.

apply ... in
  - aplikuje implikáciu na hypotézu (forward reasoning)
  - Príklad: apply EQ in H.

specialize
  - konkretizuje všeobecnú hypotézu dosadením parametra
  - Príklad: specialize H with (m := 1).

unfold
  - manuálne rozbalí definíciu
  - Príklad: unfold square.

destruct ... eqn:
  - rozdelí dôkaz podľa tvaru hodnoty, 
    uloží rovnosť do eqn:
  - Príklad: destruct m eqn:E.

-------------------------------------------
         LOGICKÉ SPOJKY (Prop)
-------------------------------------------

split
  - rozdelí cieľ typu P /\ Q na dve podciele P a Q
  - Príklad: split.

left / right
  - vyberie stranu disjunkcie (P \/ Q)
  - Príklad: left. apply HP.

exists
  - použije sa pri dôkaze existenčného tvrdenia
  - Príklad: exists 3.

destruct
  - rozkladá zložené tvrdenie (P /\ Q, P \/ Q, exists)
  - Príklad: destruct H as [HP HQ].

-------------------------------------------
        ROZŠÍRENÉ TAKTIKY
-------------------------------------------

subst
  - automaticky nahradí všetky premenné podľa rovností
    v kontexte (x = t alebo t = x)
  - odstráni rovnosti z kontextu po ich použití
  - Príklad: subst.

generalize dependent
  - „vráti“ premennú z kontextu späť do kvantifikácie
  - umožní meniť poradie premenných pri indukcii
  - Príklad: generalize dependent n.

revert
  - opak [intros]; presunie premenné alebo hypotézy
    späť do cieľa
  - Príklad: revert m n.

repeat
  - opakuje danú taktiku, kým je úspešná
  - Príklad: repeat constructor.

; (bodkočiarka)
  - aplikuje druhú taktiku na všetky podciele
  - Príklad: destruct b; reflexivity.

assert
  - umožní zaviesť pomocný medzikrok
  - Príklad: assert (H: n = m) by reflexivity.

-------------------------------------------
     SKUPINY TAKTÍK PODĽA POUŽITIA
-------------------------------------------

Práca s rovnosťami:
  apply, symmetry, transitivity, injection, 
  discriminate, reflexivity, subst

Práca s logikou (Prop):
  split, left, right, destruct, contradiction, exists

Manipulácia s kontextom:
  simpl in, apply ... in, specialize, 
  unfold, generalize dependent, revert

Riadenie toku dôkazu:
  intros, assert, induction, 
  destruct ... eqn:, ;, repeat

-------------------------------------------
      REORGANIZÁCIA DÔKAZU
-------------------------------------------

assert
  - vloží medzivýrok do dôkazu, ktorý sa dokazuje zvlášť
  - rozdelí dôkaz na dva podciele: 
      (1) dokázať tvrdenie,
      (2) pokračovať s novou hypotézou
  - Príklad:
        assert (H: n * 0 = 0).
        { simpl. reflexivity. }
        rewrite H.

generalize dependent
  - zmení poradie dôkazových premenných tak, aby
    bolo možné aplikovať indukciu na správnu z nich
  - často používané spolu s induction

revert
  - presunie premenné alebo hypotézy späť do cieľa
  - umožňuje preusporiadať kontext pred indukciou
  - Príklad: revert m n.

-------------------------------------------
      AUTOMATIZÁCIA A SKRATKY
-------------------------------------------

repeat
  - opakuje daný krok až do zlyhania
  - napr. opakované zjednodušenie alebo constructor

; (bodkočiarka)
  - aplikuje druhú taktiku na všetky vetvy po destruct

*)


(**
===========================================
      MAPA TAKTÍK – VIZUÁLNY PREHĽAD
===========================================

Cieľom je vedieť rýchlo určiť, KTORÚ taktiku
použiť v danej situácii.

────────────────────────────────────────────
1  PRÁCA S ROVNOSŤAMI
────────────────────────────────────────────
        +----------------------+
        |  Potrebujem dokázať  |
        |     x = y            |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ obe strany rovnaké →       │ reflexivity
     │ známa rovnosť H : x = y →  │ apply H
     │ opačný smer →              │ symmetry
     │ cez medzičlánok →          │ transitivity
     │ konštruktor rovnaký →      │ injection
     │ konštruktor rôzny →        │ discriminate
     │ chcem nahradiť v kontexte →│ subst
     └────────────────────────────┘

────────────────────────────────────────────
2  SPORY A KONTRADIKCIE
────────────────────────────────────────────
        +----------------------+
        |  V kontexte mám      |
        |  spor (False, P ∧ ¬P)|
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ logický spor →             │ contradiction
     │ nemožná rovnosť (S n = O) →│ discriminate
     │ z False dokážem čokoľvek → │ destruct H
     └────────────────────────────┘

────────────────────────────────────────────
3  PRÁCA S KONTEXTOM
────────────────────────────────────────────
        +----------------------+
        |  Chcem upraviť alebo |
        |  použiť hypotézu     |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ zjednodušiť výraz →        │ simpl / simpl in H
     │ aplikovať implikáciu →     │ apply ... in
     │ konkretizovať ∀ →          │ specialize H with (...)
     │ rozbaliť definíciu →       │ unfold názov
     │ rozdeliť tvar →            │ destruct ... eqn:
     │ vrátiť premennú do cieľa → │ revert
     │ zmeniť poradie pre indukciu│ generalize dependent
     └────────────────────────────┘
────────────────────────────────────────────
4  LOGICKÉ SPOJKY (Prop)
────────────────────────────────────────────
        +----------------------+
        |  Cieľ alebo hypotéza  |
        |  má tvar P /\ Q , P \/ Q , ∃ x, P x, ~P |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ P /\ Q →                   │ split / destruct
     │   • cieľ: split.           │ rozdelí P /\ Q na P a Q
     │   • hypotéza H: destruct H │ H : P /\ Q → H1 : P, H2 : Q
     │     as [HP HQ].            │
     ├────────────────────────────┤
     │ P \/ Q →                   │ left / right / destruct
     │   • cieľ: vyber stranu:    │
     │           left. apply HP.  │
     │   • hypotéza H:            │
     │    destruct H as [HP | HQ].│
     ├────────────────────────────┤
     │ ∃ x, P x →                 │ exists / destruct
     │   • cieľ:                  │
     │       exists t; apply ...  │
     │   • hypotéza H:            │ 
     │     destruct H as [x Hx].  │
     ├────────────────────────────┤
     │ P -> Q →                   │ intros / apply
     │   • cieľ:                  │
     │        intros HP; apply H. │
     │   • hypotéza H:            │
     │        apply H in HP.      │
     ├────────────────────────────┤
     │ ~P (P -> False) →          │ intros; destruct
     │   • cieľ: intros HP;       │
     │           destruct HP      │
     │   • hypotéza H :           │ 
     │       ~P → apply H in HP   │
     ├────────────────────────────┤
     │ False →                    │ contradiction / destruct
     │   • hypotéza H :           │
     │      False → contradiction │
     │   • z False možno          │
     │     dokázať čokoľvek       │
     └────────────────────────────┘

────────────────────────────────────────────
PRÍKLADY:
────────────────────────────────────────────
1) Existencia v kontexte:
   H : ∃ x, P x
   → destruct H as [x Hx]. (* Hx : P x *)

2) Existencia v cieli:
   Goal: ∃ x, P x
   → exists t. (* t je konkrétny kandidát *)
   → apply H.  (* ak máme dôkaz P t *)

3) Negácia / absurdum:
   H : P /\ ~P
   → destruct H as [HP HnP].
   → contradiction. (* logický spor *)

4) Hypotéza False:
   H : False
   → contradiction. 
   (* z False možno dokázať čokoľvek *)


────────────────────────────────────────────
5  STRATÉGIA DÔKAZU
────────────────────────────────────────────
   • **Backward reasoning** – začni od cieľa
       (apply, transitivity, symmetry, intros)

   • **Forward reasoning** – začni z hypotéz
       (apply ... in, specialize, simpl in)

   • **Reorganizácia dôkazu**
       (assert, revert, generalize dependent)

   • **Riadenie vetiev**
       (destruct ... eqn:, ;, repeat)

   • **Automatické riešenie sporu**
       (discriminate, contradiction)

   • **Rozbalenie a analýza**
       (unfold, induction)
*)

