(** * SfLib: Software Foundations Library *)

(* $Date: 2011-03-14 20:08:53 -0400 (Mon, 14 Mar 2011) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  Case "b = true". auto.
  Case "b = false".
    destruct c ; auto.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n ; destruct m ; auto ; simpl ; apply IHn.
Qed.

(* From Poly.v *)

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  intros n. 
  induction n as [| n''].
  destruct n' as [| n'''].
  Case "n = 0".
    SCase "n' = 0".
      intros H.
      simpl.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.     
    SCase "n' = S n'''".
      intros H.
      reflexivity.
 destruct n' as [| n'''].
 Case "n = S n''".
    SCase "n' = 0".
      intros H.
      reflexivity.
    SCase "n' = S n'''".
      intros H.
      simpl.
      apply IHn''.
      unfold not.
      unfold not in H.
      intros H1.
      rewrite -> H1 in H.
      apply H.
      reflexivity. 
Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. 
  Case "ev 1".
    intros H. inversion H.
  Case "ev 2".
    intros H1.
    inversion H1.
    apply IHev in H2. assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n as [| n'] ; 
    apply le_n || apply le_S ; 
    apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  intros n m.
  destruct n as [| n'].
  Case "n = 0".
    induction m as [| m'].
    SCase "m = 0".
      intros H. apply le_n.
    SCase "m = S m'".
      intros H.
      apply le_S.
      apply IHm'.
      apply O_le_n.
  Case "n = S n'".
    induction m as [| m'].
    intros H.
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      intros H.
      inversion H ; subst.
      apply le_n.
      apply le_S.
      apply IHm'.
      apply H1.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  induction n as [| n'].
  Case "n = 0".
    intros m Heq.
    apply O_le_n.
  Case "n = S n'".
    intros m. 
    destruct m as [| m'].
    SCase "m = 0".
      simpl. intros H. inversion H.
    SCase "m = S m'".
      simpl. intros H. apply IHn' in H.
      apply n_le_m__Sn_le_Sm ; assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m as [| m']. 
  Case "m = 0".
    intros n. 
    destruct n as [| n']. 
    SCase "n = 0".
     intros H. apply le_n.
    SCase "n = S n'".
     intros H. inversion H. inversion H1.
  Case "m = S m'".
    intros n H.      
    inversion H ; subst.
    apply le_n.
    apply le_S. apply IHm'.
    assumption.
Qed. 

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  induction n as [| n'].
  Case "n = 0".
    intros m.
    destruct m as [| m'].
    SCase "m = 0".
      intros H. inversion H.    
    SCase "m = S m'".
      simpl.
      intros H. inversion H.
  Case "n = S n'". 
    intros m.
    destruct m as [| m'].
    SCase "m = 0".
      simpl.
      intros H contra. clear H.
      inversion contra.
    SCase "m = S m'". 
      simpl.
      intros H. apply IHn' in H.
      intros H1.
      apply Sn_le_Sm__n_le_m in H1.
      contradiction.
Qed.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).


Definition relation (X:Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Definition transitive_relation {X : Type} (R : relation X):= 
	forall (x y z : X), R x y /\ R y z -> R x z.

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

Inductive refl_step_closure (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | rsc_refl  : forall (x : X),
                 refl_step_closure X R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure X R y z ->
                    refl_step_closure X R x z.
Implicit Arguments refl_step_closure [[X]]. 

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl.   Qed.

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  intros X R x y z H1.
  induction H1. trivial.
  intros H2.
  apply IHrefl_step_closure in H2.
  eapply rsc_step.
  apply H.
  assumption.
Qed.


(* Identifiers and polymorphic partial maps. *)
Inductive id : Type := 
  Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl.  Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.


Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (beq_id x2 x1)...
Qed.

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(** some extra things *)

Ltac inv H := inversion H ; clear H ; subst.

Definition eq_id_dec : forall (i i' : id), {i = i'} + {i <> i'}.
Proof.
  pose eq_nat_dec.
  decide equality.
Qed.