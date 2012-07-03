(** definition of the small step semantics *)

Require Import SfLib Syntax.

Reserved Notation "t '==>' t'" (at level 40).

Fixpoint subst (x : id) (t : term) (t' : term) {struct t'} : term :=
  match t' with
    | tm_var i => if beq_id x i then t else t'
    | tm_app l r => tm_app (subst x t l) (subst x t r)
    | tm_abs i T t1 => tm_abs i T (if beq_id x i then t1 else (subst x t t1))
    | tm_trust t1 => tm_trust (subst x t t1)
    | tm_distrust t1 => tm_distrust (subst x t t1)
    | tm_check t1 => tm_check (subst x t t1)
    | tm_if t1 t2 t3 => tm_if (subst x t t1) (subst x t t2) (subst x t t3)
    | tm_true        => tm_true
    | tm_false       => tm_false
  end.

Inductive bvalue : term -> Prop :=
  | v_true : bvalue tm_true | v_false : bvalue tm_false.

Inductive absvalue : term -> Prop :=
  | v_abs : forall x T t12, absvalue (tm_abs x T t12).

Definition value (t : term) : Prop := bvalue t \/ absvalue t.

Hint Constructors bvalue absvalue.
Hint Unfold value.

Inductive step : term -> term -> Prop :=
  | e_appabs : forall x T t12 v2, value v2 -> (tm_app (tm_abs x T t12) v2) ==> subst x v2 t12
  | e_app1   : forall t1 t1' t2, t1 ==> t1' -> tm_app t1 t2 ==> tm_app t1' t2
  | e_app2   : forall v1 t2 t2', value v1 -> t2 ==> t2' -> tm_app v1 t2 ==> tm_app v1 t2'
  | e_iftrue : forall t2 t3, tm_if tm_true t2 t3 ==> t2
  | e_iffalse : forall t2 t3, tm_if tm_false t2 t3 ==> t3
  | e_if : forall t1 t1' t2 t3, t1 ==> t1' -> tm_if t1 t2 t3 ==> tm_if t1' t2 t3
  (** other rules **)
  | e_trust1 : forall t1 t1', t1 ==> t1' -> tm_trust t1 ==> tm_trust t1'
  | e_distrust1 : forall t1 t1', t1 ==> t1' -> tm_distrust t1 ==> tm_distrust t1'
  | e_check1 : forall t1 t1', t1 ==> t1' -> tm_check t1 ==> tm_check t1'
  | e_trustv : forall t, value t -> tm_trust t ==> t
  | e_distrustv : forall t, value t -> tm_distrust t ==> t
  | e_checkv : forall t, value t -> tm_check t ==> t
    where "t '==>' t'" := (step t t').

Hint Constructors step.

Remark value_dont_step : forall t, value t -> ~ exists t', t ==> t'.
Proof.
intros t v.
intro contra.
destruct contra.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
inversion v; subst; clear v.
inversion H; subst; clear H.
inversion H; subst; clear H.
Qed.



Lemma step_deterministic : forall t t', t ==> t' -> forall t'', t ==> t'' -> t' = t''.
Proof.
intros.
  generalize dependent t''.
 induction H ; intros.
  Case "ST_AppAbs".
      inversion H0; subst.
      reflexivity.
      inversion H4; subst.
      apply value_dont_step in H.
      destruct H; exists t2'. apply H5.
   Case "ST_App1".
      inversion H0; subst; clear H0.
      inversion H; subst.
      apply IHstep in H4.
      rewrite H4; auto; subst.
      apply value_dont_step in H3.
      destruct H3; exists t1'; auto.
  Case "ST_App2".
      inversion H1; subst; clear H1.
      apply value_dont_step in H5.
      destruct H5; exists t2'; auto; subst.
      apply value_dont_step in H.
      destruct H; exists t1'; auto; subst.
      apply IHstep in H6.
      rewrite H6; auto; subst.
  Case "ST_ifTrue".
      inversion H0; subst; auto; subst.
      inversion H4.
  Case "ST_ifFalse".
      inversion H0; subst.
      auto; subst.
      inversion H4.
  Case "ST_if".
      inversion H0 ; subst.
      inversion H; subst. inversion H; subst.
      apply IHstep in H5.
      rewrite H5; auto; subst.
  Case "ST_Trust".
      inversion H0; subst.
      apply IHstep in H2.
      rewrite H2; auto; subst.
      apply value_dont_step in H2.
      destruct H2; exists t1'; auto; subst.
  Case "ST_Distrust".
      inversion H0; subst.
      apply IHstep in H2.
      rewrite H2; auto; subst.
       apply value_dont_step in H2.
      destruct H2; exists t1'; auto; subst.
  Case "ST_Check".
      inversion H0; subst.
      apply IHstep in H2.
      rewrite H2; auto; subst.
       apply value_dont_step in H2.
      destruct H2; exists t1'; auto; subst.
  Case "ST_Trustv".
      inversion H0; subst.
       apply value_dont_step in H.
      destruct H; exists t1'; auto; subst ; auto.
      inversion H2; subst.
      auto. auto.
   Case "ST_Distrustv".
      inversion H0; subst.
       apply value_dont_step in H.
      destruct H.
      exists t1'; auto. auto.
   Case "ST_Checkv".
      inversion H0; subst.
      apply value_dont_step in H.
      destruct H.
      exists t1'; auto. auto.
Qed.
