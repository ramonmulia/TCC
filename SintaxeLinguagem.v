Require Export Types.

Inductive secty : Type :=
  | trust : secty
  | distrust : secty
  | dontcare : secty. 

Inductive ty : Type := 
  | ty_bool  : secty -> ty
  | ty_arrow : ty -> ty -> secty -> ty.

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_trust : tm -> tm
  | tm_distrust : tm -> tm
  | tm_check :  tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tm_abs x T t)
  | t_true : 
      value tm_true
  | t_false : 
      value tm_false.

Fixpoint subst (s:tm) (x:id) (t:tm): tm :=
  match t with
  | tm_var x' => if beq_id x x' then s else t
  | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst s x t1)) 
  | tm_app t1 t2 => tm_app (subst s x t1) (subst s x t2)
  | tm_trust t1 => tm_trust (subst s x t1 )
  | tm_distrust t1  => tm_distrust (subst s x t1 ) 
  | tm_check t1  => tm_check (subst s x t1 )
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)
  end.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tm_app t1 t2 ==> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tm_app v1 t2 ==> tm_app v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  | ST_Trust : forall t1 t1',
     t1 ==> t1' ->
     tm_trust t1 ==> tm_trust t1'
  | ST_Distrust : forall t t', 
     t ==> t' ->
     tm_distrust t ==> tm_distrust t'
  | ST_Check : forall t t',
    t ==> t' ->
    tm_check t ==> tm_check t'
  | ST_TrustV : forall  t,
    value t ->
    tm_trust t ==> t
  | ST_DistrustV : forall t,
    value t ->
    tm_distrust t ==> t
   | ST_CheckV : forall t,
    value t -> 
    tm_check t ==> t
     

where "t1 '==>' t2" := (step t1 t2).

Definition context := partial_map ty.

Definition lub_secty (x y : secty) : secty :=
  match x with
    | dontcare => dontcare
    | trust    => y
    | distrust  => match y with
                    | dontcare => dontcare
                    | _        => distrust    
                  end
  end.

Definition update_secty (t : ty) (s : secty) : ty :=
  match t with
    | ty_bool s' => ty_bool (lub_secty s s')
    | ty_arrow l r s' => ty_arrow l r (lub_secty s s')
  end.


(**
Inductive has_type : context -> term -> ty -> Prop :=
  | T_True : forall ctx, has_type ctx tm_true (ty_bool Trust)
  | T_False : forall ctx, has_type ctx tm_false (ty_bool Trust)
  | T_Var : forall ctx v ty,
        ctx v = Some ty -> has_type ctx (tm_var v) ty
  | T_Abs : forall ctx x t2 T1 T2,
        has_type (extend ctx x T1) t2 T2 ->
        has_type ctx (tm_abs x T1 t2) (arrow T1 T2 Trust)
  | T_App : forall ctx t1 t2 T11 T11' T12 s,
        has_type ctx t1 (arrow T11 T12 s) ->
        has_type ctx t2 T11' ->
        subtype T11' T11     ->
        has_type ctx (tm_app t1 t2) (update_secty T12 s)
  | T_If : forall ctx t1 t2 t3 T s,
        has_type ctx t1 (ty_bool s) ->
        has_type ctx t2 T     ->
        has_type ctx t3 T     ->
        has_type ctx (tm_if t1 t2 t3) T
  | T_Trust : forall ctx t T,
        has_type ctx t T ->
        has_type ctx (tm_trust t) (update_secty T Trust)
  | T_Untrust : forall ctx t T,
        has_type ctx t T ->
        has_type ctx (tm_distrust t) (update_secty T Untrust)
  | T_Check : forall ctx t T,
        has_type ctx t T ->
        sectyof T = Trust ->
        has_type ctx (tm_check t) T
  | T_Sub : forall ctx t T T',
        has_type ctx t T ->
        subtype T T'     ->
        has_type ctx t T'. 
**)

Lemma value_not_eval: forall (t:tm),
     value t ->
     ~ exists t', t ==> t'.
Proof.
intros t v.
intro contra.
destruct contra.
inversion H; subst; clear H.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v; subst.
inversion v.
Qed.

Theorem det_sem : forall t t' t'',
    t ==> t' ->
    t ==> t'' ->
    t' = t''.
Proof.
intros t t' t'' H H2.
  generalize dependent t''.
  induction H ; intros.
  Case "ST_AppAbs".
      inversion H2; subst.
      reflexivity.
      inversion H4; subst.
      apply value_not_eval in H.
      destruct H; exists t2'. apply H5.
   Case "ST_App1".
      inversion H2; subst; clear H2.
      inversion H; subst.
      apply IHstep in H4.
      rewrite H4; auto; subst.
      apply value_not_eval in H3.
      destruct H3; exists t1'; auto.
  Case "ST_App2".
      inversion H2; subst; clear H2.
      apply value_not_eval in H5.
      destruct H5; exists t2'; auto; subst.
      apply value_not_eval in H.
      destruct H; exists t1'; auto; subst.
      apply IHstep in H6.
      rewrite H6; auto; subst.
  Case "ST_ifTrue".
      inversion H2; subst; auto; subst.
      inversion H4.
  Case "ST_ifFalse".
      inversion H2; subst.
      auto; subst.
      inversion H4.
  Case "ST_if".
      inversion H2; subst.
      inversion H; subst. inversion H; subst.
      apply IHstep in H5.
      rewrite H5; auto; subst.
  Case "ST_Trust".
      inversion H2; subst.
      apply IHstep in H1.
      rewrite H1; auto; subst.
      apply value_not_eval in H1.
      destruct H1; exists t1'; auto; subst.
  Case "ST_Distrust".
      inversion H2; subst.
      apply IHstep in H1.
      rewrite H1; auto; subst.
      apply value_not_eval in H1.
      destruct H1; exists t'; auto; subst.
  Case "ST_Check".
      inversion H2; subst.
      apply IHstep in H1.
      rewrite H1; auto; subst.
      apply value_not_eval in H1.
      destruct H1; exists t'; auto; subst.
  Case "ST_Trustv".
      inversion H2; subst.
      apply value_not_eval in H.
      destruct H; exists t1'; auto; subst ; auto.
      inversion H2; subst.
      auto. auto.
   Case "ST_Distrustv".
      inversion H2; subst.
      apply value_not_eval in H.
      destruct H.
      exists t'; auto. auto.
   Case "ST_Checkv".
      inversion H2; subst.
      apply value_not_eval in H.
      destruct H.
      exists t'; auto. auto.
Qed.