
Require Import SfLib Syntax Ty Subtype Semantics.

(** Definition of the type system -- non syntax directed version**)

Definition context := id -> (option ty).
Definition empty : context := (fun _ => None). 
Definition extend (Gamma : context) (x:id) (T : ty) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.


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
                                     
Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "T_True"  | Case_aux c "T_False"   | Case_aux c "T_Var"   |
           Case_aux c "T_Abs"   | Case_aux c "T_App"     | Case_aux c "T_If"    |
           Case_aux c "T_Trust" | Case_aux c "T_Untrust" | Case_aux c "T_Check" |
           Case_aux c "T_Sub"].

Hint Constructors has_type.


(** inversion lemmas for subtyping **)

Lemma sub_inversion_base : 
  forall T s, subtype T (ty_bool s) -> exists s',
              sec_ordering s' s /\ T = (ty_bool s').
Proof with eauto.
intros T s H.
destruct T.
inversion H ; subst. clear H.
inversion H2. subst.
exists Untrust.
split.
constructor.
reflexivity.
exists Trust.
split.
constructor.
reflexivity.
exists Trust.
split.
constructor.
reflexivity.
subst.
exists s.
split.
constructor.
reflexivity.
exists s.
split.
constructor.
inversion H.
Qed.


Lemma sub_inversion_basel :
  forall T s, subtype (ty_bool s) T -> exists s', sec_ordering s s' /\ T = (ty_bool s').
Proof.
intros.
destruct T.
inversion H; subst; clear H.
inversion H2; subst; clear H2.
exists DontCare.
split.
constructor.
reflexivity.
exists Untrust.
split.
constructor.
reflexivity.
exists DontCare.
split.
constructor.
reflexivity.
exists s0.
split.
constructor.
reflexivity.
inversion H.
Qed.


Lemma sub_inversion_arrow : 
  forall T T1 T2 s, subtype T (arrow T1 T2 s) ->
    exists s', exists T1', exists T2',
      T = (arrow T1' T2' s') /\ subtype T1 T1' /\ subtype T2' T2 /\ sec_ordering s' s.
Proof.
intros T T1 T2 s H.
  remember (arrow T1 T2 s) as V.
  generalize dependent T2. generalize dependent T1.
intros.
inversion H. subst. clear H.
exists Trust.
exists (ty_bool Trust).
inversion H0; subst; clear H0.
inversion H2. subst.
inversion H2. subst.
inversion H2. subst.
inversion H2. subst.
inversion H; subst; clear H.
exists s1.
subst.
exists T0.
exists T3.
split.
reflexivity.
split.
assumption.
split.
assumption.
assumption.
Qed.

(** canonical forms lemmas **)

Lemma canonical_forms_arrows : forall ctx t T1 T2 s,
  has_type ctx t (arrow T1 T2 s) ->
  value t ->
  exists x, exists S1, exists s2,
    t = tm_abs x S1 s2.
Proof with eauto.
intros.
 remember (arrow T1 T2 s) as T.
 has_type_cases (induction H) Case; 
 inversion HeqT; subst; intros; try solve by inversion.
 Case "T_Var".
    inversion H0.
    inversion H2. 
    inversion H2. 
  Case "T_Abs".
    exists x.
    exists T1.
    exists t2.
    reflexivity.
  Case "T_App".
    inversion H0.
    inversion H3. 
    inversion H3.
  Case "T_If".
    inversion H0.
    inversion H4. 
    inversion H4.
  Case "T_Trust".
    inversion H0.
    inversion H1.
    inversion H1.
  Case "T_Untrust".
    inversion H0.
    inversion H1.
    inversion H1.
  Case "T_Check".
    inversion H0.
    inversion H3.
    inversion H3.
  Case "T_Sub".
   destruct T.
    apply IHhas_type.
    inversion H1.
    assumption.
    apply IHhas_type.
    apply sub_inversion_arrow in H1.
    destruct H1 as [s'].
    destruct H1 as [T1'].
    destruct H1 as [T2']. 
    destruct H1.
    inversion H1. subst.
    Admitted.



Lemma canonical_forms_bool : 
  forall ctx t s, has_type ctx t (ty_bool s) -> 
    value t -> t = tm_true \/ t = tm_false.
Proof with eauto.
intros ctx t s Hty Hv.
  remember (ty_bool s) as T.
  has_type_cases (induction Hty) Case; 
  subst; intros; try solve by inversion.
  Case "T_True".
   left.
   reflexivity.
  Case "T_False". 
   right.
   reflexivity.
  Case "T_Var".
    inversion Hv.
    inversion H0.
    inversion H0.
  Case "T_App".
    inversion Hv.
    inversion H0.
    inversion H0.
  Case "T_If".
    inversion Hv.
    inversion H.
    inversion H.
  Case "T_Trust".
     inversion Hv.
    inversion H.
    inversion H.
  Case "T_Untrust".
     inversion Hv.
    inversion H.
    inversion H.
  Case "T_Check".
     inversion Hv.
    inversion H0.
    inversion H0.
  Case "T_Sub".
    apply IHHty.
    apply sub_inversion_base in H.
    destruct H as [s'].
    destruct H.
    Admitted.

(** progress *)

Theorem progress : 
  forall t T, has_type empty t T ->
    value t \/ exists t', t ==> t'.
Proof with eauto.
intros t T Ht.
  remember empty as ctx.
  revert Heqctx.
  has_type_cases (induction Ht) Case;
    intros HeqCtx; subst...
  Case "T_Var".
    inversion H.
  Case "T_App".
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
        destruct (canonical_forms_arrows empty t1 T11 T12 s)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists (subst x t2 t12)...
      SSCase "t2 steps".
          destruct H1 as [t2' Hstp]. exists (tm_app t1 t2')...
    SCase "t1 steps".
      destruct H0 as [t1' Hstp]. exists (tm_app t1' t2)...
  Case "T_If".
    right.
    destruct IHHt1.
    SCase "t1 is a value"...
      assert (t1 = tm_true \/ t1 = tm_false) 
        by (eapply canonical_forms_bool; eauto).
      inversion H0; subst...
      destruct H. rename x into t1'. eauto.
  Case "T_Trust".
     right.
     destruct IHHt; subst...
     destruct H as [t' Hstp].
     exists (tm_trust t'); subst...
   Case "T_Untrust".
     right.
     destruct IHHt; subst...
     destruct H as [t' Hstp].
     exists (tm_distrust t'); subst...
   Case "T_Check".
     right.
     destruct IHHt; subst...
     destruct H0 as [t' Hstp].
     exists (tm_check t'); subst...
Qed.

(** inversion lemmas for the typing relation *)

Lemma typing_inversion_abs : 
  forall ctx x S1 s2 T, has_type ctx (tm_abs x S1 s2) T ->
    exists S2,  subtype (arrow S1 S2 Trust) T /\
      has_type (extend ctx x S1) s2 S2.
Proof with eauto.
 intros Gamma x S1 t2 T H.
  remember (tm_abs x S1 t2) as t.
  has_type_cases (induction H) Case; 
    inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Abs".
    exists T2.
    split.
    apply subtype_refl.
    assumption.
  Case "T_Sub".
    apply IHhas_type in H1.
    destruct H1.
    destruct H1. 
    exists x0.
    split.
    eapply subtype_trans.
    apply H1.
    apply H0.
    assumption.
Qed.
    


Lemma typing_inversion_var : 
  forall ctx x T, has_type ctx (tm_var x) T ->
    exists S, ctx x = Some S /\ subtype S T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (tm_var x) as t.
  has_type_cases (induction Hty) Case; intros; 
    inversion Heqt; subst; try solve by inversion.
  Case "T_Var".
    exists ty.
    split; auto. 
    apply subtype_refl.
  Case "T_Sub".
    apply IHHty in H0.
    destruct H0 as [T2].
    destruct H0.
    exists T2.
    split.
    assumption.
    eapply subtype_trans.
    apply H1.
    apply H.
Qed.

Lemma typing_inversion_true : 
  forall ctx T, has_type ctx tm_true T ->
    subtype (ty_bool Trust) T.
Proof with eauto.
intros Gamma x H.
  remember (tm_true ) as t.
  has_type_cases (induction H) Case; intros; 
    inversion Heqt; subst; try solve by inversion.
  Case "T_True".
    apply subtype_refl.
  Case "T_Sub".
    apply IHhas_type in H1.
     eapply subtype_trans.
    apply H1.
    apply H0.
Qed.



Lemma typing_inversion_false :
  forall ctx T, has_type ctx tm_false T ->
    subtype (ty_bool Trust) T.
Proof with eauto.
intros Gamma x H.
  remember (tm_false ) as t.
  has_type_cases (induction H) Case; intros; 
    inversion Heqt; subst; try solve by inversion.
  Case "T_False".
    apply subtype_refl.
  Case "T_Sub".
    apply IHhas_type in H1.
     eapply subtype_trans.
    apply H1.
    apply H0.
Qed.

Lemma typing_inversion_app :
  forall ctx t1 t2 T2, has_type ctx (tm_app t1 t2) T2 ->
    exists T1, exists T11, exists s, 
      has_type ctx t1 (arrow T1 T2 s) /\ has_type ctx t2 T11 /\ subtype T11 T1 /\ sectyof T2 = sectyof (update_secty T2 s).
Proof with eauto.
 intros Gamma t1 t2 T2 Hty.
  remember (tm_app t1 t2) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_App".
Admitted.

Lemma typing_inversion_trust : 
  forall ctx t T, has_type ctx (tm_trust t) T ->
    exists T', has_type ctx t T' /\ subtype (update_secty T' Trust) T.
Proof with eauto.
intros Gamma t1 t2 H.
  remember (tm_trust t1) as t.
  has_type_cases (induction H) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_Trust".
    exists T.
    split.
    assumption.
    destruct T.
    simpl.
    constructor.
    constructor.
    simpl.
     constructor.
    apply subtype_refl.
    apply subtype_refl.
    constructor.
  Case "T_Sub".
     apply IHhas_type in H1.
     destruct H1.
     exists x.
     split.
     destruct H1.
     assumption.
     destruct x.
     simpl in *.
     eapply subtype_trans.
     destruct H1.
     apply H2.
     assumption.
     eapply subtype_trans.
     simpl in *.
     destruct H1.
     apply H2.
     assumption.     
Qed.
 

Lemma typing_inversion_distrust :
  forall ctx t T, has_type ctx (tm_distrust t) T ->
    exists T', has_type ctx t T' /\ subtype (update_secty T' Untrust) T.
Proof with eauto.
intros Gamma t1 t2 H.
  remember (tm_distrust t1) as t.
  has_type_cases (induction H) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_Untrust".
    exists T.
    split.
    assumption.
    destruct T.
    simpl.
    constructor.
    constructor.
    simpl.
     constructor.
    apply subtype_refl.
    apply subtype_refl.
    constructor.
  Case "T_Sub".
     apply IHhas_type in H1.
     destruct H1.
     exists x.
     split.
     destruct H1.
     assumption.
     destruct x.
     simpl in *.
     eapply subtype_trans.
     destruct H1.
     apply H2.
     assumption.
     eapply subtype_trans.
     simpl in *.
     destruct H1.
     apply H2.
     assumption.
Qed.     

Lemma typing_inversion_check : 
  forall ctx t T, has_type ctx (tm_check t) T ->
    exists T', has_type ctx t T' /\ subtype T' T /\ sectyof T' = Trust.
Proof with eauto.
intros Gamma t1 t2 H.
  remember (tm_check t1) as t.
  has_type_cases (induction H) Case; intros;
    inversion Heqt; subst; try solve by inversion.
 Case "T_Check".
    exists T.
    split.
    assumption.
    split.
    apply subtype_refl.
    assumption.
  Case "T_Sub".
     apply IHhas_type in H1.
     destruct H1.
     exists x.
     split.
     destruct H1.
     assumption.
     split.
     destruct x.
     eapply subtype_trans.
     destruct H1.
     destruct H2.
     apply H2.
     assumption.
     eapply subtype_trans.
     destruct H1.
     destruct H2.
     apply H2.
     assumption.
     destruct H1.
     destruct H2.
     assumption.
Qed.     

Lemma typing_inversion_if :
  forall ctx t1 t2 t3 T, has_type ctx (tm_if t1 t2 t3) T ->
    exists s, has_type ctx t1 (ty_bool s) /\ has_type ctx t2 T /\ has_type ctx t3 T.
Proof with eauto.
intros Gamma t1 t2 t3 T H.
  remember (tm_if t1 t2 t3) as t.
  has_type_cases (induction H) Case; intros;
    inversion Heqt; subst; try solve by inversion.
Case "T_If".
    exists s.
    split.
    assumption.
    split.
    assumption.
    assumption.
  Case "T_Sub".
     apply IHhas_type in H1.
     destruct H1.
     exists x.
     split.
     destruct H1.
     assumption.
     split.
     destruct H1.
     destruct H2.
     eapply T_Sub.
     apply H2.
     assumption.
     destruct H1.
     destruct H2.
     eapply T_Sub.
     apply H3.
     assumption.
Qed.
     

Lemma abs_arrow : 
  forall x S1 s2 T1 T2 s,
    has_type empty (tm_abs x S1 s2) (arrow T1 T2 s) ->
    subtype T1 S1 /\ has_type (extend empty x S1) s2 T2.
Proof with eauto.
intros x S1 s2 T1 T2 s H.
  apply typing_inversion_abs in H.
  destruct H as [S2 [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Hsub1; subst; clear Hsub1.
  destruct Hsub2.
  destruct H0.
  split.
   assumption.
  inversion H0. subst. clear H0.
  inversion H2; subst; clear H2.
  eapply T_Sub in Hty.
  apply Hty.
  constructor.
  constructor.
  eapply T_Sub in Hty.
  apply Hty.
  constructor.
  constructor.
  eapply T_Sub in Hty.
  apply Hty.
  constructor.
  constructor.
  assumption.
  subst.
  eapply T_Sub in Hty.
  apply Hty.
  assumption.
Qed.



(** context invariance **)

Inductive appears_free_in : id -> term -> Prop :=
  | afi_var : forall i, appears_free_in i (tm_var i)
  | afi_app1 : forall i t1 t2, appears_free_in i t1 ->
                               appears_free_in i (tm_app t1 t2)
  | afi_app2 : forall i t1 t2, appears_free_in i t2 ->
                               appears_free_in i (tm_app t1 t2)
  | afi_abs : forall i x T t, i <> x -> appears_free_in i t ->
                              appears_free_in i (tm_abs x T t)
  | afi_if1 : forall i t1 t2 t3, appears_free_in i t1 ->
                                 appears_free_in i (tm_if t1 t2 t3)
  | afi_if2 : forall i t1 t2 t3, appears_free_in i t2 ->
   appears_free_in i (tm_if t1 t2 t3)
  | afi_if3 : forall i t1 t2 t3, appears_free_in i t3 ->
                                 appears_free_in i (tm_if t1 t2 t3)
  | afi_trust : forall i t, appears_free_in i t ->
                            appears_free_in i (tm_trust t)
  | afi_distrust : forall i t, appears_free_in i t ->
                               appears_free_in i (tm_distrust t)
  | afi_check : forall i t, appears_free_in i t ->
                            appears_free_in i (tm_check t).

Hint Constructors appears_free_in.
  
Lemma context_invariance :
  forall ctx ctx' t S, has_type ctx t S ->
    (forall x, appears_free_in x t -> ctx x = ctx' x) ->
    has_type ctx' t S.
Proof with eauto.
  intros. generalize dependent ctx'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs. apply IHhas_type. intros x0 Hafi.
    unfold extend. remember (beq_id x x0) as e.
    destruct e...
    apply Heqv.
    eapply afi_abs in Hafi...
    apply beq_id_false_not_eq.
    rewrite -> Heqe.
    apply beq_id_sym.
  Case "T_App".
    eapply T_App.
    apply IHhas_type1.
    intros.
    apply Heqv.
    constructor.
    assumption.
    apply IHhas_type2.
    intros.
    apply Heqv.
    apply afi_app2.
    assumption.
    assumption.
  Case "T_If".
    eapply T_If.
    apply IHhas_type1.
    intros.
    apply Heqv.
    constructor.
    assumption.
    apply IHhas_type2.
    intros.
    apply Heqv.
    apply afi_if2.
    assumption.
    apply IHhas_type3.
    intros.
    apply Heqv.
    apply afi_if3.
    assumption.
Qed.
    
    
Lemma free_in_context :
  forall i ctx t T,
    appears_free_in i t ->
    has_type ctx t T ->
    exists T', ctx i = Some T'.
Proof with eauto.
intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; 
      subst; inversion Hafi; subst...
  Case "T_Abs".
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    unfold extend in Hctx. apply not_eq_beq_id_false in H2.
    rewrite beq_id_sym in H2.
    rewrite H2 in Hctx.
    assumption.
Qed.

(** substitution lemma **)

Lemma substitution_preserves_typing : 
  forall Gamma x U v t S,
    has_type (extend Gamma x U) t S ->
    has_type empty v U ->
    has_type Gamma (subst x v t) S.
Proof with eauto.
Admitted.

(** preservation **)

Theorem preservation : 
  forall t t' T, has_type empty t T ->
    t ==> t' -> has_type empty t' T.
Proof with eauto.
intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    inversion HE; subst...
    SCase "ST_AppAbs".
      apply abs_arrow in HT1.
      destruct HT1.
      apply substitution_preserves_typing with T.
Admitted.


