Require Import SfLib Ty.

(** definition of ordering between types **)

Inductive sec_ordering : secty -> secty -> Prop :=
  | so_untrustdontcare : sec_ordering Untrust DontCare 
  | so_trustuntrust : sec_ordering Trust Untrust
  | so_trustdontcare : sec_ordering Trust DontCare
  | so_refl : forall t, sec_ordering t t.

Inductive subtype : ty -> ty -> Prop :=
  | s_base : forall s s', sec_ordering s s' -> subtype (ty_bool s) (ty_bool s')
  | s_arrow : forall T1 T2 T1' T2' s1 s2,
              subtype T1' T1 ->
              subtype T2 T2' ->
              sec_ordering s1 s2 ->
              subtype (arrow T1 T2 s1) (arrow T1' T2' s2).

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first ; [Case_aux c "s_base" | Case_aux c "s_arrow"].

Hint Constructors sec_ordering subtype.

Definition sectyof (t : ty) : secty :=
  match t with
    | ty_bool s => s
    | arrow _ _ s => s
  end.

(** least upper bound on sec types **)

Definition lub_secty (x y : secty) : secty :=
  match x with
    | DontCare => DontCare
    | Trust    => y
    | Untrust  => match y with
                    | DontCare => DontCare
                    | Untrust  => Untrust     
                    | Trust    => Untrust
                  end
  end.

Definition update_secty (t : ty) (s : secty) : ty :=
  match t with
    | ty_bool s' => ty_bool (lub_secty s s')
    | arrow l r s' => arrow l r (lub_secty s s')
  end.

Remark sec_ordering_trans : forall s1 s2 s3, sec_ordering s1 s2 -> sec_ordering s2 s3 -> sec_ordering s1 s3.
Proof.
intros.
inversion H; subst.
inversion H0; subst.
constructor.
destruct s3.
constructor.
constructor.
constructor.
destruct s3.
constructor.
constructor.
constructor.
auto.
Qed.

Remark subtype_refl : forall T, subtype T T.
Proof.
intros.
induction T.
constructor.
constructor.
constructor.
auto.
auto.
constructor.
Qed.


Remark subtype_trans : forall T1 T2 T3, subtype T1 T2 -> subtype T2 T3 -> subtype T1 T3.
Proof.
intros T1 T2 T3.
  generalize dependent T1 ; generalize dependent T3.
  induction T2.
  intros.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  inversion H3; subst; clear H3.
  inversion H1; subst; clear H1.
  constructor. constructor.
  inversion H1; subst; clear H1.
  constructor. constructor.
  constructor. constructor.
  inversion H1; subst; clear H1.
  constructor. constructor.
  inversion H1; subst; clear H1.
  constructor. constructor.
  constructor. constructor.
  constructor. constructor.
  constructor. constructor.
  intros.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  constructor.
  apply IHT2_1.
  assumption. assumption.
  apply IHT2_2.
  assumption. assumption.
  inversion H9; subst; clear H9.
  inversion H7; subst; clear H7.
  constructor. constructor.
  inversion H7; subst; clear H7.
  constructor.
 inversion H7; subst; clear H7.
  constructor.
  assumption.
Qed.
  
  




Remark sec_ordering_lub : forall s s', sec_ordering s (lub_secty s' s).
Proof with eauto.
intros.
destruct s. destruct s'.
constructor. constructor.
constructor. destruct s'.
constructor. constructor.
constructor. destruct s'.
constructor. constructor.
constructor.
Qed.


Remark update_secty__subtype : forall T s, subtype T (update_secty T s).
Proof with eauto.
intros.
destruct s. destruct T. destruct s.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. apply subtype_refl.
apply subtype_refl. destruct s. constructor. constructor.
constructor. destruct T. destruct s. constructor.
constructor. constructor. constructor. constructor.
constructor. destruct T1. destruct T2. destruct s.
destruct s0. destruct s1. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor.
apply subtype_refl. apply subtype_refl. constructor.
destruct s. constructor. constructor. constructor.
constructor. constructor. apply subtype_refl. apply subtype_refl.
constructor. apply subtype_refl. destruct s. constructor.
constructor. constructor. destruct T. destruct s.
constructor. constructor. constructor. constructor.
constructor. constructor. constructor. apply subtype_refl.
apply subtype_refl. destruct s. constructor. constructor.
constructor.
Qed. 


Remark update_secty_ident : forall T s, update_secty T s = update_secty (update_secty T s) s.
Proof.
intros.
induction s. destruct T.
destruct s. reflexivity.
reflexivity. reflexivity.
reflexivity. destruct T.
destruct s. reflexivity.
reflexivity. reflexivity.
destruct s. reflexivity.
reflexivity. reflexivity.
destruct T. reflexivity.
reflexivity.
Qed.

Remark secty_update_eq :forall T T' s, subtype T T' -> sectyof T = sectyof (update_secty T s) -> sectyof T' = sectyof (update_secty T' s).
Proof.
intros.
inversion H; subst.
inversion H1; subst.
destruct s. reflexivity.
reflexivity. reflexivity.
destruct s. reflexivity.
reflexivity. simpl in *.
rewrite H0 in H. inversion H; subst.
inversion H4. destruct s.
reflexivity. reflexivity.
reflexivity. assumption.
inversion H3; subst.
destruct s. reflexivity.
reflexivity. reflexivity.
subst. destruct s. 
reflexivity. reflexivity.
simpl in *. rewrite H0 in H.
inversion H; subst.
inversion H12; subst.
destruct s. reflexivity.
reflexivity. reflexivity.
assumption.
Qed.

Remark update_secty_mono : forall T T' s s', subtype T T' -> sec_ordering s s' -> subtype (update_secty T s) (update_secty T' s').
Proof.
intros.
inversion H0; subst; clear H0.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
constructor. constructor.
constructor. constructor.
constructor. constructor.
constructor. destruct s'.
constructor. constructor.
constructor. constructor.
assumption. assumption.
inversion H2; subst; clear H2.
constructor. constructor.
constructor. destruct s2.
constructor. constructor.
constructor. inversion H; subst; clear H.
inversion H0; subst; clear H0.
constructor. constructor.
constructor. constructor.
constructor. constructor.
constructor. destruct s'.
constructor. constructor.
constructor. constructor.
assumption. assumption.
inversion H2; subst; clear H2.
constructor. constructor.
constructor. destruct s2.
constructor. constructor.
constructor. inversion H; subst; clear H.
inversion H0; subst; clear H0.
constructor. constructor.
constructor. constructor.
constructor. constructor.
constructor. destruct s'.
constructor. constructor.
constructor. constructor.
assumption. assumption.
inversion H2; subst; clear H2.
constructor. constructor.
constructor. destruct s2.
constructor. constructor.
constructor. inversion H; subst; clear H.
inversion H0; subst; clear H0.
constructor. destruct s'.
constructor. constructor.
constructor. constructor.
destruct s'. constructor.
constructor. constructor.
constructor. destruct s'.
constructor. constructor.
constructor. constructor.
destruct s'. destruct s'0.
constructor. constructor.
constructor. constructor.
destruct s'0. constructor.
constructor. constructor.
constructor. assumption.
assumption. inversion H2; subst; clear H2.
destruct s'. constructor.
constructor. constructor.
destruct s'. constructor.
constructor. constructor.
destruct s'. constructor.
constructor. constructor.
constructor.
Qed.

Remark lub_secty_sym : forall s s', lub_secty s s' = lub_secty s' s.
Proof.
intros.
destruct s.
destruct s'.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
destruct s'.
reflexivity.
reflexivity.
reflexivity.
Qed.

Remark subtype_bool_lub_secty : forall s s', subtype (ty_bool s) (ty_bool (lub_secty s s')).
Proof.
intros.
constructor.
destruct s.
destruct s'.
constructor.
constructor.
constructor.
destruct s'.
constructor.
constructor.
constructor.
constructor.
Qed.

