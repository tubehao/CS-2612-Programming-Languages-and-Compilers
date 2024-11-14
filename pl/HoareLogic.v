Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.Syntax.
Require Import PL.DenotationalBasic.
Require Import PL.DenotationalRels.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Module HoareSimpleWhile.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile3_Properties.



(** 首先定义断言。*)

Definition assertion: Type := state -> Prop.

Definition derives (P Q: assertion): Prop :=
  forall s, P s -> Q s.

Definition logical_equiv (P Q: assertion): Prop :=
  forall s, P s <-> Q s.

Definition andp (P Q: assertion): assertion :=
  fun s => P s /\ Q s.

Definition exp (P: Z -> assertion): assertion :=
  fun s => exists n, P n s.

(** 下面的Notation定义可以跳过*)

Declare Custom Entry assn_entry.

Notation "( x )" := x
  (in custom assn_entry, x custom assn_entry at level 99).
Notation "x" := x
  (in custom assn_entry at level 0, x constr at level 0).
Notation "'Assn' ( P )" := P
  (at level 2, P custom assn_entry at level 99).
Notation "f x" := (f x)
  (in custom assn_entry at level 1, only parsing,
   f custom assn_entry,
   x custom assn_entry at level 0).

Notation "x && y" := (andp x y)
  (in custom assn_entry at level 14, left associativity).

Notation "'exists' x , P" := (exp (fun x: Z => P))
  (in custom assn_entry at level 20,
      x constr at level 0,
      P custom assn_entry).

Notation " P |-- Q " := (derives P Q)
  (at level 80, no associativity).

Notation " P --||-- Q " := (logical_equiv P Q)
  (at level 80, no associativity).

(** 下面定义霍尔三元组。*)

Inductive HoareTriple: Type :=
| BuildHoareTriple: assertion -> com -> assertion -> HoareTriple.

Notation "{{ P }}  c  {{ Q }}" :=
  (BuildHoareTriple P c Q) (at level 1,
                            P custom assn_entry at level 99,
                            Q custom assn_entry at level 99,
                            c custom prog_lang_entry at level 99).

(** 一个布尔表达式为真是一个断言：*)

Definition eb2assn (b: expr_bool): assertion :=
  fun s => ⟦ b ⟧ s = true.

(** 断言中描述整数的逻辑表达式（区分于程序表达式）：*)

Definition exprZ: Type := state -> Z.

(** 一个程序中的整数类型可以用作逻辑表达式：*)

Definition ei2exprZ (e: expr_int): exprZ :=
  ⟦ e ⟧.

(** 断言中的等号：*)

Definition exprZ_eq (e1 e2: exprZ): assertion :=
  fun s => e1 s = e2 s.

(** 程序状态中的替换：*)

Definition state_subst (s: state) (x: var_name) (v: Z): state :=
  fun y =>
    if String.eqb x y
    then v
    else s y.

(** 断言中的替换：*)

Definition assn_subst (P: assertion) (x: var_name) (v: exprZ): assertion :=
  fun s =>
    P (state_subst s x (v s)).

Definition exprZ_subst (u: exprZ) (x: var_name) (v: exprZ): exprZ :=
  fun s =>
    u (state_subst s x (v s)).

(** 下面的Notation定义可以跳过*)

Notation "[[ e ]]" := (eb2assn e)
  (in custom assn_entry at level 0,
      e custom prog_lang_entry at level 99,
      only printing).

Notation "[[ e ]]" := (ei2exprZ e)
  (in custom assn_entry at level 0,
      e custom prog_lang_entry at level 99,
      only printing).

Ltac any_expr e :=
  match goal with
  | |- assertion => exact (eb2assn e)
  | |- exprZ => exact (ei2exprZ e)
  | _ => match type of e with
         | expr_bool => exact (eb2assn e)
         | expr_int => exact (ei2exprZ e)
         end
  end.

Notation "[[ e ]]" := (ltac:(any_expr e))
  (in custom assn_entry,
      e custom prog_lang_entry at level 99,
      only parsing).

Notation "u == v" := (exprZ_eq u v)
  (in custom assn_entry at level 10,
      u custom assn_entry,
      v custom assn_entry,
      no associativity).

Tactic Notation "unfold_substs" :=
  unfold exprZ_subst, assn_subst.

Tactic Notation "unfold_substs" "in" ident(H) :=
  unfold exprZ_subst, assn_subst in H.

Notation "'exprZ_subst' u x v" := (exprZ_subst u x v)
  (in custom assn_entry at level 1,
      u custom assn_entry at level 0,
      x custom assn_entry at level 0,
      v custom assn_entry at level 0).

Notation "'assn_subst' P x v" := (assn_subst P x v)
  (in custom assn_entry at level 1,
      P custom assn_entry at level 0,
      x custom assn_entry at level 0,
      v custom assn_entry at level 0).

(** 下面定义有效：*)

Definition valid: HoareTriple -> Prop :=
  fun ht =>
  match ht with
  | BuildHoareTriple P c Q =>
      forall s1 s2,
        P s1 ->
        (s1, s2) ∈ ⟦ c ⟧ ->
        Q s2
  end.

Lemma hoare_skip_sound:
  forall P: assertion,
    valid {{ P }} skip {{ P }}.
Proof.
  unfold valid.
  unfold_sem.
  sets_unfold.
  intros.
  rewrite <- H0; tauto.
Qed.

Lemma hoare_seq_sound:
  forall (P Q R: assertion) (c1 c2: com),
    valid {{ P }} c1 {{ Q }} ->
    valid {{ Q }} c2 {{ R }} ->
    valid {{ P }} c1; c2 {{ R }}.
Proof.
  unfold valid.
  unfold_sem.
  intros.
  destruct_concat H2 as [s1' H2 H3].
  specialize (H _ _ H1 H2).
  specialize (H0 _ _ H H3).
  apply H0.
Qed.

(************)
(** 习题：  *)
(************)

Lemma hoare_if_sound:
  forall (P Q: assertion) (e: expr_bool) (c1 c2: com),
    valid {{ P && [[ e ]] }} c1 {{ Q }} ->
    valid {{ P && [[! e ]] }} c2 {{ Q }} ->
    valid {{ P }} if (e) then { c1 } else { c2 } {{ Q }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Lemma hoare_while_sound:
  forall (P: assertion) (e: expr_bool) (c: com),
    valid {{ P && [[ e ]] }} c {{ P }} ->
    valid {{ P }} while (e) do { c } {{ P && [[! e ]] }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma state_subst_fact:
  forall (s1 s2: state) (x: var_name),
    (forall y, x <> y -> s2 y = s1 y) ->
      state_subst s2 x (s1 x) = s1.
Proof.
  intros.
  apply functional_extensionality.
  intros y.
  unfold state_subst.
  destruct (String.eqb x y) eqn:EQ.
  + apply String.eqb_eq in EQ.
    rewrite EQ.
    reflexivity.
  + apply String.eqb_neq in EQ.
    apply H; tauto.
Qed.

(************)
(** 习题：  *)
(************)

Lemma hoare_asgn_fwd_sound:
  forall P x e,
    valid {{ P }} x = e {{ exists x', exprZ_subst [[ e ]] x [[ x' ]] == [[ x ]] && assn_subst P x [[ x' ]] }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Lemma hoare_conseq_sound:
  forall (P P' Q Q': assertion) (c: com),
    valid {{ P' }} c {{ Q' }} ->
    derives P P' ->
    derives Q' Q ->
    valid {{ P }} c {{ Q }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 下面定义可证：*)

Inductive provable: HoareTriple -> Prop :=
| hoare_skip:
    forall P: assertion, 
      provable {{ P }} skip {{ P }}
| hoare_seq:
    forall (P Q R: assertion) (c1 c2: com),
      provable {{ P }} c1 {{ Q }} ->
      provable {{ Q }} c2 {{ R }} ->
      provable {{ P }} c1; c2 {{ R }}
| hoare_if:
    forall (P Q: assertion) (e: expr_bool) (c1 c2: com),
      provable {{ P && [[ e ]] }} c1 {{ Q }} ->
      provable {{ P && [[! e ]] }} c2 {{ Q }} ->
      provable {{ P }} if (e) then { c1 } else { c2 } {{ Q }}
| hoare_while:
    forall (P: assertion) (e: expr_bool) (c: com),
      provable {{ P && [[ e ]] }} c {{ P }} ->
      provable {{ P }} while (e) do { c } {{ P && [[! e ]] }}
| hoare_asgn_fwd:
    forall P x e,
      provable {{ P }} x = e {{ exists x', exprZ_subst [[ e ]] x [[ x' ]] == [[ x ]] && assn_subst P x [[ x' ]] }}
| hoare_conseq:
    forall (P P' Q Q': assertion) (c: com),
      provable {{ P' }} c {{ Q' }} ->
      P |-- P' ->
      Q' |-- Q ->
      provable {{ P }} c {{ Q }}.

(** 将前面证明的结论连接起来，即可证明霍尔逻辑的可靠性。*)

Theorem hoare_sound: forall ht,
  provable ht -> valid ht.
Proof.
  intros.
  induction H.
  + apply hoare_skip_sound.
  + apply (hoare_seq_sound _ Q); tauto.
  + apply hoare_if_sound; tauto.
  + apply hoare_while_sound; tauto.
  + apply hoare_asgn_fwd_sound; tauto.
  + apply (hoare_conseq_sound P P' Q Q'); tauto.
Qed.


End HoareSimpleWhile.

(** * 符号执行与验证条件生成 *)







