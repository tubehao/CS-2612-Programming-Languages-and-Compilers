Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.SimpleProofsAndDefs.
Require Import PL.InductiveType.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 请证明常值函数都是单调的。*)

Lemma const_mono: forall a: Z,
  mono (fun x => a).
Proof.
  unfold mono.
  intros.
  simpl.
  nia.
Qed.
(************)
(** 习题：  *)
(************)

(** 请证明函数加法能保持单调性。*)

Lemma mono_func_plus: forall f g,
  mono f ->
  mono g ->
  mono (func_plus f g).
Proof.
  unfold mono, func_plus.
  intros.
  pose proof H n m H1.
  pose proof H0 n m H1.
  nia.
Qed.


(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面关于结合律的性质。*)

Definition power2 (f: Z -> Z -> Z) (x: Z): Z :=
  f x x.

Definition power4 (f: Z -> Z -> Z) (x: Z): Z :=
  f x (f x (f x x)).

Fact power2_power2: forall f a,
  assoc f ->
  power2 f (power2 f a) = power4 f a.
Proof.
  intros.
  unfold power2, power4.
  rewrite H .
  rewrite H.
  rewrite H.
  reflexivity.
Qed.



(************)
(** 习题：  *)
(************)

Lemma size_nonneg: forall t,
  0 <= tree_size t.
Proof.
  induction t.
  - simpl. lia.
  - simpl. rewrite IHt1. lia.
Qed. 


(************)
(** 习题：  *)
(************)
Fact reverse_involutive: forall t,
  tree_reverse (tree_reverse t) = t.
Proof. 
  intros.
  induction t; simpl.
  - reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.


Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Proof.
  intros t t1 k t2 H.
  induction t as [| l IHl v r IHr].
    discriminate H. 
  - simpl in H. 
    injection H as H1 H2 H3.
    rewrite <- H1, <- H3. 
    pose proof (reverse_involutive l) .
    pose proof (reverse_involutive r).
    rewrite H0, H.
    rewrite H2.

    reflexivity. 
Qed.


(************)
(** 习题：  *)
(************)

(** 下面的_[left_most]_函数与_[right_most]_函数计算了二叉树中最左侧的节点信息与
    最右侧的节点信息。如果树为空，则返回_[default]_。*)

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

(** 很显然，这两个函数应当满足：任意一棵二叉树的最右侧节点，就是将其左右翻转之后
    最左侧节点。这个性质可以在Coq中如下描述：*)

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
Proof. 
  intros t.
  induction t as [| l IHl v r IHr].
  - reflexivity.
  - simpl. specialize (IHl v). specialize (IHr v).
    rewrite IHr.
    reflexivity.
Qed.