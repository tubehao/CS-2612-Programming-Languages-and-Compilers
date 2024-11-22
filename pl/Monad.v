Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import PL.FixedPoint.
Import SetsNotation.
Import KleeneFix Sets_CPO.
Local Open Scope sets.
Local Open Scope Z.

(** * 在Coq中定义单子结构 *)

(** 单子可以这样在Coq中定义为一类代数结构。*)

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Import Monad.

(** 我们之后最常常用到的将是集合单子（set monad）如下定义。*)

Module SetMonad.

Definition M (A: Type): Type := A -> Prop.

Definition bind: forall (A B: Type) (f: M A) (g: A -> M B), M B :=
  fun (A B: Type) (f: M A) (g: A -> M B) =>
    fun b: B => exists a: A, a ∈ f /\ b ∈ g a.

Definition ret: forall (A: Type) (a: A), M A :=
  fun (A: Type) (a: A) => Sets.singleton a.

End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := SetMonad.bind;
  ret := SetMonad.ret;
|}.

(** 下面是另一个例子状态单子的定义：*)

Module StateMonad.

Definition M (Σ A: Type): Type := Σ -> Σ * A.

Definition bind (Σ: Type):
  forall (A B: Type) (f: M Σ A) (g: A -> M Σ B), M Σ B :=
  fun A B f g s1 =>
    match f s1 with
    | (s2, a) => g a s2
    end.

Definition ret (Σ: Type):
  forall (A: Type) (a: A), M Σ A :=
  fun A a s => (s, a).

End StateMonad.

#[export] Instance state_monad (Σ: Type): Monad (StateMonad.M Σ) := {|
  bind := StateMonad.bind Σ;
  ret := StateMonad.ret Σ;
|}.

(** 下面是几个集合单子的例子。*)

Module SetMonadExamples0.

(** 任取一个整数：*)

Definition any_Z: SetMonad.M Z := Sets.full.

(** 整数乘二：*)

Definition multi_two: Z -> SetMonad.M Z :=
  fun x => ret (x * 2).

(** 整数加一：*)

Definition plus_one: Z -> SetMonad.M Z :=
  fun x => ret (x + 1).

(** 任取整数再乘二：*)

Definition bind_ex0: SetMonad.M Z :=
  bind any_Z multi_two.

(** 任取整数乘二再加一：*)

Definition bind_ex1: SetMonad.M Z :=
  bind (bind any_Z multi_two) plus_one.

Definition bind_ex2: SetMonad.M Z :=
  bind any_Z (fun x => bind (multi_two x) plus_one).

End SetMonadExamples0.

(** 以下是一些集合单子的性质：*)

Module SetMonadProperties.

(** 复合算子具有单调性：*)

#[export] Instance bind_mono (A B: Type):
  Proper (Sets.included ==> Sets.included ==> Sets.included)
    (@bind _ set_monad A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b [a ?]; exists a.
  specialize (Hf a); specialize (Hg a b).
  tauto.
Qed.

(** 复合算子保持集合相等：*)

#[export] Instance bind_congr (A B: Type):
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@bind _ set_monad A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b; split; intros [a ?]; exists a.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
Qed.

(** 复合算子具有对并集的分配律：*)

Lemma bind_union_distr_l:
  forall A B (f: SetMonad.M A) (g1 g2: A -> SetMonad.M B),
    bind f (g1 ∪ g2) == bind f g1 ∪ bind f g2.
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [? [? | ?]]]; [left | right]; exists a0; tauto.
  + intros [[a0 ?] | [a0 ?]]; exists a0; tauto.
Qed.

Lemma bind_union_distr_r:
  forall A B (f1 f2: SetMonad.M A) (g: A -> SetMonad.M B),
    bind (f1 ∪ f2) g == bind f1 g ∪ bind f2 g.
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [[? | ?] ?]]; [left | right]; exists a0; tauto.
  + intros [[a0 ?] | [a0 ?]]; exists a0; tauto.
Qed.

Lemma bind_indexed_union_distr_l:
  forall A B I (f: SetMonad.M A) (g: I -> A -> SetMonad.M B),
    bind f (⋃ g) == ⋃ (fun i: I => bind f (g i)).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [? [i ?]]]; exists i, a0; tauto.
  + intros [i [a0 ?]]; exists a0; split; [| exists i]; tauto.
Qed.

Lemma bind_indexed_union_distr_r:
  forall A B I (f: I -> SetMonad.M A) (g: A -> SetMonad.M B),
    bind (⋃ f) g == ⋃ (fun i: I => bind (f i) g).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [[i ?] ?]]; exists i, a0; tauto.
  + intros [i [a0 ?]]; exists a0; split; [exists i |]; tauto.
Qed.

End SetMonadProperties.

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

(** 下面是用单子描述计算时常用的记号：*)

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1 (fun _: unit => e2))
  (at level 61, right associativity) : monad_scope.

End MonadNotation.

(** 从下面例子可以看出，用单子描述的计算从语法上已经与伪代码程序十分相似了。*)

Module SetMonadExamples1.
Import MonadNotation SetMonadExamples0.
Local Open Scope monad.

Definition bind_ex0': SetMonad.M Z :=
  x <- any_Z;; ret (x * 2).

Definition bind_ex1': SetMonad.M Z :=
  x <- any_Z;; y <- multi_two x;; ret (y + 1).

End SetMonadExamples1.


(** * 带循环的计算 *)

Import MonadNotation.
Local Open Scope monad.

(** 如果要表示带循环的计算过程，那就需要引入新的循环算子。*)

Module StateMonadLoops.

Inductive BreakOrContinue (A B: Type): Type :=
| by_break (a: A)
| by_continue (b: B).

Arguments by_break {_} {_} (_).
Arguments by_continue {_} {_} (_).

Definition break {A B: Type} (a: A):
  SetMonad.M (BreakOrContinue A B) :=
  ret (by_break a).

Definition continue {A B: Type} (b: B):
  SetMonad.M (BreakOrContinue A B) :=
  ret (by_continue b).

Definition repeat_break_f
             {A B: Type}
             (body: A -> SetMonad.M (BreakOrContinue A B))
             (W: A -> SetMonad.M B)
             (a: A): SetMonad.M B :=
  x <- body a;;
  match x with
  | by_break a' => W a'
  | by_continue b => ret b
  end.

Definition repeat_break
             {A B: Type}
             (body: A -> SetMonad.M (BreakOrContinue A B)):
  A -> SetMonad.M B :=
  Kleene_LFix (repeat_break_f body).

End StateMonadLoops.


