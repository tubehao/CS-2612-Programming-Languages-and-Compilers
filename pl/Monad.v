Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
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

(** 我们之后最常常用到的将是集合单子（set monad）：*)

Module SetMonad.
Definition M (A: Type): Type := A -> Prop.
End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := fun (A B: Type) (f: SetMonad.M A) (g: A -> SetMonad.M B) =>
            fun b: B =>
              exists a: A, a ∈ f /\ b ∈ g a;
  ret := fun (A: Type) (a: A) => Sets.singleton a
|}.

(** 下面则是状态单子的定义：*)

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


