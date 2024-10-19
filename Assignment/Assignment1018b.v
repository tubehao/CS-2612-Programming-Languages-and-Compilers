Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.SimpleProofsAndDefs.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 我们可以使用乘法运算定义“正负号不同”这个二元谓词。请基于这一定义完成相关性质的Coq证
    明。*)

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 下面定义的谓词_[quad_nonneg a b c]_表示：以_[a]_、_[b]_、_[c]_为系数的二次式在
    自变量去一切整数的时候都恒为非负。请基于这一定义完成相关性质的Coq证明。*)

Definition quad_nonneg (a b c: Z): Prop :=
  forall x: Z, a * x * x + b * x + c >= 0.

Lemma scale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg a b c ->
  quad_nonneg (k * a) (k * b) (k * c).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma descale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg (k * a) (k * b) (k * c) ->
  quad_nonneg a b c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma plus_quad_nonneg: forall a1 b1 c1 a2 b2 c2: Z,
  quad_nonneg a1 b1 c1 ->
  quad_nonneg a2 b2 c2 ->
  quad_nonneg (a1 + a2) (b1 + b2) (c1 + c2).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 我们知道，如果二次式的二次项系数为正且判别式不为正，那么这个二次式在自变量取遍一切
    实数的时候都恒为正。相应的性质在自变量取遍一切整数的时候自然也成立。请证明这一结
    论。【选做】*)

Lemma plus_quad_discriminant: forall a b c,
  a > 0 ->
  b * b - 4 * a * c <= 0 ->
  quad_nonneg a b c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 然而，判别式不为正并不是_[quad_nonneg]_的必要条件。下面命题是一个简单的反例。*)

Example quad_nonneg_1_1_0: quad_nonneg 1 1 0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明下面命题。*)

Fact shift_up1_eq: forall f,
  shift_up1 f = func_plus f (fun x => 1).
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



