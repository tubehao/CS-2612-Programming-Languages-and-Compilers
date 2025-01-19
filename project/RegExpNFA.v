Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope sets_scope.

(*********************************************************)
(**                                                      *)
(** Regular expression, syntax and semantics             *)
(**                                                      *)
(*********************************************************)

Inductive reg_exp (T: Type) : Type :=
  (* '' *)
  | EmptyStr_r
  (* 't' *)
  | Char_r (t : T -> Prop)
  (* '<r1><r2>' *)
  | Concat_r (r1 r2 : reg_exp T)
  (* '<r1>|<r2>' *)
  | Union_r (r1 r2 : reg_exp T)
  (* '<r>*' *)
  | Star_r (r : reg_exp T).

Arguments EmptyStr_r {T}.
Arguments Char_r {T} _.
Arguments Concat_r {T} _ _.
Arguments Union_r {T} _ _.
Arguments Star_r {T} _.

Definition set_prod {T} (A B : list T -> Prop) : list T -> Prop :=
  fun s => exists s1 s2, s1 ∈ A /\ s2 ∈ B /\ s = s2 ++ s1.

Fixpoint star_r_indexed {T} (n : nat) (s : list T -> Prop) : list T -> Prop :=
  match n with
  | 0 => [ nil ]
  | S n' => set_prod s (star_r_indexed n' s)
  end.

Fixpoint exp_match {T} (r : reg_exp T) : list T -> Prop :=
  match r with
  | EmptyStr_r => [ nil ]
  | Char_r t => fun s => exists c, c ∈ t /\ s = (cons c nil)
  | Concat_r r1 r2 => set_prod (exp_match r1) (exp_match r2)
  | Union_r r1 r2 => (exp_match r1) ∪ (exp_match r2)
  | Star_r r => ⋃ star_r_indexed (exp_match r)
  end.

(*********************************************************)
(**                                                      *)
(** Graph                                                *)
(**                                                      *)
(*********************************************************)

Definition Sets_disjoint_union {X: Type} (A B C: X -> Prop): Prop :=
  A ∩ B == ∅ /\
  A ∪ B == C.

Definition Sets_overlap {X: Type} (A B: X -> Prop): Prop :=
  exists x, x ∈ A /\ x ∈ B.

Module Graph.

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

Record add_vertex {V E} (g1: PreGraph V E) (v: V) (g2: PreGraph V E): Prop :=
{
  add_vertex_vertex:
    Sets_disjoint_union g1.(vvalid) (Sets.singleton v) g2.(vvalid);
  add_vertex_edge:
    g1.(evalid) == g2.(evalid);
  add_vertex_src:
    forall e, e ∈ g1.(evalid) -> g2.(src) e = g1.(src) e;
  add_vertex_dst:
    forall e, e ∈ g1.(evalid) -> g2.(dst) e = g1.(dst) e;
}.

Record add_edge {V E} (g1: PreGraph V E) (e0: E) (x y: V) (g2: PreGraph V E): Prop :=
{
  add_edge_vertex:
    g1.(vvalid) == g2.(vvalid);
  add_edge_edge:
    Sets_disjoint_union g1.(evalid) (Sets.singleton e0) g2.(evalid);
  add_edge_src_old:
    forall e, e ∈ g1.(evalid) -> g2.(src) e = g1.(src) e;
  add_edge_dst_old:
    forall e, e ∈ g1.(evalid) -> g2.(dst) e = g1.(dst) e;
  add_edge_src_new: g2.(src) e0 = x;
  add_edge_dst_new: g2.(dst) e0 = y;
}.

(* disjoint union *)
Record union_rel {V E} (g1 g2 g: PreGraph V E): Prop :=
{
  union_vertex: Sets_disjoint_union g1.(vvalid) g2.(vvalid) g.(vvalid);
  union_edge: Sets_disjoint_union g1.(evalid) g2.(evalid) g.(evalid);
  union_src1: forall e, e ∈ g1.(evalid) -> g.(src) e = g1.(src) e;
  union_src2: forall e, e ∈ g2.(evalid) -> g.(src) e = g2.(src) e;
  union_dst1: forall e, e ∈ g1.(evalid) -> g.(dst) e = g1.(dst) e;
  union_dst2: forall e, e ∈ g2.(evalid) -> g.(dst) e = g2.(dst) e;
}.

End Graph.

Notation "'PreGraph'" := (Graph.PreGraph) (at level 0).
Notation "pg '.(vvalid)'" := (Graph.vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (Graph.evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (Graph.src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (Graph.dst _ _ pg) (at level 1).

(*********************************************************)
(**                                                      *)
(** NFA and its semantics                                *)
(**                                                      *)
(*********************************************************)

Definition epsilon {T: Type} : option T := None.

(* We use Z as unique label for each vertex and edge. *)
(* And use `symbol` to record character on each edge based on label. *)
Record pg_nfa (T: Type) := {
  pg : PreGraph Z Z;
  symbol : Z -> option (T -> Prop)
}.

Notation "g '.(pg)'" := (pg _ g) (at level 1).
Notation "g '.(symbol)'" := (symbol _ g) (at level 1).

Record add_vertex {T} (g1: pg_nfa T) (v: Z) (g2: pg_nfa T): Prop :=
{
  add_vertex_pg:
    Graph.add_vertex g1.(pg) v g2.(pg);
  add_vertex_symbol:
    forall e, e ∈ g1.(pg).(evalid) -> g2.(symbol) e = g1.(symbol) e;
}.

Record add_edge {T} (g1: pg_nfa T) (e0 x y: Z) t (g2: pg_nfa T): Prop :=
{
  add_edge_pg:
    Graph.add_edge g1.(pg) e0 x y g2.(pg);
  add_edge_symbol_old:
    forall e, e ∈ g1.(pg).(evalid) -> g2.(symbol) e = g1.(symbol) e;
  add_edge_symbol_new:
    g2.(symbol) e0 = t;
}.

Record union_rel {T} (g1 g2 g: pg_nfa T): Prop :=
{
  union_pg: Graph.union_rel g1.(pg) g2.(pg) g.(pg);
  union_symbol1: forall e, e ∈ g1.(pg).(evalid) -> g.(symbol) e = g1.(symbol) e;
  union_symbol2: forall e, e ∈ g2.(pg).(evalid) -> g.(symbol) e = g2.(symbol) e;
}.

Definition empty_nfa {T: Type} : pg_nfa T := {|
  (* ? Pose src/dst as `fun n => -1` to indicate emptyness *)
  pg := @Graph.Build_PreGraph Z Z (fun v => False) (fun e => False) (fun n => (-1)%Z) (fun n => (-1)%Z);
  symbol := fun _ => None
|}.

Definition emptyset_nfa {T: Type} (v1 v2 : Z) : pg_nfa T := {|
  (* ? Pose src/dst as `fun n => -1` to indicate emptyness *)
  pg := @Graph.Build_PreGraph Z Z (fun v => v = v1 \/ v = v2) (fun e => False) (fun n => (-1)%Z) (fun n => (-1)%Z);
  symbol := fun _ => None
|}.

Definition e_step {T} (G: pg_nfa T) : Z -> Z -> Prop :=
  fun x y => exists e, Graph.step_aux G.(pg) e x y /\ G.(symbol) e = None.

Definition e_steps {T} (G: pg_nfa T) : Z -> Z -> Prop :=
  clos_refl_trans (e_step G).

Definition c_step {T} (G: pg_nfa T) (c: T) : Z -> Z -> Prop :=
  fun x y =>
    exists e t, Graph.step_aux G.(pg) e x y /\ G.(symbol) e = Some t /\ c ∈ t.

Definition char_step {T} (G: pg_nfa T) (c: T) : Z -> Z -> Prop :=
  (c_step G c) ∘ (e_steps G).

Fixpoint string_step {T} (G: pg_nfa T) (l: list T) : Z -> Z -> Prop :=
  match l with
  | nil => (e_steps G)
  | cons s l' => (string_step G l') ∘ (char_step G s)
  end.

Definition match_str {T} (G: pg_nfa T) (sv ev: Z) (l: list T): Prop :=
  string_step G l sv ev.

(*********************************************************)
(**                                                      *)
(** General Definition of Monad                          *)
(**                                                      *)
(*********************************************************)

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Import Monad.

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
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

Arguments bind: simpl never.
Arguments ret: simpl never.
Import MonadNotation.
Local Open Scope monad.

(*********************************************************)
(**                                                      *)
(** State Rel Monad                                      *)
(**                                                      *)
(*********************************************************)

Module StateRelMonad.

Record M (Σ A: Type): Type :=
{
  nrm: Σ -> A -> Σ -> Prop;
  err: Σ -> Prop;
}.

Arguments nrm {_} {_} _.
Arguments err {_} {_} _.

Definition bind (Σ A B: Type) (f: M Σ A) (g: A -> M Σ B): M Σ B :=
{|
  nrm := fun (s1: Σ) (b: B) (s3: Σ) =>
            exists (a: A) (s2: Σ),
              (s1, a, s2) ∈ f.(nrm) /\ (s2, b, s3) ∈ (g a).(nrm);
  err := fun s1: Σ =>
            s1 ∈ f.(err) \/
            exists (a: A) (s2: Σ), (s1, a, s2) ∈ f.(nrm) /\ s2 ∈ (g a).(err);
|}.

Definition ret (Σ A: Type) (a0: A): M Σ A :=
{|
  nrm := fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2;
  err := fun (s1: Σ) => False;
|}.

End StateRelMonad.

Notation "x '.(nrm)'" := (StateRelMonad.nrm x) (at level 1).
Notation "x '.(err)'" := (StateRelMonad.err x) (at level 1).

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.

Definition Hoare {Σ A: Type}
                 (P: Σ -> Prop)
                 (c: StateRelMonad.M Σ A)
                 (Q: A -> Σ -> Prop): Prop :=
  (forall s1, P s1 -> ~ s1 ∈ c.(err)) /\
  (forall s1 a s2, P s1 -> (s1, a, s2) ∈ c.(nrm) -> Q a s2).

(*********************************************************)
(**                                                      *)
(** Generating NFA                                       *)
(**                                                      *)
(*********************************************************)

Local Open Scope Z.

Record state := {
  max_v : Z;
  max_e : Z
}.

Record elem (T: Type) := {
  startVertex : Z;
  endVertex : Z;
  graph : pg_nfa T;
}.

Notation "g '.(graph)'" := (graph _ g) (at level 1).
Notation "g '.(startVertex)'" := (startVertex _ g) (at level 1).
Notation "g '.(endVertex)'" := (endVertex _ g) (at level 1).

Definition get_new_vertex: StateRelMonad.M state Z := {|
  StateRelMonad.nrm := fun s1 n s2 =>
    s2.(max_v) = s1.(max_v) + 1 /\
    s2.(max_e) = s1.(max_e) /\
    n = s2.(max_v);
  StateRelMonad.err := fun s1 => False
|}.

Definition G_add_vertex {T} (g: pg_nfa T) (n: Z):
  StateRelMonad.M state (pg_nfa T) :=
{|
  StateRelMonad.nrm := fun s1 g0 s2 => add_vertex g n g0 /\ s1 = s2;
  StateRelMonad.err := fun _ => n ∈ g.(pg).(vvalid);
|}.

Definition get_new_edge : StateRelMonad.M state Z := {|
  StateRelMonad.nrm :=
    fun s1 n s2 =>
    s2.(max_v) = s1.(max_v) /\
    s2.(max_e) = s1.(max_e) + 1 /\
    n = s2.(max_e);
  StateRelMonad.err := fun s1 => False (* no error case *)
|}.

Definition G_add_edge {T} (g: pg_nfa T) (e x y: Z) t: StateRelMonad.M state (pg_nfa T) := {|
  StateRelMonad.nrm :=
    fun s1 g0 s2 =>
      add_edge g e x y t g0 /\ s1 = s2;
  StateRelMonad.err :=
    fun _ => e ∈ g.(pg).(evalid);
|}.

Definition G_add_graph {T} (g1 g2: pg_nfa T): StateRelMonad.M state (pg_nfa T) := {|
  StateRelMonad.nrm :=
    fun s1 g3 s2 =>
      union_rel g1 g2 g3 /\ s1 = s2;
  StateRelMonad.err :=
    fun s1 => Sets_overlap g1.(pg).(vvalid) g2.(pg).(vvalid) \/
              Sets_overlap g1.(pg).(evalid) g2.(pg).(evalid);
|}.

Inductive graph_construction_component {T} :=
  | G (g: pg_nfa T)
  | V (v: Z)
  | E (v1 v2: Z) (sbl: option (T -> Prop)).

Fixpoint graph_constr_rec {T} (g0: pg_nfa T) (l: list graph_construction_component): StateRelMonad.M state (pg_nfa T) :=
  match l with
  | nil => ret g0
  | G g :: l0 => g1 <- G_add_graph g0 g;; graph_constr_rec g1 l0
  | V v :: l0 => g1 <- G_add_vertex g0 v;; graph_constr_rec g1 l0
  | E x y t :: l0 => e <- get_new_edge;;
                     g1 <- G_add_edge g0 e x y t;;
                     graph_constr_rec g1 l0
  end.

Definition graph_constr {T} (l: list graph_construction_component):
  StateRelMonad.M state (pg_nfa T) :=
  graph_constr_rec empty_nfa l.

Definition ret_nfa {T: Type} (x y: Z) (g: pg_nfa T):
  StateRelMonad.M state (elem T) :=
  ret (Build_elem _ x y g).

(** Regex operator definition (concat/union/star/...) *)

Definition act_empty {T}: StateRelMonad.M state (elem T) :=
  v1 <- get_new_vertex ;;
  v2 <- get_new_vertex ;;
  g1 <- graph_constr [V v1; V v2] ;;
  ret_nfa v1 v2 g1.

(* match single char c *)
Definition act_singleton {T} (t: option (T -> Prop)):
  StateRelMonad.M state (elem T) :=
  v1 <- get_new_vertex ;;
  v2 <- get_new_vertex ;;
  g1 <- graph_constr [V v1; V v2; E v1 v2 t] ;;
  ret_nfa v1 v2 g1.

(* match A|B *)
Definition act_union {T} (A B: elem T) : StateRelMonad.M state (elem T) :=
  v1 <- get_new_vertex ;;
  v2 <- get_new_vertex ;;
  g <- graph_constr  [G A.(graph);
                      G B.(graph);
                      V v1;
                      V v2;
                      E v1 A.(startVertex) epsilon;
                      E v1 B.(startVertex) epsilon;
                      E A.(endVertex) v2 epsilon;
                      E B.(endVertex) v2 epsilon] ;;
  ret_nfa v1 v2 g.

(* match AB *)
Definition act_concat {T} (A B: elem T) : StateRelMonad.M state (elem T) :=
  g <- graph_constr [G A.(graph);
                     G B.(graph);
                     E A.(endVertex) B.(startVertex) epsilon] ;;
  ret_nfa A.(startVertex) B.(endVertex) g.
  
(* match A* *)
Definition act_star {T} (A: elem T) : StateRelMonad.M state (elem T) :=
  v1 <- get_new_vertex ;;
  v2 <- get_new_vertex ;;
  g1 <- graph_constr [G A.(graph);
                      V v1; V v2;
                      E v1 A.(endVertex) epsilon;
                      E A.(endVertex) v2 epsilon;
                      E A.(endVertex) A.(startVertex) epsilon] ;;
  ret_nfa v1 v2 g1.

(* Regex AST <-> NFA Monad *)

Fixpoint regexToNFA {T} (r : reg_exp T) : StateRelMonad.M state (elem T) :=
  match r with
  | EmptyStr_r => act_singleton None

  | Char_r t => act_singleton (Some t)

  | Concat_r r1 r2 =>
    E1 <- regexToNFA r1 ;;
    E2 <- regexToNFA r2 ;;
    act_concat E1 E2

  | Union_r r1 r2 =>
    E1 <- regexToNFA r1 ;;
    E2 <- regexToNFA r2 ;;
    act_union E1 E2

  | Star_r r =>
    E <- regexToNFA r ;;
    act_star E
  end.


(*********************************************************)
(**                                                      *)
(** derive_false                                         *)
(**                                                      *)
(*********************************************************)

(* 添加新顶点或边后图的顶点和边编号相关的属性。 *)
Lemma get_new_vertex_num :
  forall (s1 s2: state) (x: Z),
    (s1, x, s2) ∈ get_new_vertex.(nrm) ->
    max_v s2 = max_v s1 + 1 /\ max_e s2 = max_e s1 /\ x = max_v s2.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  tauto.
Qed.

(* 添加新顶点或边后图的顶点和边编号相关的属性。 *)
Lemma get_new_edge_num :
  forall (s1 s2: state) (x: Z),
    (s1, x, s2) ∈ get_new_edge.(nrm) ->
    max_v s2 = max_v s1 /\ max_e s2 = max_e s1 + 1 /\ x = max_e s2.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  tauto.
Qed.

(* 如果x是x1和x2通过G_add_graph得到的新图，那么点或边在x1或x2中与在x中可以互推 *)
Lemma add_graph_num :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
    (forall a : Z,
    (x1.(pg)).(vvalid) a \/ (x2.(pg)).(vvalid) a <->
    (x.(pg)).(vvalid) a) /\
    (forall a : Z,
    (x1.(pg)).(evalid) a \/ (x2.(pg)).(evalid) a <->
    (x.(pg)).(evalid) a).
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  destruct H.
  destruct union_pg0.
  unfold Sets_disjoint_union in union_vertex, union_edge.
  sets_unfold in union_vertex.
  sets_unfold in union_edge.
  destruct union_vertex.
  destruct union_edge.
  tauto.
Qed.

(* add_graph_num的点形式 *)
Lemma add_graph_num_vertex1 :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
    (forall a : Z,
    (x1.(pg)).(vvalid) a \/ (x2.(pg)).(vvalid) a ->
    (x.(pg)).(vvalid) a).
Proof.
  intros.
  pose proof add_graph_num s1 s2 x x1 x2 H.
  destruct H1.
  pose proof H1 a.
  destruct H3.
  pose proof H3 H0.
  tauto.
Qed.

Lemma add_graph_num_vertex2 :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
    (forall a : Z,
    (x.(pg)).(vvalid) a ->
    (x1.(pg)).(vvalid) a \/ (x2.(pg)).(vvalid) a).
Proof.
  intros.
  pose proof add_graph_num s1 s2 x x1 x2 H.
  destruct H1.
  pose proof H1 a.
  destruct H3.
  pose proof H4 H0.
  tauto.
Qed.

(* add_graph_num的边形式 *)
Lemma add_graph_num_edge1 :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
    (forall a : Z,
    (x1.(pg)).(evalid) a \/ (x2.(pg)).(evalid) a ->
    (x.(pg)).(evalid) a).
Proof.
  intros.
  pose proof add_graph_num s1 s2 x x1 x2 H.
  destruct H1.
  pose proof H2 a.
  destruct H3.
  pose proof H3 H0.
  tauto.
Qed.

Lemma add_graph_num_edge2 :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
    (forall a : Z,
    (x.(pg)).(evalid) a ->
    (x1.(pg)).(evalid) a \/ (x2.(pg)).(evalid) a).
Proof.
  intros.
  pose proof add_graph_num s1 s2 x x1 x2 H.
  destruct H1.
  pose proof H2 a.
  destruct H3.
  pose proof H4 H0.
  tauto.
Qed.

(* 经过G_add_vertex后，程序状态不变。add_vertex_maxv_equal和add_vertex_maxe_equal分别讨论s中的max_v和max_e *)
Lemma add_vertex_state_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v: Z),
    (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
      s1 = s2.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  tauto.
Qed.

(* add_vertex_state_equal的点形式 *)
Lemma add_vertex_maxv_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v: Z),
    (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
      max_v s1 = max_v s2.
Proof.
  intros.
  pose proof add_vertex_state_equal s1 s2 x x1 v H.
  rewrite H0.
  tauto.
Qed.

(* add_vertex_state_equal的边形式 *)
Lemma add_vertex_maxe_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v: Z),
    (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
      max_e s1 = max_e s2.
Proof.
  intros.
  pose proof add_vertex_state_equal s1 s2 x x1 v H.
  rewrite H0.
  tauto.
Qed.

(* 经过G_add_edge后，程序状态不变。add_edge_maxv_equal和add_edge_maxe_equal分别讨论s中的max_v和max_e *)
Lemma add_edge_state_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2: Z) t,
    (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 t).(nrm) ->
      s1 = s2.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  tauto.
Qed.

(* add_edge_state_equal的点形式 *)
Lemma add_edge_maxv_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2: Z) t,
    (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 t).(nrm) ->
      max_v s1 = max_v s2.
Proof.
  intros.
  pose proof add_edge_state_equal s1 s2 x x1 e v1 v2 t H.
  rewrite H0.
  tauto.
Qed.

(* add_edge_state_equal的边形式 *)
Lemma add_edge_maxe_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2: Z) t,
    (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 t).(nrm) ->
      max_e s1 = max_e s2.
Proof.
  intros.
  pose proof add_edge_state_equal s1 s2 x x1 e v1 v2 t H.
  rewrite H0.
  tauto.
Qed.

(* 经过G_add_graph后，程序状态不变。add_graph_maxv_equal和add_graph_maxe_equal分别讨论s中的max_v和max_e *)
Lemma add_graph_state_equal :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
      s1 = s2.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  tauto.
Qed.

(* add_graph_state_equal的点形式 *)
Lemma add_graph_maxv_equal :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
      max_v s1 = max_v s2.
Proof.
  intros.
  pose proof add_graph_state_equal s1 s2 x x1 x2 H.
  rewrite H0.
  tauto.
Qed.

(* add_graph_state_equal的边形式 *)
Lemma add_graph_maxe_equal :
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T),
    (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
      max_e s1 = max_e s2.
Proof.
  intros.
  pose proof add_graph_state_equal s1 s2 x x1 x2 H.
  rewrite H0.
  tauto.
Qed.

(* 对图进行G_add_vertex操作不会改变图中的边 *)
Lemma add_vertex_edge_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v: Z),
    (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
    (forall a : Z,
    (x1.(pg)).(evalid) a <-> (x.(pg)).(evalid) a).
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  destruct H.
  destruct add_vertex_pg0.
  sets_unfold in add_vertex_edge.
  pose proof add_vertex_edge a.
  tauto.
Qed.

(* 对图进行G_add_edge操作不会改变图中的点 *)
Lemma add_edge_in_graph :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2: Z) t,
    (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 t).(nrm) ->
    (forall a : Z, (x1.(pg)).(vvalid) a <-> (x.(pg)).(vvalid) a).
Proof.
  intros.
  destruct H.
  destruct H.
  destruct add_edge_pg0.
  sets_unfold in add_edge_vertex.
  pose proof add_edge_vertex a.
  apply H.
Qed.

(* 对图进行G_add_edge操作，新图中的边要么是原图中的边，要么是新加的边 *)
Lemma add_edge_edge_equal :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2: Z) t,
    (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 t).(nrm) ->
    (forall a : Z, (x1.(pg)).(evalid) a \/ e = a <-> (x.(pg)).(evalid) a).
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  destruct H.
  destruct add_edge_pg0.
  unfold Sets_disjoint_union in add_edge_edge.
  sets_unfold in add_edge_edge.
  destruct add_edge_edge.
  pose proof H1 a.
  tauto.
Qed.

(* 对图进行G_add_vertex操作，新图中的点要么是原图中的点，要么是新加的点 *)
Lemma add_vertex_in_graph :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v: Z),
    (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
    (forall a : Z, (x1.(pg)).(vvalid) a \/ v = a <-> (x.(pg)).(vvalid) a).
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  destruct H.
  destruct add_vertex_pg0.
  unfold Sets_disjoint_union in add_vertex_vertex.
  sets_unfold in add_vertex_vertex.
  destruct add_vertex_vertex.
  pose proof H1 a.
  tauto.
Qed.

(* 加边或加点后前后图边关系 *)
Lemma after_G_add_edge:
  forall {T: Type} (g1 g2: pg_nfa T) (s1 s2: state) (e x y: Z) (t: option (T -> Prop)),
    (s1, g2, s2) ∈ (G_add_edge g1 e x y t).(nrm) -> s1 = s2 /\
    (forall gv, gv ∈ g2.(pg).(vvalid) <-> gv ∈ g1.(pg).(vvalid)) /\
    (forall ge, ge ∈ g2.(pg).(evalid) <-> (ge = e \/ ge ∈ g1.(pg).(evalid))).
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  split.
  tauto.
  split.
  + intros.
    (* 证明点一样 *)
    destruct H.
    destruct add_edge_pg0.
    sets_unfold in add_edge_vertex.
    pose proof add_edge_vertex gv.
    tauto.
  + intros.
    (* 证明边在原图基础上加了一个 *)
    destruct H.
    destruct add_edge_pg0.
    sets_unfold in add_edge_edge.
    unfold Sets_disjoint_union in add_edge_edge.
    sets_unfold in add_edge_edge.
    destruct add_edge_edge.
    pose proof H1 ge.
    destruct H2.
    split.
    - intros.
      apply H3 in H4.
      destruct H4.
      right; tauto.
      left; rewrite H4; reflexivity.
    - intros.
      destruct H4.
      * apply H2.
        rewrite H4.
        right; tauto.
      * assert (H_or :  g1.(pg).(evalid) ge \/ e = ge). {
          left; tauto.
        }
        apply H2 in H_or.
        tauto.
Qed.

(* 加边或加点后前后图点关系 *)
Lemma after_G_add_vertex:
  forall {T: Type} (g1 g2: pg_nfa T) (s1 s2: state) (v: Z),
    (s1, g2, s2) ∈ (G_add_vertex g1 v).(nrm) -> s1 = s2 /\
    (forall gv, gv ∈ g2.(pg).(vvalid) <-> (gv = v \/ gv ∈ g1.(pg).(vvalid))) /\
    (forall ge, ge ∈ g2.(pg).(evalid) <-> ge ∈ g1.(pg).(evalid)).
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  destruct H.
  split.
  tauto.
  split.
  2: {
    intros.
    (* 证明边一样 *)
    destruct H.
    destruct add_vertex_pg0.
    sets_unfold in add_vertex_edge.
    pose proof add_vertex_edge ge.
    tauto.
  }
  + intros.
  (* 证明点在原图基础上加了一个 *)
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct add_vertex_pg0.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex.
    pose proof H1 gv.
    (* 为什么不能 tauto *)
    (* 下面尝试拆开来证，好像coq看不懂这俩是一样的：
        (g1.(pg)).(vvalid) gv 和 gv ∈ (g2.(pg)).(vvalid) 
    *)
    destruct H2.
    split.
    - intros.
      apply H3 in H4.
      destruct H4.
      right; tauto.
      left; rewrite H4; reflexivity.
    - intros.
      destruct H4.
      * assert (H_or :  g1.(pg).(vvalid) gv \/ v = gv) by lia.
        apply H2 in H_or.
        tauto.
      * assert (H_or :  g1.(pg).(vvalid) gv \/ v = gv). {
          left.
          tauto.
        }
        apply H2 in H_or.
        tauto.
Qed.

(* 获得新的点后程序状态的变化 *)
Lemma after_get_new_vertex:
  forall (s1 s2: state) (v: Z),
    (s1, v, s2) ∈ get_new_vertex.(nrm) ->
    (s1.(max_v) < v <= s2.(max_v) /\ s2.(max_v) = s1.(max_v) + 1) /\
    s1.(max_e) = s2.(max_e).
Proof.
  intros.
  unfold get_new_vertex in H.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H0.
  split.
  split.
  split.
  - rewrite H1.
    lia.
  - rewrite H1.
    lia.
  - lia.
  - lia.
Qed.

(* 获得新的点后程序状态的变化：get_new_edge 之后 e 的值在 s1 s2 之间左开右闭 *)
Lemma after_get_new_edge:
  forall (s1 s2: state) (e: Z),
    (s1, e, s2) ∈ get_new_edge.(nrm) ->
    (s1.(max_e) < e <= s2.(max_e) /\ s2.(max_e) = s1.(max_e) + 1) /\
    s1.(max_v) = s2.(max_v).
Proof.
  intros.
  unfold get_new_edge in H.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H0.
  split.
  split.
  split.
  - rewrite H1.
    lia.
  - rewrite H1.
    lia.
  - lia.
  - lia.
Qed.

(* 经过graph_constr获得的nfa的点都在前后state的max_v中。 *)
Lemma v_range_graph_constr_singleton:
  forall {T: Type} (t: option (T -> Prop)) (s1 s2 s3 s4: state) (v1 v2: Z) (g: pg_nfa T),
    s1.(max_v) < v1 <= s2.(max_v) ->
    s2.(max_v) < v2 <= s3.(max_v) ->
    (s3, g, s4) ∈ (graph_constr [V v1; V v2; E v1 v2 t]).(nrm) ->
    (* s1.(max_v) <= s4.(max_v) /\ *)
    forall gv, gv ∈ g.(pg).(vvalid) -> s1.(max_v) < gv <= s4.(max_v).
Proof.
  intros.
  unfold graph_constr in H1.
  unfold StateRelMonad.nrm in H1.
  destruct H1.
  destruct H1.
  destruct H1.
  unfold StateRelMonad.nrm in H3.
  destruct H3.
  destruct H3.
  destruct H3.
  unfold StateRelMonad.nrm in H4.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  induction H6.
  rewrite H6 in H2.
  rewrite <- H7.
  clear H6 H7.
  pose proof after_G_add_edge x1 x5 x4 x6 x3 v1 v2 t H5.
  destruct H6.
  destruct H7.
  clear H8.
  specialize (H7 gv).
  rewrite H7 in H2.
  clear H7.
  rewrite <- H6.
  clear H6.
  pose proof after_get_new_edge x2 x4 x3 H4.
  destruct H6.
  rewrite <- H7.
  clear H7 H6.
  pose proof after_G_add_vertex x x1 x0 x2 v2 H3.
  destruct H6.
  destruct H7.
  clear H8.
  specialize (H7 gv).
  apply H7 in H2.
  rewrite <- H6.
  pose proof after_G_add_vertex empty_nfa x s3 x0 v1 H1.
  destruct H8.
  destruct H9.
  clear H10.
  specialize (H9 gv).
  destruct H2.
  * rewrite <- H8.
    assert (H_max : max_v s1 < v2). {
      lia.
    }
    rewrite H2.
    tauto.
  * rewrite H9 in H2.
    destruct H2.
    ** assert (H_max : v1 <= max_v s3). {
        lia.
       }
       rewrite H2.
       rewrite <- H8.
       tauto.
    ** tauto.
Qed.

(* 经过graph_constr获得的nfa的边都在前后state的max_e中。 *)
Lemma e_range_graph_constr_singleton:
  forall {T: Type} (t: option (T -> Prop)) (s1 s2 s3 s4: state) (v1 v2: Z) (g: pg_nfa T),
    s1.(max_e) = s2.(max_e) ->
    s2.(max_e) = s3.(max_e) ->
    (s3, g, s4) ∈ (graph_constr [V v1; V v2; E v1 v2 t]).(nrm) ->
    forall ge, ge ∈ g.(pg).(evalid) -> s1.(max_e) < ge <= s4.(max_e).
Proof.
  intros.
  unfold graph_constr in H1.
  unfold StateRelMonad.nrm in H1.
  destruct H1.
  destruct H1.
  destruct H1.
  unfold StateRelMonad.nrm in H3.
  destruct H3.
  destruct H3.
  destruct H3.
  unfold StateRelMonad.nrm in H4.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  induction H6.
  rewrite H6 in H2.
  rewrite <- H7.
  clear H6 H7.
  pose proof after_G_add_edge x1 x5 x4 x6 x3 v1 v2 t H5.
  destruct H6.
  destruct H7.
  clear H7.
  rewrite <- H6.
  specialize (H8 ge).
  rewrite H8 in H2.
  clear H8 H6 H5.
  destruct H2.
  * pose proof after_get_new_edge x2 x4 x3 H4.
    destruct H5.
    clear H6.
    pose proof after_G_add_vertex x x1 x0 x2 v2 H3.
    destruct H6.
    destruct H5.
    rewrite <- H6 in H5.
    pose proof after_G_add_vertex empty_nfa x s3 x0 v1 H1.
    destruct H9.
    rewrite <- H9 in H5.
    assert (H_max : max_e s1 = max_e s3). {
      lia.
    }
    rewrite H_max.
    rewrite H2.
    tauto.
  * pose proof after_get_new_edge x2 x4 x3 H4.
    destruct H5.
    destruct H5.
    clear H6.
    pose proof after_G_add_vertex x x1 x0 x2 v2 H3.
    destruct H6.
    destruct H8.
    clear H8.
    specialize (H9 ge).
    rewrite H9 in H2.
    clear H9.
    rewrite H7.
    clear H5 H7.
    rewrite <- H6.
    pose proof after_G_add_vertex empty_nfa x s3 x0 v1 H1.
    destruct H5.
    destruct H7.
    clear H7.
    specialize (H8 ge).
    rewrite H8 in H2.
    clear H8.
    rewrite <- H5.
    clear H5.
    clear H3 H4 H6.
    tauto.
Qed.
      
(* 
现在已经有的点边关系（可以 pose proof 的）有如下：
after_G_add_edge: (g1 g2: pg_nfa T) (s1 s2: state) (e x y: Z) (t: option (T -> Prop))
after_G_add_vertex: (g1 g2: pg_nfa T) (s1 s2: state) (v: Z)
after_get_new_vertex: (s1 s2: state) (v: Z)
after_get_new_edge: (s1 s2: state) (e: Z)
和 act_xxx 相关的点边定理
Lemma v_range_graph_constr_singleton:
  forall {T: Type} (t: option (T -> Prop)) (s1 s2 s3 s4: state) (v1 v2: Z) (g: pg_nfa T),
    s1.(max_v) < v1 <= s2.(max_v) ->
    s2.(max_v) < v2 <= s3.(max_v) ->
    (s3, g, s4) ∈ (graph_constr [V v1; V v2; E v1 v2 t]).(nrm) ->
    forall gv, gv ∈ g.(pg).(vvalid) -> s1.(max_v) < gv <= s4.(max_v).
*)
Lemma another_order_vvalid_range :
	forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
	(s1, elem1, s2) ∈ (regexToNFA r).(nrm) -> s1.(max_v) <= s2.(max_v) /\
	forall gv, gv ∈ elem1.(graph).(pg).(vvalid) -> s1.(max_v) < gv <= s2.(max_v).
Proof.
  intros T elem1 s1 s2 r H.
  (* 2: { *)
    revert s2 H.
    revert elem1.
    revert s1.
    induction r.
    + intros.
      unfold regexToNFA in H.
      unfold act_singleton in H.
      unfold StateRelMonad.nrm in H.
      destruct H.
      destruct H.
      destruct H.
      unfold StateRelMonad.nrm in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      unfold StateRelMonad.nrm in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      pose proof after_get_new_vertex s1 x0 x H.
      destruct H3.
      destruct H3.
      pose proof after_get_new_vertex x0 x2 x1 H0.
      destruct H6.
      destruct H6.
      pose proof v_range_graph_constr_singleton None s1 x0 x2 x4 x x1 x3 as v_range_singleton.
      pose proof v_range_singleton H3 H6 H1 as temp.
      unfold ret_nfa in H3.
      destruct H2.
      assert (after_ret_nfa: elem1.(graph)=x3). {
        rewrite H2.
        reflexivity.
      }
      split.
      2: {
        intros.
        pose proof temp gv.
        rewrite <- after_ret_nfa in H11.
        apply H11 in H10.
        rewrite <- H9.
        tauto.
      }
      * (* 要证明 (x2, x3, x4) ∈ (graph_constr... 的情况下 x2=x4 *)
        clear H H0 H3 H4 H6 H7 v_range_singleton temp after_ret_nfa.
        unfold StateRelMonad.nrm in H1.
        destruct H1.
        destruct H.
        destruct H.
        unfold StateRelMonad.nrm in H0.
        destruct H0.
        destruct H0.
        destruct H0.
        unfold StateRelMonad.nrm in H1.
        destruct H1.
        destruct H1.
        destruct H1.
        unfold StateRelMonad.nrm in H3.
        destruct H3.
        destruct H3.
        destruct H3.
        unfold StateRelMonad.nrm in H4.
        destruct H4.
        pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H as [state_equeal1 _].
        pose proof after_G_add_vertex x5 x7 x6 x8 x1 H0 as [state_equeal2 _].
        pose proof after_get_new_edge x8 x10 x9 H1 as [_ state_relation3].
        pose proof after_G_add_edge x7 x11 x10 x12 x9 x x1 None H3 as [state_equeal3 _].
        (* 链条已经都有了 下面只是整数比大小来回倒 *)
        rewrite <- H9.
        rewrite <- H6.
        rewrite <- state_equeal3.
        rewrite <- state_relation3.
        rewrite <- state_equeal2; rewrite <- state_equeal1.
        rewrite H8.
        rewrite H5.
        lia.
    + intros.
      unfold regexToNFA in H.
      unfold act_singleton in H.
      unfold StateRelMonad.nrm in H.
      destruct H.
      destruct H.
      destruct H.
      unfold StateRelMonad.nrm in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      unfold StateRelMonad.nrm in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      pose proof after_get_new_vertex s1 x0 x H.
      destruct H3.
      destruct H3.
      pose proof after_get_new_vertex x0 x2 x1 H0.
      destruct H6.
      destruct H6.
      pose proof v_range_graph_constr_singleton (Some t) s1 x0 x2 x4 x x1 x3 as v_range_singleton.
      split.
      2: {
        intros.
        pose proof v_range_singleton H3 H6.
        pose proof H10 H1 gv.
        unfold ret_nfa in H2.
        destruct H2.
        assert (after_ret_nfa: elem1.(graph)=x3). {
          rewrite H2.
          reflexivity.
        }
        rewrite <- after_ret_nfa in H11.
        pose proof H11 H9.
        rewrite <- H12.
        tauto.
      }
      clear H3 H4 H6 H7 v_range_singleton.
      unfold graph_constr in H1.
      unfold StateRelMonad.nrm in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      unfold StateRelMonad.nrm in H3.
      destruct H3.
      destruct H3.
      destruct H3.
      unfold StateRelMonad.nrm in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold StateRelMonad.nrm in H7.
      destruct H7.
      (* 开始展开所有 state 的关系 *)
      pose proof after_get_new_vertex s1 x0 x H as [_ state_relation1].
      pose proof after_get_new_vertex x0 x2 x1 H0 as [_ state_relation2].
      pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H1 as [state_equeal3 _].
      pose proof after_G_add_vertex x5 x7 x6 x8 x1 H3 as [state_equeal4 _].
      pose proof after_get_new_edge x8 x10 x9 H4 as [_ state_relation5].
      pose proof after_G_add_edge x7 x11 x10 x12 x9 x x1 (Some t) H6 as [state_equeal5 _].
      unfold ret_nfa in H2.
      destruct H2 as [_ state_relation6].
      rewrite <- state_relation6.
      rewrite <- H9.
      rewrite <- state_equeal5.
      rewrite <- state_relation5.
      rewrite <- state_equeal4; rewrite <- state_equeal3.
      rewrite H8.
      rewrite H5.
      lia.
    + intros.
      unfold StateRelMonad.nrm in H.
      destruct H.
      destruct H.
      destruct H.
      unfold StateRelMonad.nrm in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      unfold StateRelMonad.nrm in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H1.
      unfold StateRelMonad.nrm in H3.
      destruct H3.
      destruct H3.
      destruct H3.
      unfold StateRelMonad.nrm in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold StateRelMonad.nrm in H5.
      destruct H5.
      destruct H5.
      destruct H5.
      pose proof IHr1 s1 x x0 H as [state_relation1 belong_g1].
      pose proof IHr2 x0 x1 x2 H0 as [state_relation2 belong_g2].
      split.
      2: {
        intros.
        unfold ret_nfa in H2.
        destruct H2 as [? state_equal3].
        unfold G_add_graph in H1.
        unfold StateRelMonad.nrm in H1.
        destruct H1 as [? state_equal4].
        unfold G_add_graph in H3.
        unfold StateRelMonad.nrm in H3.
        destruct H3 as [? state_equal5].
        pose proof after_get_new_edge x8 x10 x9 H4 as [? state_relation6].
        unfold StateRelMonad.nrm in H6.
        destruct H6.
        pose proof after_G_add_edge x7 x11 x10 x12 x9 x.(endVertex) x1.(startVertex) None H5 as [state_equal6 [? ?]].
        pose proof H10 gv.
        assert (after_ret_nfa: elem1.(graph)=x3). {
          rewrite H2.
          reflexivity.
        }
        rewrite <- after_ret_nfa in H6.
        rewrite <- H6 in H12.
        destruct H12 as [forward backward].
        pose proof forward H7.
        clear H10 H11 forward backward.
        (* 至此证明了 gv ∈ x7 也就是 union_rel x5 x1.(graph)
        后者 x1.(graph) 就是我们想要的
        前者又由 union_rel empty_nfa x.(graph) x5 得来，x.(graph) 也是我们想要的
        *)
        destruct H3.
        destruct union_pg0.
        unfold Sets_disjoint_union in union_vertex.
        sets_unfold in union_vertex.
        destruct union_vertex.
        pose proof H10 gv.
        destruct H11 as [sub_to_one one_to_sub].
        pose proof one_to_sub H12.
        (* 至此推出在两个图里之一 *)
        destruct H11.
        - (* 在 x5 中，再由 union_rel empty_nfa x.(graph) x5 可以推到 x 上 *)
          clear IHr1 IHr2 union_symbol3 union_symbol4 union_edge union_src1 union_src2 union_dst1 union_dst2 sub_to_one one_to_sub.
          destruct H1.
          destruct union_pg0.
          clear union_edge union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4.
          unfold Sets_disjoint_union in union_vertex.
          sets_unfold in union_vertex.
          destruct union_vertex.
          pose proof H13 gv.
          simpl in H14.
          destruct H14.
          pose proof H15 H11.
          destruct H16.
          contradiction.
          pose proof belong_g1 gv H16.
          rewrite <- state_equal3.
          rewrite <- H9.
          rewrite <- state_equal6.
          rewrite <- state_relation6.
          rewrite <- state_equal5.
          rewrite <- state_equal4.
          split.
          ++ tauto.
          ++ apply Z.le_trans with (m := x0.(max_v)).
            tauto.
            apply state_relation2.
        - (* 然后证明 gv 在 x1 中的情况 *)
          clear IHr1 IHr2 union_symbol3 union_symbol4 union_edge union_src1 union_src2 union_dst1 union_dst2 sub_to_one one_to_sub.
          pose proof belong_g2 gv H11.
          rewrite <- state_equal3.
          rewrite <- H9.
          rewrite <- state_equal6.
          rewrite <- state_relation6.
          rewrite <- state_equal5.
          rewrite <- state_equal4.
          split.
          2: {
            tauto.
          }
          apply Z.le_lt_trans with (m := x0.(max_v)).
          tauto.
          tauto.
      }
      (* 只要证明在外侧的 state 关系, 就要用 after_xxx 来展开 *)
      clear IHr1 IHr2.
      unfold StateRelMonad.nrm in H1.
      destruct H1 as [_ state_equal3].
      unfold StateRelMonad.nrm in H3.
      destruct H3 as [_ state_equal4].
      pose proof after_get_new_edge x8 x10 x9 H4 as [_ state_relation5].
      unfold StateRelMonad.nrm in H5.
      destruct H5 as [_ state_equal6].
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      unfold StateRelMonad.nrm in H2.
      destruct H2.
      rewrite <- H5.
      rewrite <- H3.
      rewrite <- state_equal6.
      rewrite <- state_relation5.
      rewrite <- state_equal4.
      rewrite <- state_equal3.
      apply Z.le_trans with (m := x0.(max_v)).
      tauto.
      tauto.
    + intros.
      unfold StateRelMonad.nrm in H.
      destruct H.
      destruct H.
      destruct H.
      unfold StateRelMonad.nrm in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      unfold StateRelMonad.nrm in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H2.
      destruct H2.
      unfold StateRelMonad.nrm in H3.
      destruct H3.
      destruct H3.
      destruct H3.
      unfold StateRelMonad.nrm in H3.
      destruct H3.
      destruct H3.
      destruct H3.
      unfold StateRelMonad.nrm in H5.
      destruct H5.
      destruct H5.
      destruct H5.
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold StateRelMonad.nrm in H7.
      destruct H7.
      destruct H7.
      destruct H7.
      unfold StateRelMonad.nrm in H8.
      destruct H8.
      destruct H8.
      destruct H8.
      unfold StateRelMonad.nrm in H9.
      destruct H9.
      destruct H9.
      destruct H9.
      unfold StateRelMonad.nrm in H10.
      destruct H10.
      destruct H10.
      destruct H10.
      unfold StateRelMonad.nrm in H11.
      destruct H11.
      destruct H11.
      destruct H11.
      unfold StateRelMonad.nrm in H12.
      destruct H12.
      destruct H12.
      destruct H12.
      unfold StateRelMonad.nrm in H13.
      destruct H13.
      destruct H13.
      destruct H13.
      unfold StateRelMonad.nrm in H14.
      destruct H14.
      destruct H14.
      destruct H14.
      unfold StateRelMonad.nrm in H15.
      destruct H15.
      destruct H15.
      destruct H15.
      pose proof IHr1 s1 x x0 H as [state_relation1 belong_g1].
      pose proof IHr2 x0 x1 x2 H0 as [state_relation2 belong_g2].
      split.
      -- (* 先证明外侧的状态相等 *)
        clear IHr1 IHr2 belong_g1 belong_g2 H H0.
        pose proof after_get_new_vertex x2 x4 x3 H1 as [[_ state_relation3] _].
        pose proof after_get_new_vertex x4 x6 x5 H2 as [[_ state_relation4] _].
        unfold StateRelMonad.nrm in H3.
        destruct H3 as [_ state_equal5].
        unfold StateRelMonad.nrm in H5.
        destruct H5 as [_ state_equal6].
        pose proof after_G_add_vertex x11 x13 x12 x14 x3 H6 as [state_equal7 _].
        pose proof after_G_add_vertex x13 x15 x14 x16 x5 H7 as [state_equal8 _].
        pose proof after_get_new_edge x16 x18 x17 H8 as [_ state_relation9].
        pose proof after_G_add_edge x15 x19 x18 x20 x17 x3 x.(startVertex) None H9 as [state_equal10 _].
        pose proof after_get_new_edge x20 x22 x21 H10 as [_ state_relation11].
        pose proof after_G_add_edge x19 x23 x22 x24 x21 x3 x1.(startVertex) None H11 as [state_equal12 _].
        pose proof after_get_new_edge x24 x26 x25 H12 as [_ state_relation13].
        pose proof after_G_add_edge x23 x27 x26 x28 x25 x.(endVertex) x5 None H13 as [state_equal14 _].
        pose proof after_get_new_edge x28 x30 x29 H14 as [_ state_relation15].
        pose proof after_G_add_edge x27 x31 x30 x32 x29 x1.(endVertex) x5 None H15 as [state_equal16 _].
        unfold StateRelMonad.nrm in H16.
        destruct H16 as [state_equal17 state_equal18].
        unfold StateRelMonad.nrm in H4.
        destruct H4 as [_ state_equal19].
        rewrite <- state_equal19.
        rewrite <- state_equal18.
        rewrite <- state_equal16.
        rewrite <- state_relation15.
        rewrite <- state_equal14.
        rewrite <- state_relation13.
        rewrite <- state_equal12.
        rewrite <- state_relation11.
        rewrite <- state_equal10.
        rewrite <- state_relation9.
        rewrite <- state_equal8.
        rewrite <- state_equal7.
        rewrite <- state_equal6.
        rewrite <- state_equal5.
        rewrite state_relation4.
        rewrite state_relation3.
        apply Z.le_trans with (m := x0.(max_v)).
        tauto.
        lia.
      -- (* 然后证明递归情况 *)
        intros.
        unfold ret_nfa in H4.
        destruct H4 as [final_graph_info state_equal3].
        assert (after_ret_nfa: elem1.(graph)=x7). {
          rewrite final_graph_info.
          reflexivity.
        }
        rewrite after_ret_nfa in H17.
        (* 至此把 gv ∈ elem1 转化到了 ∈ x7 下面相同处理一直往上递归到 x 和 x1 *)
        unfold StateRelMonad.nrm in H16.
        destruct H16 as [state_equal4 state_equal5].
        pose proof after_G_add_edge x27 x31 x30 x32 x29 x1.(endVertex) x5 None H15 as [state_equal6 [belong_trans1 _]].
        pose proof after_get_new_edge x28 x30 x29 H14 as [_ state_relation7].
        pose proof after_G_add_edge x23 x27 x26 x28 x25 x.(endVertex) x5 None H13 as [state_equal7 [belong_trans2 _]].
        pose proof after_get_new_edge x24 x26 x25 H12 as [_ state_relation8].
        pose proof after_G_add_edge x19 x23 x22 x24 x21 x3 x1.(startVertex) None H11 as [state_equal8 [belong_trans3 _]].
        pose proof after_get_new_edge x20 x22 x21 H10 as [_ state_relation9].
        pose proof after_G_add_edge x15 x19 x18 x20 x17 x3 x.(startVertex) None H9 as [state_equal9 [belong_trans4 _]].
        pose proof after_get_new_edge x16 x18 x17 H8 as [_ state_relation10].
        pose proof after_G_add_vertex x13 x15 x14 x16 x5 H7 as [state_equal10 [belong_trans5 _]].
        pose proof after_G_add_vertex x11 x13 x12 x14 x3 H6 as [state_equal11 [belong_trans6 _]].
        unfold StateRelMonad.nrm in H5.
        destruct H5 as [union_x_x1 state_equal12].
        unfold StateRelMonad.nrm in H3.
        destruct H3 as [union_empty_x state_equal13].
        pose proof after_get_new_vertex x4 x6 x5 H2 as [[x5_range state_relation14] _].
        pose proof after_get_new_vertex x2 x4 x3 H1 as [[x3_range state_relation15] _].
        destruct union_empty_x.
        destruct union_pg0; clear union_edge union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4.
        unfold Sets_disjoint_union in union_vertex.
        sets_unfold in union_vertex.
        destruct union_vertex as [_ exist_in_empty_x].
        pose proof exist_in_empty_x gv; clear exist_in_empty_x.
        simpl in H3.
        destruct H3 as [forward_empty_x backward_empty_x].
        (* backward_empty_x 是从 gv ∈ x9 推 gv ∈ x (因为另一张图是 false) *)
        destruct union_x_x1.
        destruct union_pg0; clear union_edge union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4.
        unfold Sets_disjoint_union in union_vertex.
        sets_unfold in union_vertex.
        destruct union_vertex as [_ exist_in_x_x1].
        pose proof exist_in_x_x1 gv; clear exist_in_x_x1.
        destruct H3 as [forward_x_x1 backward_x_x1].
        (* 这里已经可以证出了，从 gv ∈ x31.(vvalid) 可以推出四种情况讨论:
        1. gv = x5
        2. gv = x3
        3. gv ∈ x1.(vvalid)
        4. gv ∈ x.(vvalid)
        每种情况都能推出 s1.(max_v) < gv <= s2.(max_v)
        *)
        rewrite state_equal4 in H17.
        pose proof belong_trans1 gv as temp.
        destruct temp as [? _].
        pose proof H3 H17.
        pose proof belong_trans2 gv as temp.
        destruct temp as [? _].
        pose proof H5 H4.
        pose proof belong_trans3 gv as temp.
        destruct temp as [? _].
        pose proof H18 H16.
        pose proof belong_trans4 gv as temp.
        destruct temp as [? _].
        pose proof H20 H19.
        pose proof belong_trans5 gv as temp.
        destruct temp as [? _].
        pose proof H22 H21.
        destruct H23.
        ** (* gv = x5 的情况 用 x5_range 证明是正确的 *)
          (* 但是 x5_range 是关于 x4 和 x6 还需要先把他们推到 s1 s2 *)
          rewrite H23.
          rewrite state_relation15 in x5_range.
          split.
          lia.
          rewrite state_equal13 in x5_range.
          rewrite state_equal12 in x5_range.
          rewrite state_equal11 in x5_range.
          rewrite state_equal10 in x5_range.
          rewrite state_relation10 in x5_range.
          rewrite state_equal9 in x5_range.
          rewrite state_relation9 in x5_range.
          rewrite state_equal8 in x5_range.
          rewrite state_relation8 in x5_range.
          rewrite state_equal7 in x5_range.
          rewrite state_relation7 in x5_range.
          rewrite state_equal6 in x5_range.
          rewrite state_equal5 in x5_range.
          rewrite state_equal3 in x5_range.
          lia.
        ** (* gv != x5 则说明 ∈ gv ∈ (x13.(pg)).(vvalid) *) 
          pose proof belong_trans6 gv as temp.
          destruct temp as [? _].
          pose proof H24 H23.
          destruct H25.
          *** (* gv = x3 的情况 用 x3_range 证明是正确的 *)
            (* 但是 x3_range 是关于 x2 和 x4 还需要先把他们推到 s1 s2 *)
            rewrite H25.
            split.
            lia.
            apply Z.le_trans with (m := x4.(max_v)).
            tauto.
            apply Z.le_trans with (m := x6.(max_v)).
            lia.
            rewrite state_equal13.
            rewrite state_equal12.
            rewrite state_equal11.
            rewrite state_equal10.
            rewrite state_relation10.
            rewrite state_equal9.
            rewrite state_relation9.
            rewrite state_equal8.
            rewrite state_relation8.
            rewrite state_equal7.
            rewrite state_relation7.
            rewrite state_equal6.
            rewrite state_equal5.
            rewrite state_equal3.
            lia.
          *** (* gv != x3 则后面推 gv ∈ x1.(vvalid) 或 gv ∈ x.(vvalid) 两种情况 *)
            pose proof backward_x_x1 H25.
            destruct H26 as [not_in_x1 | in_x1].
            2: {
              pose proof belong_g2 gv in_x1.
              split.
              lia.
              apply Z.le_trans with (m := x2.(max_v) + 1).
              lia.
              rewrite <- state_relation15.
              apply Z.le_trans with (m := x6.(max_v)).
              lia.
              rewrite state_equal13.
              rewrite state_equal12.
              rewrite state_equal11.
              rewrite state_equal10.
              rewrite state_relation10.
              rewrite state_equal9.
              rewrite state_relation9.
              rewrite state_equal8.
              rewrite state_relation8.
              rewrite state_equal7.
              rewrite state_relation7.
              rewrite state_equal6.
              rewrite state_equal5.
              rewrite state_equal3.
              lia.
            }
            (* not_in_x1 的情况 再推几行就得到了 gv ∈ x.(vvalid) *)
            pose proof backward_empty_x not_in_x1.
            destruct H26 as [contra | in_x].
            contradiction.
            pose proof belong_g1 gv in_x.
            split.
            lia.
            apply Z.le_trans with (m := x2.(max_v)).
            lia.
            apply Z.le_trans with (m := x4.(max_v)).
            lia.
            apply Z.le_trans with (m := x6.(max_v)).
            lia.
            rewrite state_equal13.
            rewrite state_equal12.
            rewrite state_equal11.
            rewrite state_equal10.
            rewrite state_relation10.
            rewrite state_equal9.
            rewrite state_relation9.
            rewrite state_equal8.
            rewrite state_relation8.
            rewrite state_equal7.
            rewrite state_relation7.
            rewrite state_equal6.
            rewrite state_equal5.
            rewrite state_equal3.
            lia.
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H4.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.nrm in H8.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.nrm in H9.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.nrm in H10.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.nrm in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    unfold ret_nfa in H3.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    assert (after_ret_nfa: elem1.(graph)=x5). {
      rewrite H3.
      reflexivity.
    }
    clear H3.
    unfold StateRelMonad.nrm in H12.
    destruct H12.
    (* 接下来展开所有基础步骤 即 after_xxx *)
    pose proof after_get_new_vertex x0 x2 x1 H0 as [[_ state_relation1] _].
    pose proof after_get_new_vertex x2 x4 x3 H1 as [[_ state_relation2] _].
    destruct H2.
    destruct H2.
    destruct union_pg0.
    unfold Sets_disjoint_union in union_vertex; clear union_edge union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4.
    sets_unfold in union_vertex.
    destruct union_vertex.
    pose proof after_G_add_vertex x7 x9 x8 x10 x1 H4 as [state_equal3 _].
    pose proof after_G_add_vertex x9 x11 x10 x12 x3 H5 as [state_equal4 _].
    pose proof after_get_new_edge x12 x14 x13 H6 as [_ state_relation3].
    pose proof after_G_add_edge x11 x15 x14 x16 x13 x1 x.(endVertex) None H7 as [state_equal5 _].
    pose proof after_get_new_edge x16 x18 x17 H8 as [_ state_relation4].
    pose proof after_G_add_edge x15 x19 x18 x20 x17 x.(endVertex) x3 None H9 as [state_equal6 _].
    pose proof after_get_new_edge x20 x22 x21 H10 as [_ state_relation5].
    pose proof after_G_add_edge x19 x23 x22 x24 x21 x.(endVertex) x.(startVertex) None H11 as [state_equal7 _].
    pose proof IHr s1 x x0 H as [state_relation6 belong_x].
    split.
    1: {
      apply Z.le_trans with (m := x2.(max_v)).
      lia.
      apply Z.le_trans with (m := x4.(max_v)).
      lia.
      (* 以下是从 x4 重写到 s2 的过程（中间所有状态相同）*)
      rewrite H14.
      rewrite state_equal3.
      rewrite state_equal4.
      rewrite state_relation3.
      rewrite state_equal5.
      rewrite state_relation4.
      rewrite state_equal6.
      rewrite state_relation5.
      rewrite state_equal7.
      rewrite H12.
      rewrite H13.
      lia.
    }
    intros.
    pose proof belong_x gv as belong_x.
    clear IHr.
    rewrite after_ret_nfa in H16.
    rewrite H3 in H16.
    unfold StateRelMonad.nrm in H11.
    destruct H11.
    destruct H11.
    destruct add_edge_pg0.
    Sets_unfold in add_edge_vertex; clear add_edge_edge add_edge_src_old add_edge_src_new add_edge_dst_old add_edge_dst_new add_edge_symbol_old0 add_edge_symbol_new0.
    pose proof add_edge_vertex gv as temp.
    destruct temp as [_ back].
    pose proof back H16; clear back add_edge_vertex.
    unfold StateRelMonad.nrm in H9.
    destruct H9.
    destruct H9.
    destruct add_edge_pg0.
    Sets_unfold in add_edge_vertex; clear add_edge_edge add_edge_src_old add_edge_src_new add_edge_dst_old add_edge_dst_new add_edge_symbol_old0 add_edge_symbol_new0.
    pose proof add_edge_vertex gv as temp.
    destruct temp as [_ back].
    pose proof back H11; clear back add_edge_vertex.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    destruct H7.
    destruct add_edge_pg0.
    Sets_unfold in add_edge_vertex; clear add_edge_edge add_edge_src_old add_edge_src_new add_edge_dst_old add_edge_dst_new add_edge_symbol_old0 add_edge_symbol_new0.
    pose proof add_edge_vertex gv as temp.
    destruct temp as [_ back].
    pose proof back H9; clear back add_edge_vertex.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct add_vertex_pg0.
    Sets_unfold in add_vertex_vertex; clear add_vertex_edge add_vertex_src add_vertex_dst add_vertex_symbol0.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex as [_ ?].
    pose proof H5 gv as temp.
    destruct temp as [_ back].
    pose proof back H7; clear back H5.
    (* 得到 (x9.(pg)).(vvalid) gv \/ x3 = gv *)
    destruct H21 as [gv_in_x9 | gv_is_x3].
    1: {
      unfold StateRelMonad.nrm in H4.
      destruct H4.
      destruct H4.
      destruct add_vertex_pg0; clear add_vertex_symbol0.
      Sets_unfold in add_vertex_vertex; clear add_vertex_edge add_vertex_src add_vertex_dst.
      unfold Sets_disjoint_union in add_vertex_vertex.
      sets_unfold in add_vertex_vertex.
      destruct add_vertex_vertex as [_ ?].
      pose proof H4 gv as temp.
      destruct temp as [_ back].
      pose proof back gv_in_x9; clear back H4.
      (* 这里再分成 (x7.(pg)).(vvalid) gv \/ x1 = gv 
        其中 ∈ x7 就是属于 x
      *)
      destruct H21 as [gv_in_x7 | gv_is_x1].
      1: {
        pose proof H15 gv as temp.
        destruct temp as [_ back].
        pose proof back gv_in_x7; clear back H15.
        simpl in H4.
        destruct H4.
        contradiction.
        (* 这里是 gv ∈ x 的情况 *)
        pose proof belong_x H4.
        split.
        lia.
        apply Z.le_trans with (m := x2.(max_v)).
        lia.
        apply Z.le_trans with (m := x4.(max_v)).
        lia.
        rewrite H14.
        rewrite state_equal3.
        rewrite state_equal4.
        rewrite state_relation3.
        rewrite state_equal5.
        rewrite state_relation4.
        rewrite state_equal6.
        rewrite state_relation5.
        rewrite state_equal7.
        rewrite H12.
        rewrite H13.
        lia.
      }
      (* 这里是 gv = x1 的情况 *)
      rewrite <- gv_is_x1.
      pose proof after_get_new_vertex x0 x2 x1 H0 as [[x1_range _] _].
      split.
      lia.
      apply Z.le_trans with (m := x4.(max_v)).
      lia.
      rewrite H14.
      rewrite state_equal3.
      rewrite state_equal4.
      rewrite state_relation3.
      rewrite state_equal5.
      rewrite state_relation4.
      rewrite state_equal6.
      rewrite state_relation5.
      rewrite state_equal7.
      rewrite H12.
      rewrite H13.
      lia.
    }
    (* 这里是 gv = x3 的情况 *)
    rewrite <- gv_is_x3.
    pose proof after_get_new_vertex x2 x4 x3 H1 as [[x3_range _] _].
    split.
    apply Z.le_lt_trans with (m := x0.(max_v)).
    lia.
    lia.
    rewrite H14 in x3_range.
    rewrite state_equal3 in x3_range.
    rewrite state_equal4 in x3_range.
    rewrite state_relation3 in x3_range.
    rewrite state_equal5 in x3_range.
    rewrite state_relation4 in x3_range.
    rewrite state_equal6 in x3_range.
    rewrite state_relation5 in x3_range.
    rewrite state_equal7 in x3_range.
    rewrite H12 in x3_range.
    rewrite H13 in x3_range.
    lia.
Qed.

(* 过regexToNfa获得的nfa的点都在前后state的max_v中。 *)
Lemma vvalid_range :
	forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
	(s1, elem1, s2) ∈ (regexToNFA r).(nrm) ->
	(forall gv, gv ∈ elem1.(graph).(pg).(vvalid) -> s1.(max_v) < gv <= s2.(max_v)) /\ s1.(max_v) <= s2.(max_v).
Proof.
  intros.
  pose proof another_order_vvalid_range elem1 s1 s2 r.
  tauto.
Qed.

Lemma another_order_evalid_range :
	forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
	(s1, elem1, s2) ∈ (regexToNFA r).(nrm) -> s1.(max_e) <= s2.(max_e) /\
	forall ge, ge ∈ elem1.(graph).(pg).(evalid) -> s1.(max_e) < ge <= s2.(max_e).
Proof.
  intros T elem1 s1 s2 r H.
  revert s2 H.
  revert elem1.
  revert s1.
  induction r.
  + intros.
    unfold regexToNFA in H.
    unfold ret_nfa in H.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    pose proof e_range_graph_constr_singleton None s1 x0 x2 x4 x x1 x3 as e_range_singleton .
    pose proof H1 as graph_constr_temp.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H4.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    pose proof after_get_new_vertex s1 x0 x H as [_ e_state_equal1].
    pose proof after_get_new_vertex x0 x2 x1 H0 as [_ e_state_equal2].
    pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H1 as [e_state_equal3 ?].
    pose proof after_G_add_vertex x5 x7 x6 x8 x1 H4 as [e_state_equal4 ?].
    pose proof after_get_new_edge x8 x10 x9 H5 as [[_ e_state_equal5] _].
    pose proof after_G_add_edge x7 x11 x10 x12 x9 x x1 None H6 as [e_state_equal6 ?].
    split.
    1: {
      unfold StateRelMonad.nrm in H7.
      destruct H7.
      rewrite e_state_equal1.
      rewrite e_state_equal2.
      rewrite e_state_equal3.
      rewrite e_state_equal4.
      rewrite <- H3.
      rewrite <- H11.
      rewrite <- e_state_equal6.
      lia.
    }
    intros.
    assert (after_ret_nfa: elem1.(graph)=x3). {
      rewrite H2.
      reflexivity.
    }
    rewrite after_ret_nfa in H11.
    destruct H7.
    rewrite H7 in H11.
    destruct H10 as [_ temp].
    pose proof temp ge as temp.
    destruct temp as [temp _].
    pose proof temp H11; clear temp.
    clear e_range_singleton.
    destruct H10.
    (* 下面分为 ge ∈ x7.graph 或 ge==x9 *)
    - (* ge=x9 的情况 *)
      pose proof after_get_new_edge x8 x10 x9 H5 as [[x9_range _] _].
      split.
      2: {
        rewrite <- H3.
        rewrite <- H12.
        rewrite <- e_state_equal6.
        lia.
      }
      rewrite e_state_equal1.
      rewrite e_state_equal2.
      rewrite e_state_equal3.
      rewrite e_state_equal4.
      lia.
    - (* ge ∈ x7.graph 的情况 *)
      pose proof after_G_add_vertex x5 x7 x6 x8 x1 H4 as [_ [_ temp]].
      pose proof temp ge as temp.
      destruct temp as [forward _].
      pose proof forward H10; clear forward.
      clear H8 H9.
      pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H1 as [_ [_ temp]].
      pose proof temp ge as temp.
      destruct temp as [forward _].
      pose proof forward H13; clear forward.
      simpl in H8.
      tauto.
  + intros.
    unfold regexToNFA in H.
    unfold act_singleton in H.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    split.
    1: {
      pose proof after_get_new_vertex s1 x0 x H as [_ edge_equal1].
      pose proof after_get_new_vertex x0 x2 x1 H0 as [_ edge_equal2].
      unfold graph_constr in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      unfold StateRelMonad.nrm in H3.
      destruct H3.
      destruct H3.
      destruct H3.
      unfold StateRelMonad.nrm in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold StateRelMonad.nrm in H5.
      destruct H5.
      destruct H5.
      destruct H5.
      pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H1 as [state_equal3 _].
      pose proof after_G_add_vertex x5 x7 x6 x8 x1 H3 as [state_equal4 _].
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      unfold StateRelMonad.nrm in H2.
      destruct H2.
      pose proof after_G_add_edge x7 x11 x10 x12 x9 x x1 (Some t) H5 as [state_equal5].
      pose proof after_get_new_edge x8 x10 x9 H4 as [[_ edge_equal6] _].
      rewrite <- H8.
      rewrite <- H7.
      rewrite <- state_equal5.
      rewrite edge_equal6.
      rewrite <- state_equal4.
      rewrite <- state_equal3.
      apply Z.le_trans with (m := x0.(max_e)).
      lia.
      lia.
    }
    1: {
      intros.
      unfold graph_constr in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      unfold StateRelMonad.nrm in H4.
      destruct H4.
      destruct H4.
      destruct H4.
      unfold StateRelMonad.nrm in H5.
      destruct H5.
      destruct H5.
      destruct H5.
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold StateRelMonad.nrm in H7.
      destruct H7.
      unfold StateRelMonad.nrm in H2.
      destruct H2.
      assert (after_ret_nfa: elem1.(graph)=x3). {
        rewrite H2.
        reflexivity.
      }
      rewrite after_ret_nfa in H3.
      rewrite H7 in H3.
      pose proof after_G_add_edge x7 x11 x10 x12 x9 x x1 (Some t) H6 as [state_equal1 [_ temp]].
      pose proof temp ge as temp.
      destruct temp as [forward _].
      pose proof forward H3; clear forward.
      destruct H10.
      (* 下面分为 ge=x9 和 ge ∈ x7.graph 两种情况 *)
      - (* ge=x9 的情况 *)
        pose proof after_get_new_edge x8 x10 x9 H5 as [[x9_range edge_equal2] _].
        split.
        2: {
          rewrite <- H9.
          rewrite <- H8.
          rewrite <- state_equal1.
          lia.
        }
        pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H1 as [state_equal3 _].
        pose proof after_G_add_vertex x5 x7 x6 x8 x1 H4 as [state_equal4 _].
        pose proof after_get_new_vertex s1 x0 x H as [_ edge_equal5].
        pose proof after_get_new_vertex x0 x2 x1 H0 as [_ edge_equal6].
        rewrite edge_equal5.
        rewrite edge_equal6.
        rewrite state_equal3.
        rewrite state_equal4.
        lia.
      - (* 下面是 ge ∈ x7.graph 的情况 *)
        pose proof after_G_add_vertex x5 x7 x6 x8 x1 H4 as [state_equal2 [_ temp]].
        pose proof temp ge as temp.
        destruct temp as [forward _].
        pose proof forward H10; clear forward.
        pose proof after_G_add_vertex empty_nfa x5 x2 x6 x H1 as [state_equal3 [_ temp]].
        pose proof temp ge as temp.
        destruct temp as [forward _].
        pose proof forward H11; clear forward.
        simpl in H12.
        tauto.
    }
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H4.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    pose proof IHr1 s1 x x0 H as [state_relation1 belong_g1].
    pose proof IHr2 x0 x1 x2 H0 as [state_relation2 belong_g2].
    clear IHr1 IHr2.
    clear H H0.
    (* 展开状态转移情况 *)
    pose proof after_get_new_edge x8 x10 x9 H4 as [[x9_range state_equal3] _].
    split.
    1: {
      unfold StateRelMonad.nrm in H2.
      destruct H2 as [_ ?].
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      unfold StateRelMonad.nrm in H5.
      destruct H5 as [_ ?].
      unfold StateRelMonad.nrm in H3.
      destruct H3 as [_ ?].
      unfold StateRelMonad.nrm in H1.
      destruct H1 as [_ ?].
      rewrite <- H.
      rewrite <- H2.
      rewrite <- H5.
      rewrite state_equal3.
      rewrite <- H3.
      rewrite <- H1.
      apply Z.le_trans with (m := x0.(max_e)).
      lia.
      lia.
    }
    1: {
      intros.
      unfold StateRelMonad.nrm in H2.
      destruct H2.
      assert (after_ret_nfa: elem1.(graph)=x3). {
        rewrite H0.
        reflexivity.
      }
      rewrite after_ret_nfa in H; clear after_ret_nfa H0.
      unfold StateRelMonad.nrm in H6.
      destruct H6.
      rewrite H0 in H; clear H0.
      pose proof after_G_add_edge x7 x11 x10 x12 x9 x.(endVertex) x1.(startVertex) None H5 as [state_equal4 [_ temp]].
      pose proof temp ge as temp.
      destruct temp as [temp _].
      pose proof temp H; clear temp.
      destruct H0.
      (* 分成 ge=x9 和 ge ∈ x7.graph 两种情况 *)
      - (* ge = x9 的情况 *)
        split.
        2: {
          rewrite <- H2.
          rewrite <- H6.
          rewrite <- state_equal4.
          lia.
        }
        apply Z.le_lt_trans with (m := x0.(max_e)).
        lia.
        apply Z.le_lt_trans with (m := x2.(max_e)).
        lia.
        unfold StateRelMonad.nrm in H1.
        destruct H1.
        rewrite H7.
        unfold StateRelMonad.nrm in H3.
        destruct H3.
        rewrite H8.
        lia.
      - (* ge ∈ x7.graph 的情况 *)
        unfold StateRelMonad.nrm in H3.
        destruct H3.
        destruct H3.
        destruct union_pg0.
        unfold Sets_disjoint_union in union_edge.
        sets_unfold in union_edge.
        destruct union_edge as [_ ?].
        pose proof H3 ge as temp.
        destruct temp as [_ temp].
        pose proof temp H0; clear temp.
        clear union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4 union_vertex.
        destruct H8.
        (* 这里再分为 ge ∈ x5 (再推一步到递归情况x) 和 ge ∈ x1 (递归情况x1) 两种情况 *)
        -- (* ge ∈ x5 的情况 *)
          unfold StateRelMonad.nrm in H1.
          destruct H1.
          destruct H1.
          destruct union_pg0.
          clear union_vertex union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4.
          unfold Sets_disjoint_union in union_edge.
          sets_unfold in union_edge.
          destruct union_edge as [_ ?].
          pose proof H1 ge as temp.
          destruct temp as [_ temp].
          pose proof temp H8; clear temp.
          destruct H10.
          simpl in H10.
          contradiction.
          (* ge ∈ x.graph 的情况，是递推情况 *)
          pose proof belong_g1 ge H10.
          split.
          lia.
          rewrite <- H2.
          rewrite <- H6.
          rewrite <- state_equal4.
          rewrite state_equal3.
          rewrite <- H7.
          rewrite <- H9.
          lia.
        -- pose proof belong_g2 ge H8.
          split.
          lia.
          rewrite <- H2.
          rewrite <- H6.
          rewrite <- state_equal4.
          rewrite state_equal3.
          rewrite <- H7.
          unfold StateRelMonad.nrm in H1.
          destruct H1 as [_ ?].
          rewrite <- H1.
          lia.
    }
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.nrm in H8.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.nrm in H9.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.nrm in H10.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.nrm in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    unfold StateRelMonad.nrm in H12.
    destruct H12.
    destruct H12.
    destruct H12.
    unfold StateRelMonad.nrm in H13.
    destruct H13.
    destruct H13.
    destruct H13.
    unfold StateRelMonad.nrm in H14.
    destruct H14.
    destruct H14.
    destruct H14.
    unfold StateRelMonad.nrm in H15.
    destruct H15.
    destruct H15.
    destruct H15.
    unfold StateRelMonad.nrm in H16.
    destruct H16.
    destruct H16.
    destruct H16.
    unfold StateRelMonad.nrm in H17.
    destruct H17.
    pose proof IHr1 s1 x x0 H as [state_relation1 belong_g1].
    pose proof IHr2 x0 x1 x2 H0 as [state_relation2 belong_g2].
    clear IHr1 IHr2.
    clear H H0.
    unfold StateRelMonad.nrm in H4.
    destruct H4.
    split.
    1: {
      pose proof after_G_add_edge x27 x31 x30 x32 x29 x1.(endVertex) x5 None H16 as [state_equal3 _].
      pose proof after_get_new_edge x28 x30 x29 H15 as [[_ state_relation4] _].
      pose proof after_G_add_edge x23 x27 x26 x28 x25 x.(endVertex) x5 None H14 as [state_equal5 _].
      pose proof after_get_new_edge x24 x26 x25 H13 as [[_ state_relation6] _].
      pose proof after_G_add_edge x19 x23 x22 x24 x21 x3 x1.(startVertex) None H12 as [state_equal7 _].
      pose proof after_get_new_edge x20 x22 x21 H11 as [[_ state_relation8] _].
      pose proof after_G_add_edge x15 x19 x18 x20 x17 x3 x.(startVertex) None H10 as [state_equal9 _].
      pose proof after_get_new_edge x16 x18 x17 H9 as [[_ state_relation10] _].
      pose proof after_G_add_vertex x13 x15 x14 x16 x5 H8 as [state_equal11 _].
      pose proof after_G_add_vertex x11 x13 x12 x14 x3 H7 as [state_equal12 _].
      unfold StateRelMonad.nrm in H5.
      destruct H5 as [_ ?].
      pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal13].
      pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal14].
      apply Z.le_trans with (m := x0.(max_e)).
      lia.
      apply Z.le_trans with (m := x2.(max_e)).
      lia.
      rewrite state_equal14.
      rewrite state_equal13.
      rewrite H6.
      rewrite H4.
      rewrite state_equal12.
      rewrite state_equal11.
      apply Z.le_trans with (m := x18.(max_e)).
      lia.
      rewrite state_equal9.
      apply Z.le_trans with (m := x22.(max_e)).
      lia.
      rewrite state_equal7.
      apply Z.le_trans with (m := x26.(max_e)).
      lia.
      rewrite state_equal5.
      apply Z.le_trans with (m := x30.(max_e)).
      lia.
      rewrite state_equal3.
      rewrite H18.
      rewrite H0.
      lia.
    }
    intros.
    assert (after_ret_nfa: elem1.(graph)=x7). {
      rewrite H.
      reflexivity.
    }
    rewrite after_ret_nfa in H4; clear after_ret_nfa.
    rewrite H17 in H4.
    pose proof after_G_add_edge x27 x31 x30 x32 x29 x1.(endVertex) x5 None H16 as [state_equal3 [_ ?]].
    pose proof H19 ge as temp; clear H19.
    destruct temp as [temp _].
    pose proof temp H4; clear temp.
    pose proof after_get_new_edge x28 x30 x29 H15 as [[x29_range state_relation4] _].
    pose proof after_G_add_edge x23 x27 x26 x28 x25 x.(endVertex) x5 None H14 as [state_equal5 [_ ?]].
    pose proof after_get_new_edge x24 x26 x25 H13 as [[x25_range state_relation6] _].
    pose proof after_G_add_edge x19 x23 x22 x24 x21 x3 x1.(startVertex) None H12 as [state_equal7 [_ ?]].
    pose proof after_get_new_edge x20 x22 x21 H11 as [[x21_range state_relation8] _].
    pose proof after_G_add_edge x15 x19 x18 x20 x17 x3 x.(startVertex) None H10 as [state_equal9 [_ ?]].
    pose proof after_get_new_edge x16 x18 x17 H9 as [[x17_range state_relation10] _].
    pose proof after_G_add_vertex x13 x15 x14 x16 x5 H8 as [state_equal11 [_ ?]].
    pose proof after_G_add_vertex x11 x13 x12 x14 x3 H7 as [state_equal12 [_ ?]].
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H19.
    (* 分成 ge=x29 和 ge ∈ x27 两种情况 *)
    (* 先排除 ge=x29 *)
    split.
    2: {
      rewrite <- H0.
      rewrite <- H18.
      rewrite <- state_equal3.
      lia.
    }
    (* 从 s1 推到 x28 *)
    apply Z.le_lt_trans with (m := x0.(max_e)).
    lia.
    apply Z.le_lt_trans with (m := x2.(max_e)).
    lia.
    pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal13].
    pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal14].
    rewrite state_equal13.
    rewrite state_equal14.
    rewrite H6.
    rewrite H25.
    rewrite state_equal12.
    rewrite state_equal11.
    apply Z.lt_trans with (m := x18.(max_e)).
    lia.
    rewrite state_equal9.
    apply Z.lt_trans with (m := x22.(max_e)).
    lia.
    rewrite state_equal7.
    apply Z.lt_trans with (m := x26.(max_e)).
    lia.
    rewrite state_equal5.
    apply Z.lt_le_trans with (m := x30.(max_e)).
    lia.
    lia.
    (* 排除了 ge = x29 往下推 ge ∈ x27.graph *)
    clear H4 x29_range.
    pose proof H20 ge as temp; clear H20.
    destruct temp as [temp _].
    pose proof temp H5; clear temp.
    (* 再分成 ge=x25 和 ge ∈ x23.graph *)
    (* 
    x25_range: max_e x24 < x25 <= max_e x26
    *)
    destruct H4.
    split.
    2: {
      rewrite <- H0.
      rewrite <- H18.
      rewrite <- state_equal3.
      apply Z.le_trans with (m := x26.(max_e)).
      lia.
      rewrite state_equal5.
      lia.
    }
    apply Z.le_lt_trans with (m := x0.(max_e)).
    lia.
    apply Z.le_lt_trans with (m := x2.(max_e)).
    lia.
    pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal13].
    pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal14].
    rewrite state_equal13.
    rewrite state_equal14.
    rewrite H6.
    rewrite H25.
    rewrite state_equal12.
    rewrite state_equal11.
    apply Z.lt_trans with (m := x18.(max_e)).
    lia.
    rewrite state_equal9.
    apply Z.lt_trans with (m := x22.(max_e)).
    lia.
    rewrite state_equal7.
    lia.
    (* 至此排除 ge=x25 往下推 ge ∈ x23.graph *)
    clear H5 x25_range.
    pose proof H21 ge as temp.
    destruct temp as [temp _].
    pose proof temp H4; clear temp.
    (* 再分成 ge=x21 和 ge ∈ x19.graph *)
    destruct H5.
    (* 
    x21_range: max_e x20 < x21 <= max_e x22
    *)
    split.
    1: {
      apply Z.le_lt_trans with (m := x0.(max_e)).
      lia.
      apply Z.le_lt_trans with (m := x2.(max_e)).
      lia.
      pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal13].
      pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal14].
      rewrite state_equal13.
      rewrite state_equal14.
      rewrite H6.
      rewrite H25.
      rewrite state_equal12.
      rewrite state_equal11.
      apply Z.lt_trans with (m := x18.(max_e)).
      lia.
      rewrite state_equal9.
      lia.
    }
    rewrite <- H0.
    rewrite <- H18.
    rewrite <- state_equal3.
    apply Z.le_trans with (m := x22.(max_e)).
    lia.
    rewrite state_equal7.
    apply Z.le_trans with (m := x26.(max_e)).
    lia.
    rewrite state_equal5.
    lia.
    (* 至此排除 ge=x21 往下推 ge ∈ x19.graph *)
    clear H4 x21_range H21.
    pose proof H22 ge as temp.
    destruct temp as [temp _].
    pose proof temp H5.
    (* 再分成 ge=x17 和 ge ∈ x15.graph *)
    destruct H4.
    (* 
    x17_range: max_e x16 < x17 <= max_e x18
    *)
    split.
    1: {
      apply Z.le_lt_trans with (m := x0.(max_e)).
      lia.
      apply Z.le_lt_trans with (m := x2.(max_e)).
      lia.
      pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal13].
      pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal14].
      rewrite state_equal13.
      rewrite state_equal14.
      rewrite H6.
      rewrite H25.
      rewrite state_equal12.
      rewrite state_equal11.
      lia.
    }
    rewrite <- H0.
    rewrite <- H18.
    rewrite <- state_equal3.
    apply Z.le_trans with (m := x18.(max_e)).
    lia.
    rewrite state_equal9.
    apply Z.le_trans with (m := x22.(max_e)).
    lia.
    rewrite state_equal7.
    apply Z.le_trans with (m := x26.(max_e)).
    lia.
    rewrite state_equal5.
    lia.
    (* 至此排除 ge=x17 往下推 ge ∈ x15.graph *)
    clear H22 x17_range temp.
    pose proof H23 ge as temp.
    destruct temp as [temp _].
    pose proof temp H4; clear temp.
    pose proof H24 ge as temp.
    destruct temp as [temp _].
    pose proof temp H19; clear temp.
    destruct union_pg0.
    unfold Sets_disjoint_union in union_edge.
    sets_unfold in union_edge; clear union_vertex union_src1 union_src2 union_dst1 union_dst2 union_symbol3 union_symbol4.
    destruct union_edge as [_ temp].
    pose proof temp ge as temp.
    destruct temp as [_ temp].
    pose proof temp H20; clear temp.
    (* 再分成 ge ∈ x9.graph (再推一步得递归情况x) 和 ge ∈ x1.graph (递归情况x1) *)
    destruct H21.
    2: {
      (* 递归情况 ge ∈ x1.graph *)
      pose proof belong_g2 ge H21.
      split.
      lia.
      (* max_e x0 < ge <= max_e x2 *)
      apply Z.le_trans with (m := x2.(max_e)).
      lia.
      pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal13].
      pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal14].
      rewrite state_equal13.
      rewrite state_equal14.
      rewrite H6.
      rewrite H25.
      rewrite state_equal12.
      rewrite state_equal11.
      apply Z.le_trans with (m := x18.(max_e)).
      lia.
      rewrite state_equal9.
      apply Z.le_trans with (m := x22.(max_e)).
      lia.
      rewrite state_equal7.
      apply Z.le_trans with (m := x26.(max_e)).
      lia.
      rewrite state_equal5.
      apply Z.le_trans with (m := x30.(max_e)).
      lia.
      rewrite state_equal3.
      rewrite H18.
      rewrite H0.
      lia.
    }
    (* ge ∈ x9.graph (再推一步得递归情况x) *)
    destruct H3.
    destruct union_pg0; clear union_symbol3 union_symbol4.
    unfold Sets_disjoint_union in union_edge; clear union_vertex union_src1 union_src2 union_dst1 union_dst2.
    sets_unfold in union_edge.
    destruct union_edge as [_ ?].
    pose proof H3 ge as temp.
    destruct temp as [_ temp].
    pose proof temp H21; clear temp.
    destruct H22.
    simpl in H22.
    contradiction.
    (* ge ∈ x.graph 的递归情况 *)
    pose proof belong_g1 ge H22.
    (* max_e s1 < ge <= max_e x0 *)
    split.
    lia.
    apply Z.le_trans with (m := x0.(max_e)).
    lia.
    apply Z.le_trans with (m := x2.(max_e)).
    lia.
    pose proof after_get_new_vertex x2 x4 x3 H1 as [_ state_equal13].
    pose proof after_get_new_vertex x4 x6 x5 H2 as [_ state_equal14].
    rewrite state_equal13.
    rewrite state_equal14.
    rewrite H6.
    rewrite H25.
    rewrite state_equal12.
    rewrite state_equal11.
    apply Z.le_trans with (m := x18.(max_e)).
    lia.
    rewrite state_equal9.
    apply Z.le_trans with (m := x22.(max_e)).
    lia.
    rewrite state_equal7.
    apply Z.le_trans with (m := x26.(max_e)).
    lia.
    rewrite state_equal5.
    apply Z.le_trans with (m := x30.(max_e)).
    lia.
    rewrite state_equal3.
    rewrite H18.
    rewrite H0.
    lia.
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.nrm in H8.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.nrm in H9.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.nrm in H10.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.nrm in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    unfold StateRelMonad.nrm in H12.
    destruct H12.
    destruct H12.
    destruct H12.
    unfold StateRelMonad.nrm in H13.
    destruct H13.
    pose proof IHr s1 x x0 H as [state_relation1 belong_x].
    clear IHr H.
    split.
    1: {
      pose proof after_G_add_edge x19 x23 x22 x24 x21 x.(endVertex) x.(startVertex) None H12 as [x22_x24 _].
      pose proof after_get_new_edge x20 x22 x21 H11 as [[_ x22_x20_1] _].
      pose proof after_G_add_edge x15 x19 x18 x20 x17 x.(endVertex) x3 None H10 as [x18_x20 _].
      pose proof after_get_new_edge x16 x18 x17 H9 as [[_ x18_x16_1] _].
      pose proof after_G_add_edge x11 x15 x14 x16 x13 x1 x.(endVertex) None H8 as [x14_x16 _].
      pose proof after_get_new_edge x12 x14 x13 H7 as [[_ x14_x12_1] _].
      pose proof after_G_add_vertex x9 x11 x10 x12 x3 H6 as [x10_x12 _].
      pose proof after_G_add_vertex x7 x9 x8 x10 x1 H5 as [x8_x10 _].
      unfold StateRelMonad.nrm in H2.
      destruct H2 as [_ x4_x8].
      pose proof after_get_new_vertex x2 x4 x3 H1 as [_ x2_x4].
      pose proof after_get_new_vertex x0 x2 x1 H0 as [_ x0_x2].
      (* 从 s1 推到 s2 *)
      apply Z.le_trans with (m := x0.(max_e)).
      lia.
      rewrite x0_x2.
      rewrite x2_x4.
      rewrite x4_x8.
      rewrite x8_x10.
      rewrite x10_x12.
      apply Z.le_trans with (m := x14.(max_e)).
      lia.
      rewrite x14_x16.
      apply Z.le_trans with (m := x18.(max_e)).
      lia.
      rewrite x18_x20.
      apply Z.le_trans with (m := x22.(max_e)).
      lia.
      rewrite x22_x24.
      rewrite H14.
      rewrite H4.
      lia.    
    }
    intros.
    assert (after_ret_nfa: elem1.(graph)=x5). {
      rewrite H3.
      reflexivity.
    }
    rewrite after_ret_nfa in H.
    clear H3 after_ret_nfa.
    rewrite H13 in H; clear H13.
    unfold StateRelMonad.nrm in H12.
    destruct H12 as [? x22_x24].
    destruct H3.
    destruct add_edge_pg0; clear add_edge_symbol_old0 add_edge_symbol_new0.
    unfold Sets_disjoint_union in add_edge_edge.
    sets_unfold in add_edge_edge.
    clear add_edge_vertex add_edge_src_old add_edge_dst_old add_edge_src_new add_edge_dst_new.
    destruct add_edge_edge as [_ temp].
    pose proof temp ge as temp.
    destruct temp as [_ temp].
    pose proof temp H; clear temp.
    pose proof after_get_new_edge x20 x22 x21 H11 as [[x21_range x22_x20_1] _].
    pose proof after_G_add_edge x15 x19 x18 x20 x17 x.(endVertex) x3 None H10 as [x18_x20 [_ trans1]].
    pose proof after_get_new_edge x16 x18 x17 H9 as [[x17_range x18_x16_1] _].
    pose proof after_G_add_edge x11 x15 x14 x16 x13 x1 x.(endVertex) None H8 as [x14_x16 [_ trans2]].
    pose proof after_get_new_edge x12 x14 x13 H7 as [[x13_range x14_x12_1] _].
    pose proof after_G_add_vertex x9 x11 x10 x12 x3 H6 as [x10_x12 [_ trans3]].
    pose proof after_G_add_vertex x7 x9 x8 x10 x1 H5 as [x8_x10 _].
    unfold StateRelMonad.nrm in H2.
    destruct H2 as [x7_graph x4_x8].
    pose proof after_get_new_vertex x2 x4 x3 H1 as [_ x2_x4].
    pose proof after_get_new_vertex x0 x2 x1 H0 as [_ x0_x2].
    (* 开始讨论 ge 在不同图中的结果 *)
    (* 首先是 ge ∈ x19 和 ge=x21  *)
    destruct H3.
    2: {
      (* 先排除 ge=x21 的情况 *)
      (* max_e x20 < x21 <= max_e x22 *)
      split.
      apply Z.le_lt_trans with (m := x0.(max_e)).
      lia.
      rewrite x0_x2.
      rewrite x2_x4.
      rewrite x4_x8.
      rewrite x8_x10.
      rewrite x10_x12.
      apply Z.le_lt_trans with (m := x14.(max_e)).
      lia.
      rewrite x14_x16.
      apply Z.le_lt_trans with (m := x18.(max_e)).
      lia.
      rewrite x18_x20.
      lia.
      rewrite <- H4.
      rewrite <- H14.
      rewrite <- x22_x24.
      lia.
    }
    clear x21_range.
    pose proof trans1 ge as temp.
    destruct temp as [temp _].
    pose proof temp H2; clear temp trans1.
    (* ge=x17 和 ge ∈ x15 两种情况 *)
    destruct H3.
    1: {
      (* max_e x16 < x17 <= max_e x18 *)
      split.
      apply Z.le_lt_trans with (m := x0.(max_e)).
      lia.
      rewrite x0_x2.
      rewrite x2_x4.
      rewrite x4_x8.
      rewrite x8_x10.
      rewrite x10_x12.
      apply Z.le_lt_trans with (m := x14.(max_e)).
      lia.
      rewrite x14_x16.
      lia.
      rewrite <- H4.
      rewrite <- H14.
      rewrite <- x22_x24.
      apply Z.le_trans with (m := x20.(max_e)).
      2: lia.
      apply Z.le_trans with (m := x18.(max_e)).
      lia.
      rewrite x18_x20.
      lia.
    }
    (* 至此排除 ge=x17，往下讨论 ge ∈ x15 *)
    pose proof trans2 ge as temp.
    destruct temp as [temp _].
    pose proof temp H3; clear temp trans2 x17_range.
    (* ge=x13 和 ge ∈ x11 两种情况 *)
    destruct H12.
    1: {
      (* max_e x12 < x13 <= max_e x14 *)
      split.
      apply Z.le_lt_trans with (m := x0.(max_e)).
      lia.
      rewrite x0_x2.
      rewrite x2_x4.
      rewrite x4_x8.
      rewrite x8_x10.
      rewrite x10_x12.
      lia.
      apply Z.le_trans with (m := x14.(max_e)).
      lia.
      rewrite x14_x16.
      apply Z.le_trans with (m := x18.(max_e)).
      lia.
      rewrite x18_x20.
      apply Z.le_trans with (m := x22.(max_e)).
      lia.
      rewrite x22_x24.
      rewrite H14.
      rewrite H4.
      lia.
    }
    (* 至此排除 ge=x13，往下讨论 ge ∈ x11 *)
    pose proof trans3 ge as temp.
    destruct temp as [temp _].
    pose proof temp H12; clear temp trans3 x13_range.
    unfold StateRelMonad.nrm in H5.
    destruct H5 as [? _].
    destruct H5.
    destruct add_vertex_pg0; clear add_vertex_symbol0.
    clear add_vertex_vertex add_vertex_src add_vertex_dst.
    rewrite <- add_vertex_edge in H13.
    destruct x7_graph.
    destruct union_pg0; clear union_symbol3 union_symbol4.
    unfold Sets_disjoint_union in union_edge; clear union_vertex union_src1 union_src2 union_dst1 union_dst2.
    sets_unfold in union_edge.
    destruct union_edge as [_ temp].
    pose proof temp ge as temp.
    destruct temp as [_ temp].
    pose proof temp H13; clear temp.
    destruct H5.
    simpl in H5.
    contradiction.
    pose proof belong_x ge H5.
    (* 到递推情况 x.graph *)
    (* max_e s1 < ge <= max_e x0 *)
    split.
    lia.
    apply Z.le_trans with (m := x0.(max_e)).
    lia.
    rewrite x0_x2.
    rewrite x2_x4.
    rewrite x4_x8.
    rewrite x8_x10.
    rewrite x10_x12.
    apply Z.le_trans with (m := x14.(max_e)).
    lia.
    rewrite x14_x16.
    apply Z.le_trans with (m := x18.(max_e)).
    lia.
    rewrite x18_x20.
    apply Z.le_trans with (m := x22.(max_e)).
    lia.
    rewrite x22_x24.
    rewrite H14.
    rewrite H4.
    lia.    
Qed.

(* 过regexToNfa获得的nfa的边都在前后state的max_e中。 *)
Lemma evalid_range :
  forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
  (s1, elem1, s2) ∈ (regexToNFA r).(nrm) ->
  (forall ge, ge ∈ elem1.(graph).(pg).(evalid) -> s1.(max_e) < ge <= s2.(max_e)) /\ s1.(max_e) <= s2.(max_e).
Proof.
  intros.
  pose proof another_order_evalid_range elem1 s1 s2 r H.
  tauto.
Qed.

(* 在两个正则表达式的 NFA 中，如果它们的转移关系在某些状态下成立，则这两个 NFA 中的 vvalid 和 evalid 集合不会重叠。 *)
Lemma no_overlap_between_two_nfa_if_they_are_from_same_state_series :
  forall {T: Type} (r1 r2: reg_exp T) (s1 s2 s3: state) (elem1 elem2: elem T),
  (s1, elem1, s2) ∈ (regexToNFA r1).(nrm) ->
  (s2, elem2, s3) ∈ (regexToNFA r2).(nrm) ->
  ~ Sets_overlap (elem1.(graph).(pg)).(vvalid) (elem2.(graph).(pg)).(vvalid) /\
  ~ Sets_overlap (elem1.(graph).(pg)).(evalid) (elem2.(graph).(pg)).(evalid).
Proof.
  intros.
  unfold Sets_overlap.
  unfold not.
  split.
  - intros Hcontra1.
    destruct Hcontra1 as [v [Hcontra1 Hcontra2]].
    pose proof (vvalid_range elem1 s1 s2 r1 H).
    destruct H1.
    apply H1 in Hcontra1.
    pose proof (vvalid_range elem2 s2 s3 r2 H0).
    destruct H3.
    apply H3 in Hcontra2.
    lia.
  - intros Hcontra1.
    destruct Hcontra1 as [v [Hcontra1 Hcontra2]].
    pose proof (evalid_range elem1 s1 s2 r1 H).
    destruct H1.
    apply H1 in Hcontra1.
    pose proof (evalid_range elem2 s2 s3 r2 H0).
    destruct H3.
    apply H3 in Hcontra2.
    lia.
Qed.
        
(* 如果构建nfa的过程是err这种状态，那么可以推出false *)
Lemma derive_false :
  forall (T : Type) (r1 : reg_exp T)  ,
    forall (s1:state), s1 ∈ (regexToNFA r1).(err) ->
    False.
Proof.
  intros.
  revert s1 H.
  induction r1.
  3:{
    intros s.
    intros.
    unfold StateRelMonad.err in H.
    sets_unfold in H.
    destruct H.
    pose proof IHr1_1 s.
    tauto.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.err in H0.
    sets_unfold in H0.
    destruct H0.
    pose proof IHr1_2 x0.
    tauto.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold Sets_overlap in H1.
    unfold empty_nfa in H1.
    destruct H1.
    simpl in H1.
    tauto.
    unfold Sets_overlap in H1.
    simpl in H1.
    destruct H1.
    tauto.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    3:{
      destruct H2.
      destruct H2.
      destruct H2.
      unfold StateRelMonad.err in H3.
      sets_unfold in H3.
      destruct H3.
      unfold StateRelMonad.err in H3.
      sets_unfold in H3.
      destruct H3.
      destruct H3.
      destruct H3.
      destruct H3.
      unfold StateRelMonad.err in H4.
      sets_unfold in H4.
      destruct H4.
      unfold StateRelMonad.err in H4.
      sets_unfold in H4.
      unfold G_add_edge in H4.
      unfold StateRelMonad.nrm in H3.
      sets_unfold in H3.
      unfold get_new_edge in H3.
      destruct H3.
      destruct H5.
      2:{
        destruct H4.
        destruct H4.
        destruct H4.
        unfold StateRelMonad.err in H5.
        sets_unfold in H5.
        destruct H5.
      }
      pose proof add_graph_maxe_equal x4 x6 x5 x3 x1.(graph) H2.
      pose proof add_graph_maxe_equal x2 x4 x3 empty_nfa x.(graph) H1.
      pose proof add_graph_num_edge2 x4 x6 x5 x3 x1.(graph) H2 x7 H4.
      destruct H9.
      pose proof add_graph_num_edge2 x2 x4 x3 empty_nfa x.(graph) H1 x7 H9.
      unfold empty_nfa in H10.
      simpl in H10.
      destruct H10.
      tauto.
      pose proof evalid_range x s x0 r1_1 H.
      destruct H11.
      pose proof H11 x7 H10.
      pose proof evalid_range x1 x0 x2 r1_2 H0.
      destruct H14.
      lia.
      pose proof evalid_range x1 x0 x2 r1_2 H0.
      destruct H10.
      pose proof H10 x7 H9.
      lia.
    }
    3:{
      destruct H1.
      destruct H1.
      destruct H1.
      unfold StateRelMonad.err in H2.
      sets_unfold in H2.
      destruct H2.
    }
    unfold StateRelMonad.nrm in H1.
    sets_unfold in H1.
    destruct H1.
    destruct H1.
    unfold Sets_overlap in H2.
    destruct H2.
    destruct H1.
    destruct union_pg0.
    unfold empty_nfa in union_vertex.
    simpl in union_vertex.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex.
    pose proof H5 x5.
    destruct H6.
    pose proof H7 H1.
    pose proof no_overlap_between_two_nfa_if_they_are_from_same_state_series r1_1 r1_2 s x0 x2 x x1.
    pose proof H9 H H0.
    destruct H10.
    unfold Sets_overlap in H10.
    unfold not in H10.
    apply H10.
    exists x5.
    tauto.
    unfold StateRelMonad.nrm in H1.
    sets_unfold in H1.
    destruct H1.
    destruct H1.
    unfold Sets_overlap in H2.
    destruct H2.
    destruct H1.
    destruct union_pg0.
    unfold empty_nfa in union_edge.
    simpl in union_edge.
    unfold Sets_disjoint_union in union_edge.
    sets_unfold in union_edge.
    destruct union_edge.
    pose proof H5 x5.
    destruct H6.
    pose proof H7 H1.
    pose proof no_overlap_between_two_nfa_if_they_are_from_same_state_series r1_1 r1_2 s x0 x2 x x1.
    pose proof H9 H H0.
    destruct H10.
    unfold Sets_overlap in H11.
    unfold not in H11.
    apply H11.
    exists x5.
    tauto.
  }
  3:{
    intros s.
    intros.
    unfold StateRelMonad.err in H.
    sets_unfold in H.
    destruct H.
    pose proof IHr1_1 s.
    tauto.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.err in H0.
    sets_unfold in H0.
    destruct H0.
    pose proof IHr1_2 x0.
    tauto.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
    unfold Sets_overlap in H3.
    destruct H3.
    destruct H3.
    unfold empty_nfa in H3.
    simpl in H3.
    tauto.
    unfold Sets_overlap in H3.
    destruct H3.
    destruct H3.
    unfold empty_nfa in H3.
    simpl in H3.
    tauto.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    destruct H4.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    destruct H4.
    unfold Sets_overlap in H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.nrm in H3.
    sets_unfold in H3.
    destruct H3.
    destruct H3.
    destruct union_pg0.
    unfold empty_nfa in union_vertex.
    simpl in union_vertex.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex.
    pose proof H7 x9.
    destruct H8.
    pose proof H9 H4.
    pose proof no_overlap_between_two_nfa_if_they_are_from_same_state_series r1_1 r1_2 s x0 x2 x x1.
    pose proof H11 H H0.
    destruct H12.
    unfold Sets_overlap in H12.
    unfold not in H12.
    apply H12.
    exists x9.
    tauto.
    unfold Sets_overlap in H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.nrm in H3.
    sets_unfold in H3.
    destruct H3.
    destruct H3.
    destruct union_pg0.
    unfold empty_nfa in union_edge.
    simpl in union_edge.
    unfold Sets_disjoint_union in union_edge.
    sets_unfold in union_edge.
    destruct union_edge.
    pose proof H7 x9.
    destruct H8.
    pose proof H9 H4.
    pose proof no_overlap_between_two_nfa_if_they_are_from_same_state_series r1_1 r1_2 s x0 x2 x x1.
    pose proof H11 H H0.
    destruct H12.
    unfold Sets_overlap in H13.
    unfold not in H13.
    apply H13.
    exists x9.
    tauto.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.err in H5.
    sets_unfold in H5.
    destruct H5.
    unfold StateRelMonad.err in H5.
    sets_unfold in H5.
    simpl in H5.
    pose proof add_graph_num_vertex2 x8 x10 x9 x7 x1.(graph) H4 x3 H5.
    pose proof add_graph_num_vertex2 x6 x8 x7 empty_nfa x.(graph) H3 x3.
    unfold empty_nfa in H7.
    simpl in H7.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H8.
    destruct H9.
    destruct H6.
    pose proof H7 H6.
    destruct H11.
    tauto.
    pose proof vvalid_range x s x0 r1_1 H.
    destruct H12.
    pose proof H12 x3 H11.
    pose proof vvalid_range x1 x0 x2 r1_2 H0.
    destruct H15.
    lia.
    pose proof vvalid_range x1 x0 x2 r1_2 H0.
    destruct H11.
    pose proof H11 x3 H6.
    lia.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.err in H6.
    sets_unfold in H6.
    destruct H6.
    unfold StateRelMonad.err in H6.
    sets_unfold in H6.
    simpl in H6.
    unfold StateRelMonad.nrm in H5.
    sets_unfold in H5.
    destruct H5.
    destruct H5.
    destruct add_vertex_pg0.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex.
    pose proof H8 x5.
    destruct H9.
    pose proof H10 H6.
    destruct H11.
    pose proof add_graph_num_vertex2 x8 x10 x9 x7 x1.(graph) H4 x5 H11.
    pose proof add_graph_num_vertex2 x6 x8 x7 empty_nfa x.(graph) H3 x5.
    unfold empty_nfa in H13.
    simpl in H13.
    pose proof get_new_vertex_num x4 x6 x5 H2.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H14.
    destruct H16.
    destruct H15.
    destruct H18.
    destruct H12.
    pose proof H13 H12.
    destruct H20.
    tauto.
    pose proof vvalid_range x s x0 r1_1 H.
    destruct H21.
    pose proof H21 x5 H20.
    pose proof vvalid_range x1 x0 x2 r1_2 H0.
    destruct H24.
    lia.
    pose proof vvalid_range x1 x0 x2 r1_2 H0.
    destruct H20.
    pose proof H20 x5 H12.
    lia.
    pose proof get_new_vertex_num x4 x6 x5 H2.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    lia.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.err in H7.
    sets_unfold in H7.
    destruct H7.
    unfold StateRelMonad.err in H7.
    sets_unfold in H7.
    simpl in H7.
    tauto.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.err in H8.
    sets_unfold in H8.
    destruct H8.
    unfold StateRelMonad.err in H8.
    sets_unfold in H8.
    simpl in H8.
    pose proof get_new_edge_num x14 x16 x15 H7.
    destruct H9.
    destruct H10.
    pose proof add_vertex_maxe_equal x12 x14 x13 x11 x5 H6.
    pose proof add_vertex_maxe_equal x10 x12 x11 x9 x3 H5.
    pose proof add_graph_maxe_equal x8 x10 x9 x7 x1.(graph) H4.
    pose proof add_graph_maxe_equal x6 x8 x7 empty_nfa x.(graph) H3.
    pose proof get_new_vertex_num x4 x6 x5 H2.
    destruct H16.
    destruct H17.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H19.
    destruct H20.
    pose proof add_vertex_edge_equal x12 x14 x13 x11 x5 H6 x15.
    destruct H22.
    pose proof H23 H8.
    pose proof add_vertex_edge_equal x10 x12 x11 x9 x3 H5 x15.
    destruct H25.
    pose proof H26 H24.
    pose proof add_graph_num_edge2 x8 x10 x9 x7 x1.(graph) H4 x15.
    pose proof H28 H27.
    destruct H29.
    pose proof add_graph_num_edge2 x6 x8 x7 empty_nfa x.(graph) H3 x15.
    pose proof H30 H29.
    unfold empty_nfa in H31.
    simpl in H31.
    destruct H31.
    tauto.
    pose proof evalid_range x s x0 r1_1 H.
    destruct H32.
    pose proof H32 x15 H31.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H35.
    lia.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H30.
    pose proof H30 x15 H29.
    lia.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.err in H9.
    sets_unfold in H9.
    destruct H9.
    unfold StateRelMonad.err in H9.
    sets_unfold in H9.
    simpl in H9.
    tauto.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.err in H10.
    sets_unfold in H10.
    destruct H10.
    unfold StateRelMonad.err in H10.
    sets_unfold in H10.
    simpl in H10.
    pose proof get_new_edge_num x18 x20 x19 H9.
    destruct H11.
    destruct H12.
    pose proof add_edge_maxe_equal x16 x18 x17 x13 x15 x3 x.(startVertex) epsilon H8.
    pose proof get_new_edge_num x14 x16 x15 H7.
    destruct H15.
    destruct H16.
    pose proof add_vertex_maxe_equal x12 x14 x13 x11 x5 H6.
    pose proof add_vertex_maxe_equal x10 x12 x11 x9 x3 H5.
    pose proof add_graph_maxe_equal x8 x10 x9 x7 x1.(graph) H4.
    pose proof add_graph_maxe_equal x6 x8 x7 empty_nfa x.(graph) H3.
    pose proof get_new_vertex_num x4 x6 x5 H2.
    destruct H22.
    destruct H23.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H25.
    destruct H26.
    pose proof add_edge_edge_equal x16 x18 x17 x13 x15 x3 x.(startVertex) epsilon H8 x19.
    destruct H28.
    pose proof H29 H10.
    destruct H30.
    pose proof add_vertex_edge_equal x12 x14 x13 x11 x5 H6 x19.
    destruct H31.
    pose proof H32 H30.
    pose proof add_vertex_edge_equal x10 x12 x11 x9 x3 H5 x19.
    destruct H34.
    pose proof H35 H33.
    pose proof add_graph_num_edge2 x8 x10 x9 x7 x1.(graph) H4 x19.
    pose proof H37 H36.
    destruct H38.
    pose proof add_graph_num_edge2 x6 x8 x7 empty_nfa x.(graph) H3 x19.
    pose proof H39 H38.
    unfold empty_nfa in H40.
    simpl in H40.
    destruct H40.
    tauto.
    pose proof evalid_range x s x0 r1_1 H.
    destruct H41.
    pose proof H41 x19 H40.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H44.
    lia.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H39.
    pose proof H39 x19 H38.
    lia.
    lia.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.err in H11.
    sets_unfold in H11.
    destruct H11.
    simpl in H11.
    tauto.
    destruct H11.
    destruct H11.
    destruct H11.
    unfold StateRelMonad.err in H12.
    sets_unfold in H12.
    destruct H12.
    unfold StateRelMonad.err in H12.
    sets_unfold in H12.
    simpl in H12.
    pose proof get_new_edge_num x22 x24 x23 H11.
    destruct H13.
    destruct H14.
    pose proof add_edge_edge_equal x20 x22 x21 x17 x19 x3 x1.(startVertex) epsilon H10 x23.
    destruct H16.
    pose proof H17 H12.
    pose proof get_new_edge_num x18 x20 x19 H9.
    destruct H19.
    destruct H20.
    pose proof add_edge_maxe_equal x20 x22 x21 x17 x19 x3 x1.(startVertex) epsilon H10.
    destruct H18.
    pose proof add_edge_edge_equal x16 x18 x17 x13 x15 x3 x.(startVertex) epsilon H8 x23.
    destruct H23.
    pose proof H24 H18.
    pose proof add_edge_maxe_equal x16 x18 x17 x13 x15 x3 x.(startVertex) epsilon H8.
    pose proof get_new_edge_num x14 x16 x15 H7.
    destruct H27.
    destruct H28.
    destruct H25.
    pose proof add_vertex_maxe_equal x12 x14 x13 x11 x5 H6.
    pose proof add_vertex_maxe_equal x10 x12 x11 x9 x3 H5.
    pose proof add_graph_maxe_equal x8 x10 x9 x7 x1.(graph) H4.
    pose proof add_graph_maxe_equal x6 x8 x7 empty_nfa x.(graph) H3.
    pose proof get_new_vertex_num x4 x6 x5 H2.
    destruct H34.
    destruct H35.
    pose proof add_vertex_edge_equal x12 x14 x13 x11 x5 H6 x23.
    destruct H37.
    pose proof H38 H25.
    pose proof add_vertex_edge_equal x10 x12 x11 x9 x3 H5 x23.
    destruct H40.
    pose proof H41 H39.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H43.
    destruct H44.
    pose proof add_graph_num_edge2 x8 x10 x9 x7 x1.(graph) H4 x23.
    pose proof H46 H42.
    destruct H47.
    pose proof add_graph_num_edge2 x6 x8 x7 empty_nfa x.(graph) H3 x23.
    pose proof H48 H47.
    unfold empty_nfa in H49.
    simpl in H49.
    destruct H49.
    tauto.
    pose proof evalid_range x s x0 r1_1 H.
    destruct H50.
    pose proof H50 x23 H49.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H53.
    lia.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H48.
    pose proof H48 x23 H47.
    lia.
    lia.
    lia.
    destruct H12.
    destruct H12.
    destruct H12.
    unfold StateRelMonad.err in H13.
    sets_unfold in H13.
    destruct H13.
    simpl in H13.
    tauto.
    destruct H13.
    destruct H13.
    destruct H13.
    unfold StateRelMonad.err in H14.
    sets_unfold in H14.
    destruct H14.
    unfold StateRelMonad.err in H14.
    sets_unfold in H14.
    simpl in H14.
    pose proof get_new_edge_num x26 x28 x27 H13.
    destruct H15.
    destruct H16.
    pose proof add_edge_maxe_equal x24 x26 x25 x21 x23 x.(endVertex) x5 epsilon H12.
    pose proof get_new_edge_num x22 x24 x23 H11.
    destruct H19.
    destruct H20.
    pose proof add_edge_maxe_equal x20 x22 x21 x17 x19 x3 x1.(startVertex) epsilon H10.
    pose proof get_new_edge_num x18 x20 x19 H9.
    destruct H23.
    destruct H24.
    pose proof add_edge_maxe_equal x16 x18 x17 x13 x15 x3 x.(startVertex) epsilon H8.
    pose proof get_new_edge_num x14 x16 x15 H7.
    destruct H27.
    destruct H28.
    pose proof add_vertex_maxe_equal x12 x14 x13 x11 x5 H6.
    pose proof add_vertex_maxe_equal x10 x12 x11 x9 x3 H5.
    pose proof add_graph_maxe_equal x8 x10 x9 x7 x1.(graph) H4.
    pose proof add_graph_maxe_equal x6 x8 x7 empty_nfa x.(graph) H3.
    pose proof get_new_vertex_num x4 x6 x5 H2.
    destruct H34.
    destruct H35.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H37.
    destruct H38.
    pose proof add_edge_edge_equal x24 x26 x25 x21 x23 x.(endVertex) x5 epsilon H12 x27.
    destruct H40.
    pose proof H41 H14.
    destruct H42.
    pose proof add_edge_edge_equal x20 x22 x21 x17 x19 x3 x1.(startVertex) epsilon H10 x27.
    destruct H43.
    pose proof H44 H42.
    destruct H45.
    pose proof add_edge_edge_equal x16 x18 x17 x13 x15 x3 x.(startVertex) epsilon H8 x27.
    destruct H46.
    pose proof H47 H45.
    destruct H48.
    pose proof add_vertex_edge_equal x12 x14 x13 x11 x5 H6 x27.
    destruct H49.
    pose proof H50 H48.
    pose proof add_vertex_edge_equal x10 x12 x11 x9 x3 H5 x27.
    destruct H52.
    pose proof H53 H51.
    pose proof add_graph_num_edge2 x8 x10 x9 x7 x1.(graph) H4 x27 H54.
    destruct H55.
    pose proof add_graph_num_edge2 x6 x8 x7 empty_nfa x.(graph) H3 x27 H55.
    unfold empty_nfa in H56.
    simpl in H56.
    destruct H56.
    tauto.
    pose proof evalid_range x s x0 r1_1 H.
    destruct H57.
    pose proof H57 x27 H56.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H60.
    lia.
    pose proof evalid_range x1 x0 x2 r1_2 H0.
    destruct H56.
    pose proof H56 x27 H55.
    lia.
    lia.
    lia.
    lia.
    destruct H14.
    destruct H14.
    destruct H14.
    unfold StateRelMonad.err in H15.
    sets_unfold in H15.
    destruct H15.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    destruct H4.
  }
  3:{
    intros.
    unfold StateRelMonad.err in H.
    sets_unfold in H.
    destruct H.
    pose proof IHr1 s1 H.
    tauto.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.err in H0.
    sets_unfold in H0.
    destruct H0.
    simpl in H0.
    tauto.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    simpl in H1.
    tauto.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    unfold Sets_overlap in H2.
    destruct H2.
    destruct H2.
    unfold empty_nfa in H2.
    simpl in H2.
    tauto.
    unfold Sets_overlap in H2.
    destruct H2.
    destruct H2.
    unfold empty_nfa in H2.
    simpl in H2.
    tauto.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    simpl in H3.
    pose proof add_graph_num_vertex2 x4 x6 x5 empty_nfa x.(graph) H2 x1 H3.
    unfold empty_nfa in H4.
    simpl in H4.
    destruct H4.
    tauto.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H5.
    destruct H6.
    pose proof vvalid_range x s1 x0 r1 H.
    destruct H8.
    pose proof H8 x1 H4.
    lia.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    destruct H4.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    simpl in H4.
    pose proof add_vertex_in_graph x6 x8 x7 x5 x1 H3 x3.
    destruct H5.
    pose proof H6 H4.
    pose proof add_vertex_maxv_equal x6 x8 x7 x5 x1 H3.
    pose proof add_graph_maxv_equal x4 x6 x5 empty_nfa x.(graph) H2.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H10.
    destruct H11.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H13.
    destruct H14.
    destruct H7.
    pose proof add_graph_num_vertex2 x4 x6 x5 empty_nfa x.(graph) H2 x3 H7.
    unfold empty_nfa in H16.
    simpl in H16.
    destruct H16.
    tauto.
    pose proof vvalid_range x s1 x0 r1 H.
    destruct H17.
    pose proof H17 x3 H16.
    lia.
    lia.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.err in H5.
    sets_unfold in H5.
    destruct H5.
    simpl in H5.
    tauto.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.err in H6.
    sets_unfold in H6.
    destruct H6.
    unfold StateRelMonad.err in H6.
    sets_unfold in H6.
    simpl in H6.
    pose proof get_new_edge_num x10 x12 x11 H5.
    destruct H7.
    destruct H8.
    pose proof add_vertex_maxe_equal x8 x10 x9 x7 x3 H4.
    pose proof add_vertex_maxe_equal x6 x8 x7 x5 x1 H3.
    pose proof add_graph_maxe_equal x4 x6 x5 empty_nfa x.(graph) H2.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H13.
    destruct H14.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H16.
    destruct H17.
    pose proof add_vertex_edge_equal x8 x10 x9 x7 x3 H4 x11.
    destruct H19.
    pose proof H20 H6.
    pose proof add_vertex_edge_equal x6 x8 x7 x5 x1 H3 x11.
    destruct H22.
    pose proof H23 H21.
    pose proof add_graph_num_edge2 x4 x6 x5 empty_nfa x.(graph) H2 x11 H24.
    unfold empty_nfa in H25.
    simpl in H25.
    destruct H25.
    tauto.
    pose proof evalid_range x s1 x0 r1 H.
    destruct H26.
    pose proof H26 x11 H25.
    lia.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.err in H7.
    sets_unfold in H7.
    destruct H7.
    simpl in H7.
    tauto.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.err in H8.
    sets_unfold in H8.
    destruct H8.
    unfold StateRelMonad.err in H8.
    sets_unfold in H8.
    simpl in H8.
    pose proof get_new_edge_num x14 x16 x15 H7.
    destruct H9.
    destruct H10.
    pose proof add_edge_maxe_equal x12 x14 x13 x9 x11 x1 x.(endVertex) epsilon H6.
    pose proof get_new_edge_num x10 x12 x11 H5.
    destruct H13.
    destruct H14.
    pose proof add_vertex_maxe_equal x8 x10 x9 x7 x3 H4.
    pose proof add_vertex_maxe_equal x6 x8 x7 x5 x1 H3.
    pose proof add_graph_maxe_equal x4 x6 x5 empty_nfa x.(graph) H2.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H19.
    destruct H20.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H22.
    destruct H23.
    pose proof add_edge_edge_equal x12 x14 x13 x9 x11 x1 x.(endVertex) epsilon H6 x15.
    destruct H25.
    pose proof H26 H8.
    destruct H27.
    pose proof add_vertex_edge_equal x8 x10 x9 x7 x3 H4 x15.
    destruct H28.
    pose proof H29 H27.
    pose proof add_vertex_edge_equal x6 x8 x7 x5 x1 H3 x15.
    destruct H31.
    pose proof H32 H30.
    pose proof add_graph_num_edge2 x4 x6 x5 empty_nfa x.(graph) H2 x15 H33.
    unfold empty_nfa in H34.
    simpl in H34.
    destruct H34.
    tauto.
    pose proof evalid_range x s1 x0 r1 H.
    destruct H35.
    pose proof H35 x15 H34.
    lia.
    lia.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.err in H9.
    sets_unfold in H9.
    destruct H9.
    simpl in H9.
    tauto.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.err in H10.
    sets_unfold in H10.
    destruct H10.
    unfold StateRelMonad.err in H10.
    sets_unfold in H10.
    simpl in H10.
    pose proof get_new_edge_num x18 x20 x19 H9.
    destruct H11.
    destruct H11.
    pose proof add_edge_maxe_equal x16 x18 x17 x13 x15 x.(endVertex) x3 epsilon H8.
    pose proof get_new_edge_num x14 x16 x15 H7.
    destruct H13.
    destruct H14.
    pose proof add_edge_maxe_equal x12 x14 x13 x9 x11 x1 x.(endVertex) epsilon H6.
    pose proof get_new_edge_num x10 x12 x11 H5.
    destruct H17.
    destruct H18.
    pose proof add_vertex_maxe_equal x8 x10 x9 x7 x3 H4.
    pose proof add_vertex_maxe_equal x6 x8 x7 x5 x1 H3.
    pose proof add_graph_maxe_equal x4 x6 x5 empty_nfa x.(graph) H2.
    pose proof get_new_vertex_num x2 x4 x3 H1.
    destruct H23.
    destruct H24.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H26.
    destruct H27.
    pose proof add_edge_edge_equal x16 x18 x17 x13 x15 x.(endVertex) x3 epsilon H8 x19.
    destruct H29.
    pose proof H30 H10.
    destruct H31.
    pose proof add_edge_edge_equal x12 x14 x13 x9 x11 x1 x.(endVertex) epsilon H6 x19.
    destruct H32.
    pose proof H33 H31.
    destruct H34.
    pose proof add_vertex_edge_equal x8 x10 x9 x7 x3 H4 x19.
    destruct H35.
    pose proof H36 H34.
    pose proof add_vertex_edge_equal x6 x8 x7 x5 x1 H3 x19.
    destruct H38.
    pose proof H39 H37.
    pose proof add_graph_num_edge2 x4 x6 x5 empty_nfa x.(graph) H2 x19 H40.
    unfold empty_nfa in H41.
    simpl in H41.
    destruct H41.
    tauto.
    pose proof evalid_range x s1 x0 r1 H.
    destruct H42.
    pose proof H42 x19 H41.
    lia.
    lia.
    lia.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.err in H11.
    sets_unfold in H11.
    destruct H11.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
  }
  + intros.
    unfold StateRelMonad.err in H.
    sets_unfold in H.
    unfold regexToNFA in H.
    destruct H.
    simpl in H.
    tauto.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.err in H0.
    sets_unfold in H0.
    destruct H0.
    simpl in H0.
    tauto.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.err in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    simpl in H2.
    pose proof add_vertex_in_graph x2 x4 x3 empty_nfa x H1 x1.
    destruct H3.
    pose proof H4 H2.
    unfold empty_nfa in H5.
    simpl in H5.
    destruct H5.
    tauto.
    pose proof get_new_vertex_num s1 x0 x H.
    destruct H6.
    destruct H7.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H9.
    destruct H10.
    lia.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
    simpl in H3.
    tauto.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    destruct H4.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    simpl in H4.
    pose proof get_new_edge_num x6 x8 x7 H3.
    destruct H5.
    destruct H6.
    pose proof add_vertex_maxe_equal x4 x6 x5 x3 x1 H2.
    pose proof add_vertex_maxe_equal x2 x4 x3 empty_nfa x H1.
    pose proof add_vertex_edge_equal x4 x6 x5 x3 x1 H2 x7.
    destruct H10.
    pose proof H11 H4.
    pose proof add_vertex_edge_equal x2 x4 x3 empty_nfa x H1 x7.
    destruct H13.
    pose proof H14 H12.
    unfold empty_nfa in H15.
    simpl in H15.
    tauto.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.err in H5.
    sets_unfold in H5.
    simpl in H5.
    tauto.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    simpl in H2.
    tauto.
  + intros.
    unfold StateRelMonad.err in H.
    sets_unfold in H.
    unfold regexToNFA in H.
    destruct H.
    simpl in H.
    tauto.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.err in H0.
    sets_unfold in H0.
    destruct H0.
    simpl in H0.
    tauto.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.err in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    unfold StateRelMonad.err in H1.
    sets_unfold in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    destruct H2.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    simpl in H2.
    pose proof add_vertex_in_graph x2 x4 x3 empty_nfa x H1 x1.
    destruct H3.
    pose proof H4 H2.
    unfold empty_nfa in H5.
    simpl in H5.
    destruct H5.
    tauto.
    pose proof get_new_vertex_num s1 x0 x H.
    destruct H6.
    destruct H7.
    pose proof get_new_vertex_num x0 x2 x1 H0.
    destruct H9.
    destruct H10.
    lia.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.err in H3.
    sets_unfold in H3.
    destruct H3.
    simpl in H3.
    tauto.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    destruct H4.
    unfold StateRelMonad.err in H4.
    sets_unfold in H4.
    simpl in H4.
    pose proof get_new_edge_num x6 x8 x7 H3.
    destruct H5.
    destruct H6.
    pose proof add_vertex_maxe_equal x4 x6 x5 x3 x1 H2.
    pose proof add_vertex_maxe_equal x2 x4 x3 empty_nfa x H1.
    pose proof add_vertex_edge_equal x4 x6 x5 x3 x1 H2 x7.
    destruct H10.
    pose proof H11 H4.
    pose proof add_vertex_edge_equal x2 x4 x3 empty_nfa x H1 x7.
    destruct H13.
    pose proof H14 H12.
    unfold empty_nfa in H15.
    simpl in H15.
    tauto.
    destruct H4.
    destruct H4.
    destruct H4.
    unfold StateRelMonad.err in H5.
    sets_unfold in H5.
    simpl in H5.
    tauto.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.err in H2.
    sets_unfold in H2.
    simpl in H2.
    tauto.
Qed.

(*********************************************************)
(**                                                      *)
(** Empty_String                                         *)
(**                                                      *)
(*********************************************************)

(* 正则表达式匹配到nfa匹配 *)
Lemma empty_string_hoare_backward {T: Type}:
  forall (str : list T) (s: state),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA EmptyStr_r)                           
    (fun (e : elem T) (s2 : state) =>                          
    exp_match EmptyStr_r str ->match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  unfold match_str.
  split.
  - intros.
    unfold act_singleton.
    intros contra.
    apply derive_false in contra.
    tauto.
  - intros.
    unfold exp_match in H1.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H3.
    inversion H1.
    simpl.
    destruct H4.
    rewrite H4.
    simpl.
    unfold e_steps.
    unfold clos_refl_trans.
    unfold Sets.indexed_union.
    simpl.
    exists Nat.one.
    simpl.
    unfold Rels.id.
    simpl.
    sets_unfold.
    exists x1.
    split.
    2:{
      tauto.
    }
    unfold e_step.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    exists x9.
    split.
    2:{
      destruct H9.
      destruct H9.
      rewrite H10.
      tauto.
    }
    split.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      destruct add_edge_edge.
      sets_unfold in H13.
      specialize (H13 x9).
      destruct H13.
      assert (H_or: (x7.(pg)).(evalid) x9 \/ x9 = x9).
      {
        right;lia.
      }
      apply H13 in H_or.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      destruct H7.
      destruct H7.
      destruct add_vertex_pg0.
      destruct H3.
      destruct H3.
      destruct add_vertex_pg0.
      destruct add_vertex_vertex0.
      sets_unfold in H13.
      specialize (H13 x).
      assert (H_or :False \/ x = x).
      {
        right;tauto. 
      }
      destruct H13.
      apply H13 in H_or.
      destruct add_vertex_vertex.
      sets_unfold in H16.
      specialize (H16 x).
      assert ( H_or0: (x5.(pg)).(vvalid) x \/ x1=x ).
      {
        left;tauto. 
      }
      destruct H16.
      apply H16 in H_or0.
      apply add_edge_vertex in H_or0.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      destruct H7.
      destruct H7.
      destruct add_vertex_pg0.
      destruct add_vertex_vertex.
      sets_unfold in H13.
      specialize (H13 x1).
      destruct H13.
      assert (H_or :(x5.(pg)).(vvalid) x1 \/ x1 = x1).
      {
        right;tauto. 
      }
      apply H13 in H_or.
      apply add_edge_vertex in H_or.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      tauto.
Qed.

(* nfa匹配到正则表达式匹配 *)
Lemma empty_string_hoare_forward {T: Type}:
  forall (str : list T) (s: state),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA EmptyStr_r)                           
    (fun (e : elem T) (s2 : state) =>                          
    match_str e.(graph) e.(startVertex) e.(endVertex) str->exp_match EmptyStr_r str).
Proof.
  intros str.
  intros s.
  unfold Hoare.
  split.
  - intros.
    intros contra.
    apply derive_false in contra.
    tauto.
  - intros.
    unfold exp_match.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H4.
    rewrite H4 in H1.
    simpl in H1.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold match_str in H1.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H9.
    rewrite H9 in H1.
    destruct H8.
    destruct H8.
    destruct add_edge_pg0.
    unfold string_step in H1.
    destruct str.
    + sets_unfold.
      tauto.
    + destruct H1.
      destruct H1.
      sets_unfold in H8.
      destruct H8.
      sets_unfold in H8.
      destruct H8.
      unfold e_steps in H12.
      unfold clos_refl_trans in H12.
      sets_unfold in H12.
      destruct H12.
      destruct x15.
      * intros.
        simpl in H12.
        unfold Rels.id in H12.
        simpl in H12.
        rewrite H12 in H8.
        destruct H8.
        destruct H8.
        destruct H8.
        destruct H8.
        destruct add_edge_edge.
        sets_unfold in H14.
        specialize (H14 x15).
        destruct H14.
        apply H15 in step_evalid.
        destruct step_evalid.
        2:{
          rewrite H16 in add_edge_symbol_new0.
          rewrite add_edge_symbol_new0 in H13.
          destruct H13.
          discriminate H13.
        }
        specialize(add_edge_symbol_old0 x15).
        pose proof H16.
        apply add_edge_symbol_old0 in H16.
        rewrite H16 in H13.
        destruct H6.
        destruct H6.
        destruct add_vertex_pg0.
        apply add_vertex_edge in H17.
        specialize (add_vertex_symbol0 x15).
        pose proof H17.
        apply add_vertex_symbol0 in H17.
        rewrite H17 in H13. 
        destruct H3.
        destruct H3.
        destruct add_vertex_pg0.
        apply add_vertex_edge0 in H6.
        specialize (add_vertex_symbol1 x15).
        apply add_vertex_symbol1 in H6.
        rewrite H6 in H13.
        simpl in H13.
        destruct H13.
        discriminate H3.
      * destruct x15.
        ++simpl in H12.
          destruct H12.
          unfold Rels.id in H12.
          simpl in H12.
          sets_unfold in H12.
          destruct H12.
          rewrite H13 in H12.
          destruct add_edge_edge.
          sets_unfold in H15.
          destruct H12.
          destruct H12.
          destruct H12.
          apply H15 in step_evalid.
          destruct step_evalid.
          2:{
            rewrite H12 in add_edge_src_new.
            rewrite add_edge_src_new in step_src.
            rewrite <- step_src in H8.
            destruct H8.
            destruct H8.
            destruct H8.
            destruct H8.
            specialize (H15 x17).
            destruct H15.
            apply H15 in step_evalid.
            destruct step_evalid.
            - destruct H6.
              destruct H6.
              destruct add_vertex_pg0.
              destruct H3.
              destruct H3.
              destruct add_vertex_pg0.
              apply add_vertex_edge in H18.
              apply add_vertex_edge0 in H18.
              simpl in H18.
              tauto.
            - rewrite H18 in add_edge_symbol_new0.
              rewrite add_edge_symbol_new0 in H17.
              destruct H17.
              discriminate H17.
          }
          destruct H6.
          destruct H6.
          destruct add_vertex_pg0.
          destruct H3.
          destruct H3.
          destruct add_vertex_pg0.
          apply add_vertex_edge in H12.
          apply add_vertex_edge0 in H12.
          simpl in H12.
          tauto.
        ++destruct H12.
          destruct H12.
          destruct H13.
          destruct H13.
          destruct H12.
          destruct H13.
          destruct H12.
          destruct H13.
          destruct H12.
          destruct H13.
          destruct add_edge_edge.
          sets_unfold in H13.
          apply H13 in step_evalid0.
          destruct step_evalid0.
          --destruct H6.
            destruct H6.
            destruct add_vertex_pg0.
            destruct H3.
            destruct H3.
            destruct add_vertex_pg0.
            apply add_vertex_edge in H17.
            apply add_vertex_edge0 in H17.
            simpl in H18.
            tauto.
          --apply H13 in step_evalid.
            destruct step_evalid.
            **destruct H6.
              destruct H6.
              destruct add_vertex_pg0.
              destruct H3.
              destruct H3.
              destruct add_vertex_pg0.
              apply add_vertex_edge in H18.
              apply add_vertex_edge0 in H18.
              simpl in H18.
              tauto.
            **rewrite <- H18 in step_dst.
              rewrite <- H17 in step_src0.
              rewrite add_edge_dst_new in step_dst.
              rewrite add_edge_src_new in step_src0.
              rewrite <- step_dst in step_src0.
              apply get_new_vertex_num in H0.
              apply get_new_vertex_num in H2.
              destruct H0.
              destruct H19.
              destruct H2.
              destruct H21.
              rewrite H2 in H22.
              rewrite <- H20 in H22.
              lia.
Qed.

(*********************************************************)
(**                                                      *)
(** Char_set                                             *)
(**                                                      *)
(*********************************************************)

(* 正则表达式匹配到nfa匹配 *)
Lemma char_set_hoare_backward {T: Type}:
  forall (str : list T) (s: state) (t:T->Prop),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA (Char_r t))                           
    (fun (e : elem T) (s2 : state) =>                          
    exp_match (Char_r t) str ->match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  unfold match_str.
  split.
  - intros.
    unfold act_singleton.
    intros contra.
    apply derive_false in contra.
    tauto.
  - intros.
    unfold exp_match in H1.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H3.
    inversion H1 as [t1 H5].
    simpl.
    destruct H4.
    rewrite H4.
    simpl.
    destruct H5 as [H5 Hs].
    rewrite Hs.
    simpl.
    unfold e_steps.
    unfold clos_refl_trans.
    unfold Sets.indexed_union.
    simpl.
    sets_unfold.
    exists x.
    split.
    1:{
      exists Nat.zero.
      simpl.
      unfold Rels.id.
      simpl.
      tauto.
    }
    unfold char_step.
    sets_unfold.
    exists x1.
    split.
    2:{
      unfold e_steps.
      unfold clos_refl_trans.
      sets_unfold.
      exists Nat.zero.
      simpl.
      unfold Rels.id.
      simpl.
      tauto.
    }
    unfold c_step.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    exists x9.
    exists t.
    split.
    2:{
      destruct H9.
      destruct H9.
      rewrite H10.
      split.
      2:{
        sets_unfold.
        tauto.
      }
      tauto.
    }
    split.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      destruct add_edge_edge.
      sets_unfold in H13.
      specialize (H13 x9).
      destruct H13.
      assert (H_or: (x7.(pg)).(evalid) x9 \/ x9 = x9).
      {
        right;lia.
      }
      apply H13 in H_or.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      destruct H7.
      destruct H7.
      destruct add_vertex_pg0.
      destruct H3.
      destruct H3.
      destruct add_vertex_pg0.
      destruct add_vertex_vertex0.
      sets_unfold in H13.
      specialize (H13 x).
      assert (H_or :False \/ x = x).
      {
        right;tauto. 
      }
      destruct H13.
      apply H13 in H_or.
      destruct add_vertex_vertex.
      sets_unfold in H16.
      specialize (H16 x).
      assert ( H_or0: (x5.(pg)).(vvalid) x \/ x1=x ).
      {
        left;tauto. 
      }
      destruct H16.
      apply H16 in H_or0.
      apply add_edge_vertex in H_or0.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      destruct H7.
      destruct H7.
      destruct add_vertex_pg0.
      destruct add_vertex_vertex.
      sets_unfold in H13.
      specialize (H13 x1).
      destruct H13.
      assert (H_or :(x5.(pg)).(vvalid) x1 \/ x1 = x1).
      {
        right;tauto. 
      }
      apply H13 in H_or.
      apply add_edge_vertex in H_or.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      tauto.
    * destruct H9.
      rewrite H10.
      destruct H9.
      destruct add_edge_pg0.
      tauto.
Qed.

(* nfa匹配到正则表达式匹配 *)
Lemma char_set_hoare_forward {T: Type}:
  forall (str : list T) (s: state)(t: T->Prop),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA (Char_r t))                           
    (fun (e : elem T) (s2 : state) =>                          
    match_str e.(graph) e.(startVertex) e.(endVertex) str->exp_match (Char_r t) str).
Proof.
  intros str.
  intros s.
  unfold Hoare.
  split.
  - intros.
    intros contra.
    apply derive_false in contra.
    tauto.
  - intros.
    unfold exp_match.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H4.
    rewrite H4 in H1.
    simpl in H1.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold match_str in H1.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H9.
    rewrite H9 in H1.
    destruct H8.
    destruct H8.
    destruct add_edge_pg0.
    unfold string_step in H1.
    destruct str.
    + sets_unfold.
      unfold e_steps in H1.
      unfold clos_refl_trans in H1.
      sets_unfold in H1.
      destruct H1.
      destruct x13.
      * simpl in H1.
        unfold Rels.id in H1.
        simpl in H1.
        apply get_new_vertex_num in H0.
        apply get_new_vertex_num in H2.
        destruct H0.
        destruct H8.
        destruct H2.
        destruct H13.
        rewrite H2 in H14.
        rewrite <- H12 in H14.
        lia.
      * destruct H1.
        destruct H1.
        simpl in H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct add_edge_edge.
        sets_unfold in H13.
        apply H13 in step_evalid.
        destruct step_evalid.
        --destruct H6.
          destruct H6.
          destruct add_vertex_pg0.
          destruct H3.
          destruct H3.
          destruct add_vertex_pg0.
          apply add_vertex_edge in H14.
          apply add_vertex_edge0 in H14.
          simpl in H14.
          tauto.
        --rewrite <- H14 in H12.
          rewrite add_edge_symbol_new0 in H12.
          discriminate H12.
    + destruct H1.
      destruct H1.
      destruct str.
      * sets_unfold in H8.
        destruct H8.
        sets_unfold in H8.
        destruct H8.
        destruct H1.
        destruct x15.
        2:{
          destruct H1.
          destruct H1.
          destruct H1.
          destruct H1.
          destruct H1.
          apply add_edge_edge in step_evalid.
          destruct step_evalid.
          - destruct H6.
            destruct H6.
            destruct add_vertex_pg0.
            destruct H3.
            destruct H3.
            destruct add_vertex_pg0.
            apply add_vertex_edge in H1.
            apply add_vertex_edge0 in H1.
            simpl in H1.
            tauto.
          - sets_unfold in H1.
            rewrite <- H1 in H14.
            rewrite add_edge_symbol_new0 in H14.
            discriminate H14.
        }
        simpl in H1.
        unfold Rels.id in H1.
        simpl in H1.
        unfold e_steps in H12.
        unfold clos_refl_trans in H12.
        sets_unfold in H12.
        destruct H12.
        destruct x15.
        2:{
          destruct H12.
          destruct H12.
          destruct H12.
          destruct H12.
          destruct H12.
          apply add_edge_edge in step_evalid.
          destruct step_evalid.
          - destruct H6.
            destruct H6.
            destruct add_vertex_pg0.
            destruct H3.
            destruct H3.
            destruct add_vertex_pg0.
            apply add_vertex_edge in H12.
            apply add_vertex_edge0 in H12.
            simpl in H12.
            tauto.
          - sets_unfold in H12.
            rewrite <- H12 in H14.
            rewrite add_edge_symbol_new0 in H14.
            discriminate H14.
        }
        simpl in H12.
        unfold Rels.id in H12.
        simpl in H12.
        rewrite <- H1 in H8.
        rewrite H12 in H8.
        destruct H8.
        destruct H8.
        destruct H8.
        destruct H8.
        destruct add_edge_edge.
        sets_unfold in H14.
        specialize (H14 x15).
        destruct H14.
        apply H15 in step_evalid.
        destruct step_evalid.
        2:{
          rewrite H16 in add_edge_symbol_new0.
          rewrite add_edge_symbol_new0 in H13.
          destruct H13.
          exists t0.
          split.
          - inversion H13.
            tauto.
          - tauto.
        }
        specialize(add_edge_symbol_old0 x15).
        pose proof H16.
        apply add_edge_symbol_old0 in H16.
        rewrite H16 in H13.
        destruct H6.
        destruct H6.
        destruct add_vertex_pg0.
        apply add_vertex_edge in H17.
        specialize (add_vertex_symbol0 x15).
        pose proof H17.
        apply add_vertex_symbol0 in H17.
        rewrite H17 in H13. 
        destruct H3.
        destruct H3.
        destruct add_vertex_pg0.
        apply add_vertex_edge0 in H6.
        specialize (add_vertex_symbol1 x15).
        apply add_vertex_symbol1 in H6.
        rewrite H6 in H13.
        simpl in H13.
        destruct H13.
        discriminate H3.
      * destruct H1.
        destruct H1.
        destruct H8.
        destruct H8.
        destruct H13.
        destruct x16.
        2:{
          destruct H13.
          destruct H13.
          destruct H13.
          destruct H13.
          destruct H13.
          apply add_edge_edge in step_evalid.
          destruct step_evalid.
          - destruct H6.
            destruct H6.
            destruct add_vertex_pg0.
            destruct H3.
            destruct H3.
            destruct add_vertex_pg0.
            apply add_vertex_edge in H13.
            apply add_vertex_edge0 in H13.
            simpl in H13.
            tauto.
          - sets_unfold in H13.
            rewrite <- H13 in H15.
            rewrite add_edge_symbol_new0 in H15.
            discriminate H15.
        }
        simpl in H13.
        unfold Rels.id in H13.
        simpl in H13.
        destruct H8.
        destruct H8.
        destruct H8.
        rewrite H13 in H8.
        destruct H8.
        destruct H12.
        destruct H8.
        destruct H12.
        destruct x19.
        2:{
          destruct H12.
          destruct H12.
          destruct H12.
          destruct H12.
          destruct H12.
          apply add_edge_edge in step_evalid0.
          destruct step_evalid0.
          - destruct H6.
            destruct H6.
            destruct add_vertex_pg0.
            destruct H3.
            destruct H3.
            destruct add_vertex_pg0.
            apply add_vertex_edge in H12.
            apply add_vertex_edge0 in H12.
            simpl in H12.
            tauto.
          - sets_unfold in H12.
            rewrite <- H12 in H16.
            rewrite add_edge_symbol_new0 in H16.
            discriminate H16.
        }
        simpl in H12.
        unfold Rels.id in H12.
        simpl in H12.
        rewrite H12 in H8.
        destruct H8.
        destruct H8.
        destruct H8.
        destruct H8.
        destruct add_edge_edge.
        sets_unfold in H16.
        apply H16 in step_evalid.
        destruct step_evalid.
        2:{
          apply H16 in step_evalid0.
          destruct step_evalid0.
          - destruct H6.
            destruct H6.
            destruct add_vertex_pg0.
            destruct H3.
            destruct H3.
            destruct add_vertex_pg0.
            apply add_vertex_edge in H18.
            apply add_vertex_edge0 in H18.
            simpl in H18.
            tauto.
          - rewrite <- H18 in step_dst0.
            rewrite <- H17 in step_src.
            rewrite add_edge_dst_new in step_dst0.
            rewrite add_edge_src_new in step_src.
            rewrite <- step_dst0 in step_src.
            apply get_new_vertex_num in H0.
            apply get_new_vertex_num in H2.
            destruct H0.
            destruct H19.
            destruct H2.
            destruct H21.
            rewrite H2 in H22.
            rewrite <- H20 in H22.
            lia.
          }
        destruct H6.
        destruct H6.
        destruct add_vertex_pg0.
        destruct H3.
        destruct H3.
        destruct add_vertex_pg0.
        apply add_vertex_edge in H17.
        apply add_vertex_edge0 in H17.
        simpl in H17.
        tauto.
Qed.
    

(*********************************************************)
(**                                                      *)
(** step相关引理                                       *)
(**                                                      *)
(*********************************************************)

(* 通过 G_add_graph 操作合成图 g0 和图 g 后，图 g1 应该保留epsilon步的性质。 *)
Lemma e_step_add_graph_preserves1 :
forall {T} (g0 g: pg_nfa T) g1 x y (s: state),
  (s, g1,s) ∈ (G_add_graph g0 g).(nrm) -> 
  e_step g x y ->
  e_step g1 x y.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H.
  destruct union_pg0.
  unfold e_step in H0.
  destruct H0.
  destruct H.
  destruct H.
  unfold e_step.
  exists x0.
  split.
  - split.
    + unfold Sets_disjoint_union in union_edge.
      destruct union_edge.
      sets_unfold in H2.
      specialize (H2 x0).
      destruct H2.
      assert (H_or : (g0.(pg)).(evalid) x0 \/ (g.(pg)).(evalid) x0).
      {
        right.
        exact step_evalid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 x).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) x \/ (g.(pg)).(vvalid) x).
      {
        right. 
        exact step_src_valid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 y).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) y \/ (g.(pg)).(vvalid) y).
      {
        right. 
        exact step_dst_valid.
      }
      apply H2 in H_or.
      tauto.
    + specialize (union_src2 x0).
      sets_unfold in union_src2.
      apply union_src2 in step_evalid.
      rewrite <- step_evalid in step_src.
      tauto.
    + specialize (union_dst2 x0).
      sets_unfold in union_dst2.
      apply union_dst2 in step_evalid.
      rewrite <- step_evalid in step_dst.
      tauto.
  - specialize (union_symbol4 x0).
    sets_unfold in union_symbol4.
    apply union_symbol4 in step_evalid.
    rewrite <- step_evalid in H0.
    tauto.
Qed.

(* 通过 G_add_graph 操作合成图 g0 和图 g 后，图 g1 应该保留epsilon步的性质。 *)
Lemma e_step_add_edge_preserves :
forall {T} (g0  g1: pg_nfa T) (s1 s2: state)(e x1 y1 x y :Z),
  (s1, e, s2) ∈ get_new_edge.(nrm)->
  (s2, g1 ,s2) ∈ (G_add_edge g0 e x1 y1 epsilon).(nrm) -> 
  e_step g0 x y ->
  e_step g1 x y.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H.
  destruct add_edge_pg0.
  unfold e_step in H1.
  destruct H1.
  destruct H.
  destruct H.
  unfold e_step.
  exists x0.
  split.
  - split.
    + unfold Sets_disjoint_union in add_edge_edge.
      destruct add_edge_edge.
      sets_unfold in H3.
      specialize (H3 x0).
      destruct H3.
      assert (H_or : (g0.(pg)).(evalid) x0 \/ e = x0).
      {
        left.
        exact step_evalid.
      }
      apply H3 in H_or.
      tauto.
    + apply add_edge_vertex in step_src_valid.
      tauto.
    + apply add_edge_vertex in step_dst_valid.
      tauto.
    + apply add_edge_src_old in step_evalid.
      rewrite step_evalid.
      tauto.
    + apply add_edge_dst_old in step_evalid.
      rewrite step_evalid.
      tauto.
  - apply add_edge_symbol_old0 in step_evalid.
    rewrite step_evalid.
    tauto.
Qed.

(* 在图 g0 中存在从状态 x 到状态 y 的字符转移 c_step，
  并且在图 g1 中通过 G_add_edge 操作（添加新边）后，
  图 g1 中也会有从 x 到 y 的字符转移，
  即c_step 转移性质会得到保留 *)
Lemma c_step_add_edge_preserves :
forall {T} (g0  g1: pg_nfa T) (s1 s2: state)(e x1 y1 x y :Z)(a :T),
  (s1, e, s2) ∈ get_new_edge.(nrm)->
  (s2, g1 ,s2) ∈ (G_add_edge g0 e x1 y1 epsilon).(nrm) -> 
  c_step g0 a x y ->
  c_step g1 a x y .
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H.
  destruct add_edge_pg0.
  unfold e_step in H1.
  destruct H1.
  destruct H.
  destruct H.
  destruct H.
  unfold e_step.
  exists x0.
  exists x2.
  split.
  - split.
    + unfold Sets_disjoint_union in add_edge_edge.
      destruct add_edge_edge.
      sets_unfold in H3.
      specialize (H3 x0).
      destruct H3.
      assert (H_or : (g0.(pg)).(evalid) x0 \/ e = x0).
      {
        left.
        exact step_evalid.
      }
      apply H3 in H_or.
      tauto.
    + apply add_edge_vertex in step_src_valid.
      tauto.
    + apply add_edge_vertex in step_dst_valid.
      tauto.
    + apply add_edge_src_old in step_evalid.
      rewrite step_evalid.
      tauto.
    + apply add_edge_dst_old in step_evalid.
      rewrite step_evalid.
      tauto.
  - apply add_edge_symbol_old0 in step_evalid.
    rewrite step_evalid.
    tauto.
Qed.

(* 如果在图 g0 中有一个从状态 x 到状态 y 的 epsilon 转移 e_step g0 x y，
  并且图 g1 是通过将 g0 和 g 合并生成的图，
  那么在图 g1 中也会有一个从 x 到 y 的 epsilon 转移 e_step g1 x y。
  即G_add_graph 操作不会破坏图中的 epsilon 转移。 *)
Lemma e_step_add_graph_preserves2 :
forall {T} (g0 g: pg_nfa T) g1 x y (s: state),
  (s, g1,s) ∈ (G_add_graph g0 g).(nrm) -> 
  e_step g0 x y ->
  e_step g1 x y.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H.
  destruct union_pg0.
  unfold e_step in H0.
  destruct H0.
  destruct H.
  destruct H.
  unfold e_step.
  exists x0.
  split.
  - split.
    + unfold Sets_disjoint_union in union_edge.
      destruct union_edge.
      sets_unfold in H2.
      specialize (H2 x0).
      destruct H2.
      assert (H_or : (g0.(pg)).(evalid) x0 \/ (g.(pg)).(evalid) x0).
      {
        left.
        exact step_evalid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 x).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) x \/ (g.(pg)).(vvalid) x).
      {
        left. 
        exact step_src_valid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 y).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) y \/ (g.(pg)).(vvalid) y).
      {
        left. 
        exact step_dst_valid.
      }
      apply H2 in H_or.
      tauto.
    + specialize (union_src1 x0).
      sets_unfold in union_src1.
      apply union_src1 in step_evalid.
      rewrite <- step_evalid in step_src.
      tauto.
    + specialize (union_dst1 x0).
      sets_unfold in union_dst1.
      apply union_dst1 in step_evalid.
      rewrite <- step_evalid in step_dst.
      tauto.
  - specialize (union_symbol3 x0).
    sets_unfold in union_symbol3.
    apply union_symbol3 in step_evalid.
    rewrite <- step_evalid in H0.
    tauto.
Qed.

(* 如果图 g0 和图 g 通过 G_add_graph 操作合并成图 g1，
  并且图 g 中存在从状态 x 到状态 y 的字符 c 转移，
  那么在合并后的图 g1 中也会有相同的转移。
  即G_add_graph 操作不会破坏图中的字符转移。 *)
Lemma c_step_add_graph_preserves1 :
forall {T} (g0 g: pg_nfa T) g1 x y (s: state) (c: T),
  (s,g1,s) ∈ (G_add_graph g0 g).(nrm) -> 
  c_step g c x y ->
  c_step g1 c x y.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H.
  destruct union_pg0.
  unfold c_step in H0.
  destruct H0.
  destruct H.
  destruct H.
  unfold c_step.
  exists x0.
  exists x1.
  split.
  - destruct H.
    split.
    + unfold Sets_disjoint_union in union_edge.
      destruct union_edge.
      sets_unfold in H2.
      specialize (H2 x0).
      destruct H2.
      assert (H_or : (g0.(pg)).(evalid) x0 \/ (g.(pg)).(evalid) x0).
      {
        right.
        exact step_evalid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 x).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) x \/ (g.(pg)).(vvalid) x).
      {
        right. 
        exact step_src_valid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 y).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) y \/ (g.(pg)).(vvalid) y).
      {
        right. 
        exact step_dst_valid.
      }
      apply H2 in H_or.
      tauto.
    + specialize (union_src2 x0).
      sets_unfold in union_src2.
      apply union_src2 in step_evalid.
      rewrite <- step_evalid in step_src.
      tauto.
    + specialize (union_dst2 x0).
      sets_unfold in union_dst2.
      apply union_dst2 in step_evalid.
      rewrite <- step_evalid in step_dst.
      tauto.
  - destruct H.
    specialize (union_symbol4 x0).
    sets_unfold in union_symbol4.
    apply union_symbol4 in step_evalid.
    rewrite <- step_evalid in H0.
    tauto.
Qed.

(* 类似c_step_add_graph_preserves1，
  如果图 g0 中存在从状态 x 到状态 y 的字符 c 转移，
  那么在通过 G_add_graph 合并 g0 和 g 后得到的图 g1 中，
  也会存在从状态 x 到状态 y 的字符 c 转移。 *)
Lemma c_step_add_graph_preserves2 :
forall {T} (g0 g: pg_nfa T) g1 x y (s: state) (c: T),
  (s,g1,s) ∈ (G_add_graph g0 g).(nrm) -> 
  c_step g0 c x y ->
  c_step g1 c x y.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  destruct H.
  destruct H.
  destruct union_pg0.
  unfold c_step in H0.
  destruct H0.
  destruct H.
  destruct H.
  unfold c_step.
  exists x0.
  exists x1.
  split.
  - destruct H.
    split.
    + unfold Sets_disjoint_union in union_edge.
      destruct union_edge.
      sets_unfold in H2.
      specialize (H2 x0).
      destruct H2.
      assert (H_or : (g0.(pg)).(evalid) x0 \/ (g.(pg)).(evalid) x0).
      {
        left.
        exact step_evalid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 x).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) x \/ (g.(pg)).(vvalid) x).
      {
        left. 
        exact step_src_valid.
      }
      apply H2 in H_or.
      tauto.
    + unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H2.
      specialize (H2 y).
      destruct H2.
      assert (H_or : (g0.(pg)).(vvalid) y \/ (g.(pg)).(vvalid) y).
      {
        left. 
        exact step_dst_valid.
      }
      apply H2 in H_or.
      tauto.
    + specialize (union_src1 x0).
      sets_unfold in union_src1.
      apply union_src1 in step_evalid.
      rewrite <- step_evalid in step_src.
      tauto.
    + specialize (union_dst1 x0).
      sets_unfold in union_dst1.
      apply union_dst1 in step_evalid.
      rewrite <- step_evalid in step_dst.
      tauto.
  - destruct H.
    specialize (union_symbol3 x0).
    sets_unfold in union_symbol3.
    apply union_symbol3 in step_evalid.
    rewrite <- step_evalid in H0.
    tauto.
Qed.

(* 通过G_add_edge加epsilon边获得的新图能够在加的epsilon边上走e_step *)
Lemma add_edge_e_step :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2: Z),
  v1 ∈ (x1.(pg)).(vvalid) -> v2 ∈ (x1.(pg)).(vvalid) ->
  (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 epsilon).(nrm) ->
  e_step x v1 v2.
Proof.
  intros.
  unfold StateRelMonad.nrm in H.
  sets_unfold in H.
  simpl in H.
  destruct H1.
  destruct H1.
  unfold e_step.
  exists e.
  split.
  + destruct add_edge_pg0.
    split.
    unfold Sets_disjoint_union in add_edge_edge.
    sets_unfold in add_edge_edge.
    destruct add_edge_edge.
    pose proof H3 e.
    destruct H4.
    assert (e = e).
    reflexivity.
    tauto.
    sets_unfold in add_edge_vertex.
    pose proof add_edge_vertex v1.
    destruct H1.
    pose proof H1 H.
    tauto.
    sets_unfold in add_edge_vertex.
    pose proof add_edge_vertex v2.
    destruct H1.
    pose proof H1 H0.
    tauto.
    apply add_edge_src_new.
    apply add_edge_dst_new.
  + unfold epsilon in add_edge_symbol_new0.
    tauto.
Qed. 

(* 在通过 regexToNFA 生成的 NFA 中，其起始顶点和结束顶点都是有效的图中顶点。 *)
(* 在通过 regexToNFA 生成的 NFA 中，其起始顶点和结束顶点都是有效的图中顶点。 *)
Lemma start_end_in_graph :
  forall {T: Type} (x: elem T) (s1 s2: state) (r: reg_exp T),
  (s1, x, s2) ∈ (regexToNFA r).(nrm) ->
    (((x.(graph)).(pg)).(vvalid) x.(startVertex)) /\ (((x.(graph)).(pg)).(vvalid) x.(endVertex)).
Proof.
  intros.
  revert s2 H.
  revert x.
  revert s1.
  induction r.
  + intros.
    unfold regexToNFA in H.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    (* 出现了 (x5, x, s2) ∈ (ret_nfa x0 x2 x4).(nrm) *)
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    assert (x_start: x.(startVertex)=x0). {
      rewrite H3.
      tauto.
    }
    assert (x_end: x.(endVertex)=x2). {
      rewrite H3.
      tauto.
    }
    assert (x_graph: x.(graph)=x4). {
      rewrite H3.
      tauto.
    }
    clear H3.
    (* 要分别证明 x0 ∈ x4 且 x2 ∈ x4 *)
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    (* 要分别证明 x0 ∈ x4 且 x2 ∈ x4 *)
    pose proof after_G_add_edge x8 x12 x11 x13 x10 x0 x2 None H6 as [x11_x13 [in_x12_in_x8 _]].
    pose proof after_G_add_vertex x6 x8 x7 x9 x2 H3 as [x7_x9 [in_x8_in_x6 _]].
    pose proof after_G_add_vertex empty_nfa x6 x3 x7 x0 H2 as [x3_x7 [in_x6_is_x0 _]].
    rewrite x_graph.
    rewrite H7.
    split.
    - rewrite x_start.
      pose proof in_x12_in_x8 x0 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof in_x8_in_x6 x0 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      right.
      pose proof in_x6_is_x0 x0 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      tauto.
    - rewrite x_end.
      pose proof in_x12_in_x8 x2 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof in_x8_in_x6 x2 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      tauto.
  + intros.
    unfold regexToNFA in H.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    unfold StateRelMonad.nrm in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    (* 出现了 (x5, x, s2) ∈ (ret_nfa x0 x2 x4).(nrm) *)
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    assert (x_start: x.(startVertex)=x0). {
      rewrite H3.
      tauto.
    }
    assert (x_end: x.(endVertex)=x2). {
      rewrite H3.
      tauto.
    }
    assert (x_graph: x.(graph)=x4). {
      rewrite H3.
      tauto.
    }
    clear H3.
    (* 要分别证明 x0 ∈ x4 且 x2 ∈ x4 *)
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    (* 要分别证明 x0 ∈ x4 且 x2 ∈ x4 *)
    pose proof after_G_add_edge x8 x12 x11 x13 x10 x0 x2 (Some t) H6 as [x11_x13 [in_x12_in_x8 _]].
    pose proof after_G_add_vertex x6 x8 x7 x9 x2 H3 as [x7_x9 [in_x8_in_x6 _]].
    pose proof after_G_add_vertex empty_nfa x6 x3 x7 x0 H2 as [x3_x7 [in_x6_is_x0 _]].
    rewrite x_graph.
    rewrite H7.
    split.
    - rewrite x_start.
      pose proof in_x12_in_x8 x0 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof in_x8_in_x6 x0 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      right.
      pose proof in_x6_is_x0 x0 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      tauto.
    - rewrite x_end.
      pose proof in_x12_in_x8 x2 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof in_x8_in_x6 x2 as temp.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      tauto.
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1; clear union_symbol3 union_symbol4.
    destruct union_pg0; clear union_edge union_src1 union_dst1 union_src2 union_dst2.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex as [? inx6_isx0].
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7 as [x4_x12 x13_x5].
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    assert (x_start: x.(startVertex)=x0.(startVertex)). {
      rewrite H2.
      tauto.
    }
    assert (x_end: x.(endVertex)=x2.(endVertex)). {
      rewrite H2.
      tauto.
    }
    assert (x_graph: x.(graph)=x4). {
      rewrite H2.
      tauto.
    }
    clear H2.
    (* 先产生递推式 *)
    pose proof IHr1 s1 x0 x1 H as regex1; clear IHr1.
    pose proof IHr2 x1 x2 x3 H0 as regex2; clear IHr2.
    (* 重写 起点/终点/图 *)
    rewrite x_start.
    rewrite x_end.
    rewrite x_graph.
    rewrite x4_x12.
    pose proof after_G_add_edge x8 x12 x11 x13 x10 x0.(endVertex) x2.(startVertex) None H6 as [x11_x13 [in_x12_in_x8 _]].
    unfold StateRelMonad.nrm in H3.
    destruct H3 as [? x7_x9].
    destruct H2; clear union_symbol3 union_symbol4.
    destruct union_pg0; clear union_edge union_src1 union_dst1 union_src2 union_dst2.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex as [? inx8_inx6_inx2].
    pose proof after_get_new_edge x9 x11 x10 H5 as [_ x9_x11].
    split.
    - pose proof in_x12_in_x8 x0.(startVertex) as temp; clear in_x12_in_x8.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx8_inx6_inx2 x0.(startVertex) as temp.
      destruct temp as [temp _].
      apply temp; clear temp.
      left.
      pose proof inx6_isx0 x0.(startVertex) as temp.
      destruct temp as [temp _].
      apply temp; clear temp.
      right.
      tauto.
    - pose proof in_x12_in_x8 x2.(endVertex) as temp; clear in_x12_in_x8.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx8_inx6_inx2 x2.(endVertex) as temp.
      destruct temp as [temp _].
      apply temp; clear temp.
      right.
      tauto.
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.nrm in H8.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.nrm in H9.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.nrm in H10.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.nrm in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    unfold StateRelMonad.nrm in H12.
    destruct H12.
    destruct H12.
    destruct H12.
    unfold StateRelMonad.nrm in H13.
    destruct H13.
    destruct H13.
    destruct H13.
    unfold StateRelMonad.nrm in H14.
    destruct H14.
    destruct H14.
    destruct H14.
    unfold StateRelMonad.nrm in H15.
    destruct H15.
    destruct H15.
    destruct H15.
    unfold StateRelMonad.nrm in H16.
    destruct H16 as [x8_x32 x33_x9].
    unfold StateRelMonad.nrm in H4.
    destruct H4 as [? x9_s2].
    (* 转化要证明的点和图 *)
    assert (x_start: x.(startVertex)=x4). {
      rewrite H4.
      tauto.
    }
    assert (x_end: x.(endVertex)=x6). {
      rewrite H4.
      tauto.
    }
    assert (x_graph: x.(graph)=x8). {
      rewrite H4.
      tauto.
    }
    clear H4.
    (* 先产生递推式 *)
    pose proof IHr1 s1 x0 x1 H as regex1; clear IHr1.
    pose proof IHr2 x1 x2 x3 H0 as regex2; clear IHr2.
    (* 重写 起点/终点/图 *)
    rewrite x_start.
    rewrite x_end.
    rewrite x_graph.
    rewrite x8_x32.
    pose proof after_G_add_edge x28 x32 x31 x33 x30 x2.(endVertex) x6 None H15 as [x31_x33 [inx32_inx28 _]].
    pose proof after_G_add_edge x24 x28 x27 x29 x26 x0.(endVertex) x6 None H13 as [x27_x29 [inx28_inx24 _]].
    pose proof after_G_add_edge x20 x24 x23 x25 x22 x4 x2.(startVertex) None H11 as [x23_x25 [inx24_inx20 _]].
    pose proof after_G_add_edge x16 x20 x19 x21 x18 x4 x0.(startVertex) None H9 as [x19_x21 [inx20_inx16 _]].
    pose proof after_G_add_vertex x14 x16 x15 x17 x6 H7 as [x15_x17 [inx16_inx14 _]].
    pose proof after_G_add_vertex x12 x14 x13 x15 x4 H6 as [x11_x13 [inx14_inx12 _]].
    unfold StateRelMonad.nrm in H5.
    destruct H5 as [? _].
    destruct H4; clear union_symbol3 union_symbol4.
    destruct union_pg0; clear union_edge union_src1 union_dst1 union_src2 union_dst2.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex as [? inx12_inx10_inx2].
    unfold StateRelMonad.nrm in H3.
    destruct H3 as [? x7_x11].
    destruct H3; clear union_symbol3 union_symbol4.
    destruct union_pg0; clear union_edge union_src1 union_dst1 union_src2 union_dst2.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex as [? inx10_inx0].
    split.
    - pose proof inx32_inx28 x4 as temp; clear inx32_inx28.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx28_inx24 x4 as temp; clear inx28_inx24.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx24_inx20 x4 as temp; clear inx24_inx20.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx20_inx16 x4 as temp; clear inx20_inx16.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx16_inx14 x4 as temp; clear inx16_inx14.
      destruct temp as [_ temp].
      apply temp; clear temp.
      right.
      pose proof inx14_inx12 x4 as temp; clear inx14_inx12.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      tauto.
    - pose proof inx32_inx28 x6 as temp; clear inx32_inx28.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx28_inx24 x6 as temp; clear inx28_inx24.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx24_inx20 x6 as temp; clear inx24_inx20.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx20_inx16 x6 as temp; clear inx20_inx16.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx16_inx14 x6 as temp; clear inx16_inx14.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      reflexivity.
  + intros.
    unfold StateRelMonad.nrm in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.
    destruct H0.
    unfold StateRelMonad.nrm in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H3.
    destruct H3.
    unfold StateRelMonad.nrm in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    unfold StateRelMonad.nrm in H5.
    destruct H5.
    destruct H5.
    destruct H5.
    unfold StateRelMonad.nrm in H6.
    destruct H6.
    destruct H6.
    destruct H6.
    unfold StateRelMonad.nrm in H7.
    destruct H7.
    destruct H7.
    destruct H7.
    unfold StateRelMonad.nrm in H8.
    destruct H8.
    destruct H8.
    destruct H8.
    unfold StateRelMonad.nrm in H9.
    destruct H9.
    destruct H9.
    destruct H9.
    unfold StateRelMonad.nrm in H10.
    destruct H10.
    destruct H10.
    destruct H10.
    unfold StateRelMonad.nrm in H11.
    destruct H11.
    destruct H11.
    destruct H11.
    unfold StateRelMonad.nrm in H12.
    destruct H12.
    destruct H12.
    destruct H12.
    unfold StateRelMonad.nrm in H13.
    destruct H13 as [x6_x24 x25_x7].
    (* 转化要证明的点和图 *)
    assert (x_start: x.(startVertex)=x2). {
      rewrite H3.
      tauto.
    }
    assert (x_end: x.(endVertex)=x4). {
      rewrite H3.
      tauto.
    }
    assert (x_graph: x.(graph)=x6). {
      rewrite H3.
      tauto.
    }
    clear H3.
    (* 先产生递推式 *)
    pose proof IHr s1 x0 x1 H as regexr; clear IHr.
    (* 重写 起点/终点/图 *)
    rewrite x_start.
    rewrite x_end.
    rewrite x_graph.
    rewrite x6_x24.
    pose proof after_G_add_edge x20 x24 x23 x25 x22 x0.(endVertex) x0.(startVertex) None H12 as [x23_x25 [inx24_inx20 _]].
    pose proof after_G_add_edge x16 x20 x19 x21 x18 x0.(endVertex) x4 None H10 as [x19_x21 [inx20_inx16 _]].
    pose proof after_G_add_edge x12 x16 x15 x17 x14 x2 x0.(endVertex) None H8 as [x15_x17 [inx16_inx12 _]].
    pose proof after_G_add_vertex x10 x12 x11 x13 x4 H6 as [x11_x13 [inx12_inx10 _]].
    pose proof after_G_add_vertex x8 x10 x9 x11 x2 H5 as [x9_x11 [inx10_inx8 _]].
    unfold StateRelMonad.nrm in H2.
    destruct H2 as [? x5_x9].
    destruct H2; clear union_symbol3 union_symbol4.
    destruct union_pg0; clear union_edge union_src1 union_dst1 union_src2 union_dst2.
    unfold Sets_disjoint_union in union_vertex.
    sets_unfold in union_vertex.
    destruct union_vertex as [? inx8_inx0].
    split.
    - pose proof inx24_inx20 x2 as temp; clear inx24_inx20.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx20_inx16 x2 as temp; clear inx20_inx16.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx16_inx12 x2 as temp; clear inx16_inx12.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx12_inx10 x2 as temp; clear inx12_inx10.
      destruct temp as [_ temp].
      apply temp; clear temp.
      right.
      pose proof inx10_inx8 x2 as temp; clear inx10_inx8.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      tauto.
    - pose proof inx24_inx20 x4 as temp; clear inx24_inx20.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx20_inx16 x4 as temp; clear inx20_inx16.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx16_inx12 x4 as temp; clear inx16_inx12.
      destruct temp as [_ temp].
      apply temp; clear temp.
      pose proof inx12_inx10 x4 as temp; clear inx12_inx10.
      destruct temp as [_ temp].
      apply temp; clear temp.
      left.
      reflexivity.
Qed.


(* 加边后原有的e_step仍然成立 *)
Lemma add_edge_preserve_e_step :
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2 u1 u2: Z),
  e_step x1 u1 u2 ->
  (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 epsilon).(nrm) ->
  e_step x u1 u2.
Proof.
  intros.
  unfold e_step in H.
  destruct H.
  destruct H.
  destruct H.
  unfold e_step.
  exists x0.
  split.
  split.
  pose proof add_edge_edge_equal s1 s2 x x1 e v1 v2 epsilon H0 x0.
  tauto.
  pose proof add_edge_in_graph s1 s2 x x1 e v1 v2 epsilon H0 u1.
  tauto.
  pose proof add_edge_in_graph s1 s2 x x1 e v1 v2 epsilon H0 u2.
  tauto.
  destruct H0.
  destruct H.
  destruct add_edge_pg0.
  pose proof add_edge_src_old x0 step_evalid.
  rewrite H.
  tauto.
  destruct H0.
  destruct H.
  destruct add_edge_pg0.
  pose proof add_edge_dst_old x0 step_evalid.
  rewrite H.
  tauto.
  destruct H0.
  destruct H.
  pose proof add_edge_symbol_old0 x0 step_evalid.
  rewrite H.
  tauto.
Qed.

(* 将一步e_step和string_step合并 *)
Lemma e_step_extend_string_step1:
    forall {T: Type} (x: pg_nfa T) (v1 v2 v3: Z) (str: list T),
      e_step x v1 v2 ->
      string_step x str v2 v3 ->
      string_step x str v1 v3.
Proof.
  intros.
  revert H0.
  revert v3.
  induction str.
  + intros.
    unfold string_step in H0.
    unfold e_steps in H0.
    unfold clos_refl_trans in H0.
    unfold Sets.indexed_union in H0.
    simpl in H0.
    destruct H0.
    unfold string_step.
    unfold e_steps.
    unfold clos_refl_trans.
    unfold Sets.indexed_union.
    simpl.
    exists (S x0).
    simpl.
    sets_unfold.
    exists v2.
    split.
    apply H.
    apply H0.
  + intros.
    unfold string_step in H0.
    sets_unfold in H0.
    destruct H0.
    destruct H0.
    unfold string_step.
    sets_unfold.
    exists x0.
    split.
    2:{
      apply H1.
    }
    unfold string_step in IHstr.
    pose proof IHstr x0.
    sets_unfold in H2.
    pose proof H2 H0.
    tauto.
Qed.

(* 将一步e_step和string_step合并 *)
Lemma e_step_extend_string_step2:
    forall {T: Type} (x: pg_nfa T) (v1 v2 v3: Z) (str: list T),
      e_step x v2 v3 ->
      string_step x str v1 v2 ->
      string_step x str v1 v3.
Proof.
  intros.
  destruct str.
  2:{
    unfold string_step in H0.
    destruct H0.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    unfold string_step.
    sets_unfold.
    exists x0.
    split.
    apply H0.
    unfold char_step in H1.
    sets_unfold in H1.
    destruct H1.
    destruct H1.
    unfold char_step.
    sets_unfold.
    exists x1.
    split.
    apply H1.
    unfold e_steps in H2.
    unfold clos_refl_trans in H2.
    unfold Sets.indexed_union in H2.
    simpl in H2.
    destruct H2.
    unfold e_steps.
    unfold clos_refl_trans.
    unfold Sets.indexed_union.
    simpl.
    clear H1.
    revert x1 H2.
    induction x2.
    2:{
      intros.
      simpl in H2.
      sets_unfold in H2.
      destruct H2.
      destruct H1.
      apply IHx2 in H2.
      destruct H2.
      exists (S x4).
      simpl.
      sets_unfold.
      exists x3.
      split.
      - tauto.
      - tauto.
    }
    intros.
    simpl in H2.
    unfold Rels.id in H2.
    simpl in H2.
    exists Nat.one.
    simpl.
    sets_unfold.
    exists v3.
    split.
    rewrite H2.
    tauto.
    tauto.
  }
  simpl in H0.
  simpl.
  unfold e_steps in H0.
  unfold e_steps.
  unfold clos_refl_trans in H0.
  unfold clos_refl_trans.
  sets_unfold in H0.
  sets_unfold.
  destruct H0.
  revert v1 H0.
  induction x0.
  2:{
    intros.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    destruct H0.
    apply IHx0 in H1.
    destruct H1.
    exists (S x2).
    simpl.
    sets_unfold.
    exists x1.
    split.
    - tauto.
    - tauto.
  }
  intros.
  exists Nat.one.
  simpl.
  sets_unfold.
  exists v3.
  split.
  - simpl in H0.
    unfold Rels.id in H0.
    simpl in H0.
    rewrite H0.
    tauto.
  - tauto.
Qed.

(* 给定一个图 x1，我们向 x1 中添加一条空边（即标签为 epsilon 的边），并通过 G_add_edge 构造了新的图 x。
  在新的图 x 中，如果从顶点 v2 到顶点 v3 可以通过某个字符串 str 实现转换，那么从 v1 到 v3 也可以通过相同的字符串 str 进行转换。 *)
Lemma add_empty_edge_extend_string_step1:
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2 v3: Z) (str: list T),
  v1 ∈ (x1.(pg)).(vvalid) -> v2 ∈ (x1.(pg)).(vvalid) ->
  (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 epsilon).(nrm) ->
  string_step x str v2 v3 ->
  string_step x str v1 v3.
Proof.
  intros.
  pose proof add_edge_e_step s1 s2 x x1 e v1 v2 H H0 H1.
  pose proof e_step_extend_string_step1 x v1 v2 v3 str H3 H2.
  tauto.
Qed.

(* 向一个 NFA的图中添加一个空边，并且已经知道从某个状态 v1 到 v2 经过字符串 str 的转换有效，
  那么我们可以推导出，从 v1 到 v3 也能通过同样的字符串 str 成功转换 *)
Lemma add_empty_edge_extend_string_step2:
  forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2 v3: Z) (str: list T),
  v2 ∈ (x1.(pg)).(vvalid) -> v3 ∈ (x1.(pg)).(vvalid) ->
  (s1, x, s2) ∈ (G_add_edge x1 e v2 v3 epsilon).(nrm) ->
  string_step x str v1 v2 ->
  string_step x str v1 v3.
Proof.
  intros.
  pose proof add_edge_e_step s1 s2 x x1 e v2 v3 H H0 H1.
  pose proof e_step_extend_string_step2 x v1 v2 v3 str H3 H2.
  tauto.
Qed.

(* 在一个图中，添加一个点后，不改变原来就有的e_steps关系 *)
Lemma add_vertex_preserve_e_steps:
forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v u1 u2: Z),
  (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
  e_steps x1 u1 u2 ->
  e_steps x u1 u2.
Proof.
  intros.
  unfold e_steps in H0.
  unfold clos_refl_trans in H0.
  sets_unfold in H0.
  destruct H0.
  unfold e_steps.
  unfold clos_refl_trans.
  sets_unfold.
  exists x0.
  revert H0.
  revert u1.
  induction x0.
  2:{
    intros.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    simpl.
    sets_unfold.
    exists x2.
    split.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H.
    destruct H.
    destruct add_vertex_pg0.
    unfold e_step.
    exists x3.
    split.
    split.
    sets_unfold in add_vertex_edge.
    pose proof add_vertex_edge x3.
    tauto.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex.
    pose proof H3 u1.
    tauto.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex.
    pose proof H3 x2.
    tauto.
    pose proof add_vertex_src x3 step_evalid.
    rewrite H.
    tauto.
    pose proof add_vertex_dst x3 step_evalid.
    rewrite H.
    tauto.
    pose proof add_vertex_symbol0 x3 step_evalid.
    rewrite H.
    tauto.
    destruct H0.
    pose proof IHx0 x2 H1.
    apply H2.
  }
  simpl.
  unfold Rels.id.
  simpl.
  intros.
  lia.
Qed.

(* 类似add_graph_preserve_string_step1，
  通过操作 G_add_vertex向一个图中添加一个顶点时，在图中的字符串转换保持不变。
  具体来说，如果在原始图 x1 中，从 u1 到 u2 通过字符串 str 能够实现转换，
  那么在添加了新顶点 v 后的图 x 中，使用相同的字符串 str 也能够从 u1 到 u2 进行转换。 *)
Lemma add_vertex_preserve_string_step:
forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (v u1 u2: Z) (str: list T),
  (s1, x, s2) ∈ (G_add_vertex x1 v).(nrm) ->
  string_step x1 str u1 u2 ->
  string_step x str u1 u2.
Proof.
  intros.
  revert H0.
  revert u2.
  induction str.
  2:{
    intros.
    unfold string_step in H0.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    destruct H0.
    unfold string_step.
    simpl.
    sets_unfold.
    exists x0.
    split.
    + pose proof IHstr x0.
      unfold string_step in H2.
      sets_unfold in H2.
      pose proof H2 H0.
      apply H3.
    + destruct H1.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H3.
      destruct H1.
      destruct H2.
      unfold char_step.
      sets_unfold.
      exists x2.
      split.
      - unfold c_step.
        exists x3.
        exists x4.
        split.
        destruct H.
        destruct H.
        destruct add_vertex_pg0.
        split.
        sets_unfold in add_vertex_edge.
        pose proof add_vertex_edge x3.
        tauto.
        unfold Sets_disjoint_union in add_vertex_vertex.
        sets_unfold in add_vertex_vertex.
        destruct add_vertex_vertex.
        pose proof H5 x0.
        tauto.
        unfold Sets_disjoint_union in add_vertex_vertex.
        sets_unfold in add_vertex_vertex.
        destruct add_vertex_vertex.
        pose proof H5 x2.
        tauto.
        pose proof add_vertex_src x3 step_evalid.
        rewrite H.
        tauto.
        pose proof add_vertex_dst x3 step_evalid.
        rewrite H.
        tauto.
        split.
        destruct H.
        destruct H.
        pose proof add_vertex_symbol0 x3 step_evalid.
        rewrite H.
        tauto.
        tauto.
      - unfold e_steps.
        unfold clos_refl_trans.
        sets_unfold.
        pose proof add_vertex_preserve_e_steps s1 s2 x x1 v x2 u2 H.
        unfold e_steps in H2.
        unfold clos_refl_trans in H2.
        sets_unfold in H2.
        apply H2.
        exists x5.
        apply H1.  
  }
  intros.
  unfold string_step.
  unfold e_steps.
  unfold clos_refl_trans.
  sets_unfold.
  unfold string_step in H0.
  unfold e_steps in H0.
  unfold clos_refl_trans in H0.
  sets_unfold in H0.
  destruct H0.
  exists x0.
  revert H0.
  revert u1.
  induction x0.
  2:{
    intros.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    destruct H0.
    simpl.
    sets_unfold.
    exists x2.
    split.
    2:{
      pose proof IHx0 x2 H1.
      apply H2.
    }
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H.
    destruct H.
    destruct add_vertex_pg0.
    unfold e_step.
    exists x3.
    split.
    split.
    sets_unfold in add_vertex_edge.
    pose proof add_vertex_edge x3.
    tauto.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex.
    pose proof H3 u1.
    tauto.
    unfold Sets_disjoint_union in add_vertex_vertex.
    sets_unfold in add_vertex_vertex.
    destruct add_vertex_vertex.
    pose proof H3 x2.
    tauto.
    pose proof add_vertex_src x3 step_evalid.
    rewrite H.
    tauto.
    pose proof add_vertex_dst x3 step_evalid.
    rewrite H.
    tauto.
    pose proof add_vertex_symbol0 x3 step_evalid.
    rewrite H.
    tauto.
  }
  simpl.
  unfold Rels.id.
  simpl.
  intros.
  lia.
Qed.

(* 如果从状态 u1 到状态 u2 可以通过字符串 str 在原图 x1 中实现，
那么同样的转换在修改后的图 x 中也可以通过相同的字符串 str 实现。 *)
Lemma add_edge_preserve_string_step:
forall {T: Type} (s1 s2: state) (x x1: pg_nfa T) (e v1 v2 u1 u2: Z) t (str: list T),
  (s1, x, s2) ∈ (G_add_edge x1 e v1 v2 t).(nrm) ->
  string_step x1 str u1 u2 ->
  string_step x str u1 u2.
Admitted.

(* 当我们向图中通过 G_add_graph 操作合并两个子图时，合并后的图中的字符串转换不受影响。
  具体来说，如果在图 x1 中，从状态 v1 到状态 v2 可以通过字符串 str 实现转换，
  那么在合并后的图 x 中，使用相同的字符串 str 也能从 v1 到 v2 转换。 *)
Lemma add_graph_preserve_string_step1:
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T) (v1 v2: Z) (str: list T),
  (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
  string_step x1 str v1 v2 ->
  string_step x str v1 v2.
Admitted.

(* 类似add_graph_preserve_string_step1引理，
  但是条件换成如果在图 x2 中，从状态 v1 到状态 v2 可以通过字符串 str 实现转换，
  那么在合并后的图 x 中，使用相同的字符串 str 也能从 v1 到 v2 转换。 *)
Lemma add_graph_preserve_string_step2:
  forall {T: Type} (s1 s2: state) (x x1 x2: pg_nfa T) (v1 v2: Z) (str: list T),
  (s1, x, s2) ∈ (G_add_graph x1 x2).(nrm) ->
  string_step x2 str v1 v2 ->
  string_step x str v1 v2.
Admitted.


(*********************************************************)
(**                                                      *)
(** Union                                                *)
(**                                                      *)
(*********************************************************)

(* 正则表达式匹配到nfa匹配 *)
Theorem union_hoare_backward {T: Type}:
  forall (s: state) (r1 r2: reg_exp T) (str: list T),
  (forall (s0: state),
  Hoare 
    (fun s1 : state => s1 = s0) 
    (regexToNFA r1)
    (fun (e : elem T) (_ : state) =>
      exp_match r1 str ->
      match_str e.(graph) e.(startVertex) e.(endVertex) str)) ->
  (forall (s0: state),
  Hoare 
    (fun s1 : state => s1 = s0) 
    (regexToNFA r2)
    (fun (e : elem T) (_ : state) =>
      exp_match r2 str ->
      match_str e.(graph) e.(startVertex) e.(endVertex) str)) ->

  Hoare
    (fun s1 => s1 = s)
    (regexToNFA (Union_r r1 r2))
    (fun(e : elem T) (s2 : state) =>
    exp_match (Union_r r1 r2) str -> match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  split.
  + intros.
    unfold not.
    intros.
    pose proof derive_false T (Union_r r1 r2) s1 H2.
    tauto.
  + intros.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H6.
    destruct H6.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    destruct H10.
    destruct H10.
    destruct H11.
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H13.
    destruct H14.
    destruct H14.
    destruct H14.
    destruct H15.
    destruct H15.
    destruct H15.
    destruct H16.
    destruct H16.
    destruct H16.
    destruct H17.
    destruct H17.
    destruct H17.
    destruct H18.
    destruct H18.
    destruct H18.
    destruct H19.
    destruct H19.
    destruct H19.
    destruct H20.
    destruct H8.
    rewrite H8.
    simpl.
    pose proof H s1.
    pose proof H0 x0.
    unfold Hoare in H23, H24.
    destruct H23.
    destruct H24.
    pose proof H25 s1 x x0.
    assert (s1 = s1).
    reflexivity.
    pose proof H27 H28 H2.
    pose proof H26 x0 x1 x2.
    assert (x0 = x0).
    reflexivity.
    pose proof H30 H31 H4.
    destruct H3.
    - pose proof H29 H3.
      unfold match_str.
      clear H32 H31 H30 H29 H28 H27 H26 H24 H25 H23 H8 H H0.
      unfold match_str in H33.
      pose proof add_vertex_in_graph x12 x14 x13 x11 x3 H10 x3.
      destruct H.
      assert (x3 = x3).
      reflexivity.
      assert ((x13.(pg)).(vvalid) x3).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x3.
      destruct H24.
      assert ((x15.(pg)).(vvalid) x3).
      tauto.
      pose proof start_end_in_graph x s1 x0 r1 H2.
      destruct H27.
      pose proof add_graph_num_vertex1 x6 x10 x9 empty_nfa x.(graph) H7 x.(startVertex).
      assert ((x9.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_graph_num_vertex1 x10 x12 x11 x9 x1.(graph) H9 x.(startVertex).
      assert ((x11.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_vertex_in_graph x12 x14 x13 x11 x3 H10 x.(startVertex).
      destruct H34.
      assert ((x13.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x.(startVertex).
      destruct H37.
      assert ((x15.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_graph_preserve_string_step2 x6 x10 x9 empty_nfa x.(graph) x.(startVertex) x.(endVertex) str H7 H33.
      pose proof add_graph_preserve_string_step1 x10 x12 x11 x9 x1.(graph) x.(startVertex) x.(endVertex) str H9 H40.
      pose proof add_vertex_preserve_string_step x12 x14 x13 x11 x3 x.(startVertex) x.(endVertex) str H10 H41.
      pose proof add_vertex_preserve_string_step x14 x16 x15 x13 x5 x.(startVertex) x.(endVertex) str H11 H42.
      pose proof add_edge_preserve_string_step x18 x20 x19 x15 x17 x3 x.(startVertex) x.(startVertex) x.(endVertex) epsilon str H13 H43.
      pose proof add_empty_edge_extend_string_step1 x18 x20 x19 x15 x17 x3 x.(startVertex) x.(endVertex) str H26 H39 H13 H44.
      pose proof add_edge_preserve_string_step x22 x24 x23 x19 x21 x3 x1.(startVertex) x3 x.(endVertex) epsilon str H15 H45.
      pose proof add_edge_preserve_string_step x26 x28 x27 x23 x25 x.(endVertex) x5 x3 x.(endVertex) epsilon str H17 H46.
      pose proof add_graph_num_vertex1 x6 x10 x9 empty_nfa x.(graph) H7 x.(endVertex).
      assert ((x9.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_graph_num_vertex1 x10 x12 x11 x9 x1.(graph) H9 x.(endVertex).
      assert ((x11.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x12 x14 x13 x11 x3 H10 x.(endVertex).
      assert ((x13.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x.(endVertex).
      assert ((x15.(pg)).(vvalid) x.(endVertex)).
      tauto.
      clear H54 H52 H50 H48 H38 H37 H36 H35 H34 H31 H29 H25 H24.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x3 x.(startVertex) epsilon H13 x.(endVertex).
      assert ((x19.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_edge_in_graph x22 x24 x23 x19 x21 x3 x1.(startVertex) epsilon H15 x.(endVertex).
      assert ((x23.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x5.
      assert ((x15.(pg)).(vvalid) x5).
      tauto.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x3 x.(startVertex) epsilon H13 x5.
      assert ((x19.(pg)).(vvalid) x5).
      tauto.
      pose proof add_edge_in_graph x22 x24 x23 x19 x21 x3 x1.(startVertex) epsilon H15 x5.
      assert ((x23.(pg)).(vvalid) x5).
      tauto.
      clear H H0 H24 H29 H34 H36 H38.
      pose proof add_empty_edge_extend_string_step2 x26 x28 x27 x23 x25 x3 x.(endVertex) x5 str H31 H48 H17 H47.
      pose proof add_edge_preserve_string_step x30 x32 x31 x27 x29 x1.(endVertex) x5 x3 x5 epsilon str H19 H.
      rewrite H20.
      tauto.
    - pose proof H32 H3.
      unfold match_str.
      clear H32 H31 H30 H29 H28 H27 H26 H24 H25 H23 H8 H H0.
      unfold match_str in H33.
      pose proof add_vertex_in_graph x12 x14 x13 x11 x3 H10 x3.
      destruct H.
      assert (x3 = x3).
      reflexivity.
      assert ((x13.(pg)).(vvalid) x3).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x3.
      destruct H24.
      assert ((x15.(pg)).(vvalid) x3).
      tauto.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x3 x.(startVertex) epsilon H13 x3.
      assert ((x19.(pg)).(vvalid) x3).
      tauto.
      pose proof start_end_in_graph x1 x0 x2 r2 H4.
      destruct H29.
      pose proof add_graph_num_vertex1 x10 x12 x11 x9 x1.(graph) H9 x1.(startVertex).
      assert ((x11.(pg)).(vvalid) x1.(startVertex)).
      tauto.
      pose proof add_vertex_in_graph x12 x14 x13 x11 x3 H10 x1.(startVertex).
      assert ((x13.(pg)).(vvalid) x1.(startVertex)).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x1.(startVertex).
      assert ((x15.(pg)).(vvalid) x1.(startVertex)).
      tauto.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x3 x.(startVertex) epsilon H13 x1.(startVertex).
      assert ((x19.(pg)).(vvalid) x1.(startVertex)).
      tauto.
      pose proof add_graph_preserve_string_step2 x10 x12 x11 x9 x1.(graph) x1.(startVertex) x1.(endVertex) str H9 H33.
      pose proof add_vertex_preserve_string_step x12 x14 x13 x11 x3 x1.(startVertex) x1.(endVertex) str H10 H40.
      pose proof add_vertex_preserve_string_step x14 x16 x15 x13 x5 x1.(startVertex) x1.(endVertex) str H11 H41.
      pose proof add_edge_preserve_string_step x18 x20 x19 x15 x17 x3 x.(startVertex) x1.(startVertex) x1.(endVertex) epsilon str H13 H42.
      pose proof add_edge_preserve_string_step x22 x24 x23 x19 x21 x3 x1.(startVertex) x1.(startVertex) x1.(endVertex) epsilon str H15 H43.
      pose proof add_empty_edge_extend_string_step1 x22 x24 x23 x19 x21 x3 x1.(startVertex) x1.(endVertex) str H28 H39 H15 H44.
      pose proof add_edge_preserve_string_step x26 x28 x27 x23 x25 x.(endVertex) x5 x3 x1.(endVertex) epsilon str H17 H45.
      pose proof add_edge_preserve_string_step x30 x32 x31 x27 x29 x1.(endVertex) x5 x3 x1.(endVertex) epsilon str H19 H46.
      pose proof add_graph_num_vertex1 x10 x12 x11 x9 x1.(graph) H9 x1.(endVertex).
      assert ((x11.(pg)).(vvalid) x1.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x12 x14 x13 x11 x3 H10 x1.(endVertex).
      assert ((x13.(pg)).(vvalid) x1.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x1.(endVertex).
      assert ((x15.(pg)).(vvalid) x1.(endVertex)).
      tauto.
      clear H52 H50 H48 H38 H37 H36 H35 H34 H31 H27 H25 H24.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x3 x.(startVertex) epsilon H13 x1.(endVertex).
      assert ((x19.(pg)).(vvalid) x1.(endVertex)).
      tauto.
      pose proof add_edge_in_graph x22 x24 x23 x19 x21 x3 x1.(startVertex) epsilon H15 x1.(endVertex).
      assert ((x23.(pg)).(vvalid) x1.(endVertex)).
      tauto.
      pose proof add_edge_in_graph x26 x28 x27 x23 x25 x.(endVertex) x5 epsilon H17 x1.(endVertex).
      assert ((x27.(pg)).(vvalid) x1.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x14 x16 x15 x13 x5 H11 x5.
      assert ((x15.(pg)).(vvalid) x5).
      tauto.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x3 x.(startVertex) epsilon H13 x5.
      assert ((x19.(pg)).(vvalid) x5).
      tauto.
      pose proof add_edge_in_graph x22 x24 x23 x19 x21 x3 x1.(startVertex) epsilon H15 x5.
      assert ((x23.(pg)).(vvalid) x5).
      tauto.
      pose proof add_edge_in_graph x26 x28 x27 x23 x25 x.(endVertex) x5 epsilon H17 x5.
      assert ((x27.(pg)).(vvalid) x5).
      tauto.
      clear H54 H50 H38 H36 H34 H27 H24 H H0.
      pose proof add_empty_edge_extend_string_step2 x30 x32 x31 x27 x29 x3 x1.(endVertex) x5 str H35 H55 H19 H47.
      rewrite H20.
      tauto.
Qed.

(* act_union A B 合成的 NFA 中，某个元素 a 不能同时涉及跨越 A 和 B 之间的转换 *)
Lemma act_union_non_vrel {T: Type}:
forall (A B a: elem T) (s1 s2: state),
  (s1, a, s2) ∈ (act_union A B).(nrm) ->
    (~e_steps a.(graph) A.(startVertex) B.(endVertex) /\
    ~e_steps a.(graph) B.(startVertex) A.(endVertex)).
Admitted.

(* 如果在图 G 中，从 x 到 y 没有任何边 (~e_steps G x y)，
  那么不可能存在一个字符串 l 能够让 x 到 y 通过 string_step 成功转换。 *)
Lemma no_e_infer_no_string {T: Type}:
  forall (l: list T) (G: pg_nfa T) (x y: Z),
    ~e_steps G x y -> 
    ~string_step G l x y.
Admitted.

(* 如果从状态 s1 到 s2 存在一个有效转移 e，并且字符串 l 能够匹配这个转移，
那么可以得出下面几个结论有一个成立：
  1. l 可以通过 A 中的某个转移来匹配
  2. l 可以通过 B 中的某个转移来匹配
  3. l 可以通过 A 的起点到 B 的终点来匹配
  4. l 可以通过 B 的起点到 A 的终点来匹配 *)
Lemma act_union_reverse_correctness_aux {T: Type}:
forall (A B e: elem T) (s1 s2: state) (l: list T),
  (s1, e, s2) ∈ (act_union A B).(nrm) ->
    match_str e.(graph) e.(startVertex) e.(endVertex) l ->
    ((match_str e.(graph) A.(startVertex) A.(endVertex) l) \/ 
    (match_str e.(graph) B.(startVertex) B.(endVertex) l) \/
    (match_str e.(graph) A.(startVertex) B.(endVertex) l) \/
    (match_str e.(graph) B.(startVertex) A.(endVertex) l)).
Admitted.
  
(* 4如果 l 能够在 act_union A B 的组合中匹配 A 的起点到终点，
  那么它同样可以在 A 的原始图中匹配。 *)
Lemma act_union_same_vertex_graph_A {T: Type}:
forall (A B e: elem T) (s1 s2: state) (l: list T),
  (s1, e, s2) ∈ (act_union A B).(nrm) ->
  match_str e.(graph) A.(startVertex) A.(endVertex) l ->
  match_str A.(graph) A.(startVertex) A.(endVertex) l.
Admitted.

(* 与 act_union_same_vertex_graph_A 类似，
  act_union_same_vertex_graph_B 证明了如果 l 可以匹配 B 中的状态转换，
  那么它也可以匹配 B 的原始图 *)
Lemma act_union_same_vertex_graph_B {T: Type}:
forall (A B e: elem T) (s1 s2: state) (l: list T),
  (s1, e, s2) ∈ (act_union A B).(nrm) ->
  match_str e.(graph) B.(startVertex) B.(endVertex) l ->
  match_str B.(graph) B.(startVertex) B.(endVertex) l.
Admitted.

(* 如果a是A和B的union且str可以string step通过l，
  那么l要么可以在A中通过string step，要么可以在B中通过string step。 *)
Lemma act_union_reverse_correctness {T: Type}:
forall (s1 s2: state) (A B: elem T) (a : elem T) (l: list T),
 (s1, a, s2) ∈ (act_union A B).(nrm) ->
 string_step a.(graph) l a.(startVertex) a.(endVertex) ->
 string_step A.(graph) l A.(startVertex) A.(endVertex) \/
 string_step B.(graph) l B.(startVertex) B.(endVertex).
Proof.
  intros.
  unfold match_str.
  pose proof act_union_reverse_correctness_aux A B a s1 s2 l H.
  unfold match_str in H1.
  pose proof H1 H0.
  pose proof act_union_non_vrel A B a s1 s2 H.
  destruct H3.
  pose proof no_e_infer_no_string l a.(graph) A.(startVertex) B.(endVertex) H3.
  pose proof no_e_infer_no_string l a.(graph) B.(startVertex) A.(endVertex) H4.
  destruct H2.
  pose proof act_union_same_vertex_graph_A A B a s1 s2 l H H2.
  tauto.
  destruct H2.
  pose proof act_union_same_vertex_graph_B A B a s1 s2 l H H2.
  tauto.
  destruct H2.
  tauto.
  tauto.
Qed.

(* nfa匹配到正则表达式匹配 *)
Theorem union_hoare_forward {T: Type}:
  forall (s: state) (r1 r2: reg_exp T) (str: list T),
  (forall (s0: state),
  Hoare 
    (fun s1 : state => s1 = s0) 
    (regexToNFA r1)
    (fun (e : elem T) (_ : state) =>
      match_str e.(graph) e.(startVertex) e.(endVertex) str ->
      exp_match r1 str)) ->
  (forall (s0: state),
  Hoare 
    (fun s1 : state => s1 = s0) 
    (regexToNFA r2)
    (fun (e : elem T) (_ : state) =>
      match_str e.(graph) e.(startVertex) e.(endVertex) str ->
      exp_match r2 str)) ->
  
  Hoare
    (fun s1 => s1 = s)
    (regexToNFA (Union_r r1 r2))
    (fun(e : elem T) (s2 : state) =>
    match_str e.(graph) e.(startVertex) e.(endVertex) str -> exp_match (Union_r r1 r2) str).
Proof.
  intros.
  unfold Hoare.
  split.
  + intros.
    unfold not.
    intros.
    pose proof derive_false T (Union_r r1 r2) s1 H2.
    tauto.
  + intros.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H6.
    destruct H6.
    destruct H6.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    destruct H10.
    destruct H10.
    destruct H11.
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H13.
    destruct H14.
    destruct H14.
    destruct H14.
    destruct H15.
    destruct H15.
    destruct H15.
    destruct H16.
    destruct H16.
    destruct H16.
    destruct H17.
    destruct H17.
    destruct H17.
    destruct H18.
    destruct H18.
    destruct H18.
    destruct H19.
    destruct H19.
    destruct H19.
    destruct H20.
    destruct H8.
    rewrite H8 in H3.
    simpl in H3.
    simpl.
    sets_unfold.
    unfold match_str in H3.
    pose proof act_union_reverse_correctness x2 s2 x x1 a str.
    assert ((x2, a, s2) ∈ (act_union x x1).(nrm)).
    simpl.
    pose proof get_new_vertex_num x2 x4 x3 H5.
    exists x3.
    exists x4.
    split.
    apply H24.
    pose proof get_new_vertex_num x4 x6 x5 H6.
    exists x5.
    exists x6.
    split.
    apply H25.
    exists x7.
    exists x8.
    split.
    exists x9.
    exists x10.
    split.
    destruct H7.
    tauto.
    exists x11.
    exists x12.
    split.
    destruct H9.
    tauto.
    exists x13.
    exists x14.
    split.
    destruct H10.
    tauto.
    exists x15.
    exists x16.
    split.
    destruct H11.
    tauto.
    exists x17.
    exists x18.
    split.
    destruct H12.
    tauto.
    exists x19.
    exists x20.
    split.
    destruct H13.
    tauto.
    exists x21.
    exists x22.
    split.
    destruct H14.
    tauto.
    exists x23.
    exists x24.
    split.
    destruct H15.
    tauto.
    exists x25.
    exists x26.
    split.
    destruct H16.
    tauto.
    exists x27.
    exists x28.
    split.
    destruct H17.
    tauto.
    exists x29.
    exists x30.
    split.
    destruct H18.
    tauto.
    exists x31.
    exists x32.
    destruct H19.
    tauto.
    tauto.
    pose proof H23 H24.
    assert (match_str a.(graph) a.(startVertex) a.(endVertex) str).
    unfold match_str.
    rewrite H8.
    simpl.
    apply H3.
    pose proof H25 H26.
    clear H23 H24 H25 H26.
    destruct H27.
    - pose proof H s1.
      unfold Hoare in H24.
      destruct H24.
      pose proof H25 s1 x x0.
      left.
      tauto.
    - pose proof H0 x0.
      unfold Hoare in H24.
      destruct H24.
      pose proof H25 x0 x1 x2.
      right.
      tauto.
Qed. 

(*********************************************************)
(**                                                      *)
(** Concat                                               *)
(**                                                      *)
(*********************************************************)


(* 如果能够通过正则表达式 r1 的 str 也能够在 r1 生成的 nfa 上 match_str *)
Definition MatchR {T} (r1 : reg_exp T) :=
  forall (str:list T) (s1 s2 s: state) (a: elem T),
  exp_match r1 str ->
  s1 = s->
  (s1, a, s2) ∈ (regexToNFA r1).(nrm) ->
  match_str a.(graph) a.(startVertex) a.(endVertex) str.

(* 如果str能够匹配一个concat得到的正则表达式，那么他一定可以写成str2和str1的连接，
  且str1可以match r1，str2可以match r2。 *)
Lemma RexMatch_ConcatR {T} :
  forall (str: list T)(r1 r2: reg_exp T),
  exp_match (Concat_r r1 r2) str ->
  exists str1 str2: list T,
  exp_match r1 str1 /\ exp_match r2 str2 /\ str = str2 ++ str1.
Proof.
  intros.
  revert str r2 H. 
  destruct r1.
  3:{
    intros.
    repeat destruct H.
    destruct H1, H0.
    exists x, x0.
    split.
    - unfold exp_match.
      unfold set_prod.
      exists x1,x2.
      split.
      + tauto.
      + tauto.
    - split.
      + tauto.
      + tauto. 
  }
  3:{
    intros.
    unfold exp_match in H.
    unfold set_prod in H.
    repeat destruct H.
    - exists x, x0.
      split.
      + unfold exp_match.
        sets_unfold.
        left;tauto.
      + split.
        tauto.
        tauto.
    - exists x,x0.
      split.
      + unfold exp_match.
        sets_unfold.
        right;tauto.
      + split.
        tauto.
        tauto.
  }
  3:{
    intros.
    unfold exp_match in H.
    unfold set_prod in H.
    destruct H.
    destruct H.
    destruct H.
    exists x,x0.
    split.
    - tauto.
    - tauto.
  }
  - intros.
    unfold exp_match in H.
    unfold set_prod in H.
    repeat destruct H.
    destruct H0.
    exists nil, x0.
    split.
    + unfold exp_match.
      sets_unfold.
      tauto.
    + split.
      * tauto.
      * tauto.
  - intros.
    unfold exp_match in H.
    unfold set_prod in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H.
    destruct H.
    exists x ,x0.
    split.
    + unfold exp_match.
      exists x1.
      tauto.
    + split.
      * tauto.
      * tauto.
Qed.

(* 这个命题描述了在图 x1 上添加一个新的边后，保持匹配字符串的能力。
  如果在图 x1 中存在一个匹配字符串的路径，并且通过图 x1 添加了一条新的边，
  那么这个路径在新图 x2 中仍然有效。 *)
Lemma add_edge_match_preserve:
  forall {T: Type}(str: list T) (x1 x2: pg_nfa T)(s1 s2:state) (e v1 v2 v3 v4:Z),
  match_str x1 v1 v2 str->
  (s1, x2, s2) ∈ (G_add_edge x1 e v3 v4 epsilon).(nrm)->
  match_str x2 v1 v2 (str).
Admitted.

(* 将两个字符串的匹配连接起来，并在经过图结构的扩展后保持匹配。 *)
Lemma match_str_graph_constr_rec:
  forall  {T :Type} (str1 str2: list T)(a : elem T) (x1 x2: pg_nfa T)(s1 s2 s3:state) (v1 v2 v3 v4 :Z),
  match_str x1 v1 v2 str1->
  match_str x1 v3 v4 str2->
  x1.(pg).(vvalid) v2 /\ x1.(pg).(vvalid) v3->
  (s1, x2, s2)
  ∈ (graph_constr_rec x1 [E v2 v3 epsilon]).(nrm)->
  match_str x2 v1 v4 (str2 ++ str1).
Proof.
  intros.
  pose proof H1 as Hh.
  clear H1.
  pose proof H2 as H1.
  clear H2.
  unfold match_str.
  unfold match_str in H, H0.
  revert v4 s1 s2 H0 H1.
  induction str2.
  2:{
    intros.
    simpl.
    sets_unfold.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    destruct H0.
    exists x.
    split.
    - specialize (IHstr2 x s1 s2).
      apply IHstr2 in H0.
      + tauto.
      + tauto.
    - unfold char_step.
      unfold char_step in H2.
      sets_unfold in H2.
      sets_unfold.
      destruct H2.
      destruct H2.
      exists x0.
      split.
      2:{
        unfold e_steps.
        unfold e_steps in H3.
        unfold clos_refl_trans in H3.
        unfold clos_refl_trans.
        sets_unfold.
        sets_unfold in H3.
        destruct H3.
        exists x3.
        clear H2.
        revert x0 H3.
        induction x3.
        2:{
          intros.
          simpl.
          sets_unfold.
          simpl in H3.
          sets_unfold in H3.
          destruct H3.
          exists x4.
          destruct H2.
          split.
          2:{
            apply IHx3 in H3.
            tauto.
          }
          destruct H1.
          destruct H1.
          destruct H1.
          destruct H4.
          destruct H4.
          destruct H4.
          pose proof e_step_add_edge_preserves(T:=T).
          specialize (H6 x1 x7 s1 x6 x5 v2 v3 x0 x4).
          apply H6 in H1.
          2:{
            pose proof H4.
            destruct H4.
            rewrite <- H8 in H7.
            tauto.
          }
          2:{
            tauto.
          }
          destruct H5.
          rewrite H5.
          tauto.
      }
      intros.
      simpl.
      simpl in H3.
      unfold Rels.id in H3.
      unfold Rels.id.
      simpl.
      simpl in H3.
      tauto.
    }
    specialize (IHstr2 x s1 s2).
    apply IHstr2 in H0.
    2:{
      tauto.
    }
    pose proof c_step_add_edge_preserves(T:=T).
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H5.
    destruct H5.
    destruct H5.
    specialize (H4 x1 x5 s1 x4 x3 v2 v3 x x0 a0).
    apply H4 in H1.
    2:{
      pose proof H5.
      destruct H5.
      rewrite <- H8 in H7.
      tauto.
    }
    2:{
      tauto.
    }
    destruct H6.
    rewrite H6.
    tauto.
  }
  intros.
  simpl.
  simpl in H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H2.
  destruct H2.
  pose proof add_edge_match_preserve(T:=T).
  specialize (H4 str1 x1 x3 x0 x4 x v1 v2 v2 v3).
  apply H4 in H.
  2:{
    tauto.
  }
  assert (H5: e_step x3 v2 v3).
  {
    destruct H2.
    destruct H2.
    destruct add_edge_pg0.
    unfold e_step.
    exists x.
    split.
    - split.
      + unfold Sets_disjoint_union in add_edge_edge.
        sets_unfold in add_edge_edge.
        destruct add_edge_edge.
        assert (H7 : (x1.(pg)).(evalid) x \/ x = x).
        {
          tauto.
        }
        apply H6 in H7.
        tauto.
      + unfold string_step in H.
        apply add_edge_vertex.
        tauto.
      + unfold string_step in H.
        apply add_edge_vertex.
        tauto.
      + tauto.
      + tauto.
    - tauto.
  }
  pose proof e_step_extend_string_step2(T:=T).
  specialize (H6 x3 v1 v2 v3 str1).
  pose proof H5.
  apply H6 in H5.
  2:{
    tauto.
  }
  destruct H3.
  rewrite H3.
  pose proof e_step_extend_string_step2(T:=T).
  specialize (H9 x3 v1 v2 v3 str1).
  apply H9 in H7.
  2:{
    tauto.
  }
  destruct H0.
  assert (H10 : e_steps x3 v3 v4).
  {
    unfold e_steps.
    unfold clos_refl_trans.
    sets_unfold.
    exists x5.
    destruct H2.
    destruct H2.
    destruct add_edge_pg0.
    clear Hh add_edge_dst_new H4 H5 H7 H9 H6.
    revert v3 H0.
    induction x5.
    2:{
      intros.
      destruct H0.
      sets_unfold in H0.
      destruct H0.
      apply IHx5 in H2.
      exists x6.
      sets_unfold.
      split.
      2:{
        tauto.
      }
      unfold e_step.
      destruct H0.
      destruct H0.
      exists x7.
      split.
      - split.
        destruct H0.
        destruct add_edge_edge.
        sets_unfold in H5.
        assert (H6: (x1.(pg)).(evalid) x7 \/ x = x7).
        {
          left;tauto. 
        }
        apply H5 in H6.
        tauto.
        apply add_edge_vertex.
        destruct H0.
        tauto.
        apply add_edge_vertex.
        destruct H0.
        tauto.
        destruct H0.
        apply add_edge_src_old in step_evalid.
        rewrite step_evalid.
        tauto.
        destruct H0.
        apply add_edge_dst_old in step_evalid.
        rewrite step_evalid.
        tauto.
      - destruct H0.
        apply add_edge_symbol_old0 in step_evalid.
        rewrite step_evalid.
        tauto.
    }
    intros.
    simpl in H0.
    simpl.
    unfold Rels.id in H0.
    unfold Rels.id.
    tauto. 
  }
  destruct H2.
  destruct H2.
  destruct add_edge_pg0.
  clear add_edge_dst_new H4 H5 H6 H9.
  revert v3 H0 Hh H7 H10.
  induction x5.
  2:{
    intros.
    simpl in H0.
    sets_unfold in H0.
    destruct H0.
    destruct H0.
    apply IHx5 in H2.
    2:{
      destruct H0.
      destruct H0.
      destruct H0.
      tauto.
    }
    tauto.
    assert (H12 :  e_step x3 v3 x6).
    {
      unfold e_step.
      destruct H0.
      destruct H0.
      exists x7.
      split.
      - split.
        destruct H0.
        destruct add_edge_edge.
        sets_unfold in H5.
        assert (H6: (x1.(pg)).(evalid) x7 \/ x = x7).
        {
          left;tauto. 
        }
        apply H5 in H6.
        tauto.
        apply add_edge_vertex.
        destruct H0.
        tauto.
        apply add_edge_vertex.
        destruct H0.
        tauto.
        destruct H0.
        apply add_edge_src_old in step_evalid.
        rewrite step_evalid.
        tauto.
        destruct H0.
        apply add_edge_dst_old in step_evalid.
        rewrite step_evalid.
        tauto.
      - destruct H0.
        apply add_edge_symbol_old0 in step_evalid.
        rewrite step_evalid.
        tauto.
    }
    pose proof e_step_extend_string_step2(T:=T).
    specialize (H4 x3 v1 v3 x6 str1).
    apply H4 in H12.
    tauto.
    tauto.
    exists x5.
    clear H0.
    revert x6 H2.
    induction x5.
    2:{
      intros.
      destruct H2.
      sets_unfold in H0.
      destruct H0.
      exists x7.
      sets_unfold.
      split.
      - unfold e_step.
        destruct H0.
        destruct H0.
        exists x8.
        split.
        + split.
          destruct H0.
          destruct add_edge_edge.
          sets_unfold in H5.
          assert (H6: (x1.(pg)).(evalid) x8 \/ x = x8).
          {
            left;tauto. 
          }
          apply H5 in H6.
          tauto.
          apply add_edge_vertex.
          destruct H0.
          tauto.
          apply add_edge_vertex.
          destruct H0.
          tauto.
          destruct H0.
          apply add_edge_src_old in step_evalid.
          rewrite step_evalid.
          tauto.
          destruct H0.
          apply add_edge_dst_old in step_evalid.
          rewrite step_evalid.
          tauto.
        + destruct H0.
          apply add_edge_symbol_old0 in step_evalid.
          rewrite step_evalid.
          tauto.
      - clear H0 IHx5 IHx0.
        revert x7 H2.
        induction x5.
        2:{
          intros.
          destruct H2.
          sets_unfold in H0.
          destruct H0.
          exists x8.
          sets_unfold.
          split.
          2:{
            apply IHx5 in H2.
            tauto.
          }
          unfold e_step.
          destruct H0.
          destruct H0.
          exists x9.
          split.
          + split.
            destruct H0.
            destruct add_edge_edge.
            sets_unfold in H5.
            assert (H6: (x1.(pg)).(evalid) x9 \/ x = x9).
            {
              left;tauto. 
            }
            apply H5 in H6.
            tauto.
            apply add_edge_vertex.
            destruct H0.
            tauto.
            apply add_edge_vertex.
            destruct H0.
            tauto.
            destruct H0.
            apply add_edge_src_old in step_evalid.
            rewrite step_evalid.
            tauto.
            destruct H0.
            apply add_edge_dst_old in step_evalid.
            rewrite step_evalid.
            tauto.
          + destruct H0.
            apply add_edge_symbol_old0 in step_evalid.
            rewrite step_evalid.
            tauto.
        }
        intros.
        simpl.
        unfold Rels.id.
        simpl in H2.
        unfold Rels.id in H2.
        tauto.
    }
    tauto.
  }
  intros.
  simpl in H0.
  unfold Rels.id in H0.
  simpl in H0.
  rewrite <- H0.
  tauto.
Qed.

(* 在图x1中，如果从顶点v1到顶点v2通过字符串str1匹配，同时从顶点v3到顶点v4通过字符串str2匹配，
  并且顶点v2和顶点v3都是x1中的点，图x2是x1在v2和v3之间添加一条epsilon边得到的，
  将字符串str1和str2拼接起来，则x2中从顶点v1到顶点v4也能match_str拼接后的字符串。 *)
Lemma match_str_concat:
  forall  {T :Type} (str1 str2: list T)(a : elem T) (x1 x2: pg_nfa T)(s1 s2 s3:state) (v1 v2 v3 v4 :Z),
  match_str x1 v1 v2 str1->
  match_str x1 v3 v4 str2->
  x1.(pg).(vvalid) v2 /\ x1.(pg).(vvalid) v3->
  (s1, x2, s2)
  ∈ (graph_constr_rec x1 [E v2 v3 epsilon]).(nrm)->
  match_str x2 v1 v4 (str2 ++ str1).
Proof. 
  intros.
  unfold match_str.
  unfold match_str in H, H0.
  revert v4 H0 H1 H2.
  induction str2.
  2:{
    intros.
    simpl.
    sets_unfold.
    destruct H0.
    sets_unfold in H0.
    destruct H0.
    exists x.
    split.
    - apply IHstr2 in H0.
      + tauto.
      + tauto.
      + tauto.
    - unfold char_step.
      sets_unfold.
      destruct H3.
      sets_unfold in H3.
      destruct H3.
      exists x0.
      split.
      + pose proof c_step_add_edge_preserves(T:=T).
        destruct H2.
        destruct H2.
        destruct H2.
        destruct H6.
        destruct H6.
        destruct H6.
        specialize (H5 x1 x5 s1 x4 x3 v2 v3 x x0 a0).
        pose proof H6.
        destruct H8.
        rewrite <- H9 in H6.
        apply H5 in H2.
        * destruct H7.
          rewrite H7.
          tauto.
        * tauto.
        * tauto.
      + clear H3.
        destruct H4.
        exists x3.
        revert x0 H3.
        induction x3.
        2:{
          intros.
          destruct H3.
          sets_unfold in H3.
          destruct H3.
          apply IHx3 in H4.
          exists x4.
          sets_unfold.
          split.
          - pose proof e_step_add_edge_preserves(T:=T).
            destruct H2.
            destruct H2.
            destruct H2.
            destruct H6.
            destruct H6.
            destruct H6.
            specialize (H5 x1 x7 s1 x6 x5 v2 v3 x0 x4).
            pose proof H6.
            destruct H6.
            rewrite <- H9 in H8.
            apply H5 in H2.
            + destruct H7.
              rewrite H7.
              tauto.
            + tauto.
            + tauto.
          - tauto.
        }
        intros.
        simpl.
        unfold Rels.id.
        simpl.
        simpl in H3.
        unfold Rels.id in H3.
        simpl in H3.
        tauto.
  }
  intros.
  destruct H0.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  pose proof app_nil_l.
  specialize (H5 T str1).
  rewrite H5.
  pose proof add_edge_match_preserve(T:=T).
  specialize (H6 str1 x1 x4 x3 x5 x0 v1 v2 v2 v3).
  apply H6 in H.
  2:{
    tauto.
  }
  destruct H4.
  rewrite H4.
  unfold match_str in H.
  pose proof e_step_extend_string_step2(T:=T).
  assert (H9 : e_step x4 v2 v3).
  {
    unfold e_step.
    exists x0.
    split.
    - split.
      destruct H3.
      destruct H3.
      destruct add_edge_pg0.
      unfold Sets_disjoint_union in add_edge_edge.
      sets_unfold in add_edge_edge.
      destruct  add_edge_edge.
      assert (H11: (x1.(pg)).(evalid) x0 \/ x0 = x0).
      {
        right;tauto. 
      }
      apply H10 in H11.
      tauto.
      destruct H3.
      destruct H3.
      destruct add_edge_pg0.
      apply add_edge_vertex.
      tauto.
      destruct H3.
      destruct H3.
      destruct add_edge_pg0.
      apply add_edge_vertex.
      tauto.
      destruct H3.
      destruct H3.
      destruct add_edge_pg0.
      tauto.
      destruct H3.
      destruct H3.
      destruct add_edge_pg0.
      tauto.
    - destruct H3.
      destruct H3.
      tauto.
  }
  specialize (H8 x4 v1 v2 v3 str1).
  apply H8 in H9.
  2:{
    tauto.
  }
  assert (H10: nsteps (e_step x4) x v3 v4 ).
  {
    destruct H3.
    destruct H3.
    destruct add_edge_pg0.
    clear H6 H8 H9 add_edge_dst_new.
    revert v3 H0 H1.
    induction x.
    2:{
      intros.
      destruct H0.
      sets_unfold in H0.
      destruct H0.
      apply IHx in H3.
      2:{
        destruct H0.
        destruct H0.
        destruct H0.
        tauto.
      }
      exists x6.
      sets_unfold.
      split.
      - destruct H0.
        exists x7.
        destruct H0.
        split.
        + split.
          destruct H0.
          unfold Sets_disjoint_union in add_edge_edge.
          sets_unfold in add_edge_edge.
          destruct  add_edge_edge.
          assert (H11: (x1.(pg)).(evalid) x7 \/ x0 = x7).
          {
            left;tauto. 
          }
          apply H8 in H11.
          tauto.
          destruct H0.
          apply add_edge_vertex.
          tauto.
          destruct H0.
          apply add_edge_vertex.
          tauto.
          destruct H0.
          apply add_edge_src_old in step_evalid.
          rewrite step_evalid.
          tauto.
          destruct H0.
          apply add_edge_dst_old in step_evalid.
          rewrite step_evalid.
          tauto.
        + destruct H0.
          apply add_edge_symbol_old0 in step_evalid.
          rewrite step_evalid. 
          tauto.
      - tauto.
    }
    intros.
    simpl.
    unfold Rels.id.
    simpl in H0.
    unfold Rels.id in H0.
    tauto. 
  }
  assert (H11 : e_steps x4 v3 v4).
  {
    unfold e_steps.
    unfold clos_refl_trans.
    sets_unfold.
    exists x.
    tauto. 
  }
  destruct H3.
  destruct H3.
  destruct add_edge_pg0.
  clear H10 H H0 add_edge_dst_new H6 H8.
  destruct H11.
  revert v3 H1 H9 H.
  induction x6.
  2:{
    intros.
    destruct H.
    sets_unfold in H.
    destruct H.
    apply IHx6 in H0.
    - tauto.
    - destruct H.
      destruct H.
      destruct H.
      apply add_edge_vertex in step_dst_valid.
      tauto.
    - pose proof e_step_extend_string_step2(T:=T).
      specialize (H3 x4 v1 v3 x7 str1).
      apply H3 in H.
      + tauto.
      + tauto.
  }
  intros.
  simpl in H.
  unfold Rels.id in H.
  simpl in H.
  rewrite <- H.
  tauto.
Qed.

(* 经过union_rel得到的新图能够保留原有的e_step *)
Lemma union_rel_e_step_preserves :
  forall {T} (x1 x2 x3: pg_nfa T) (x y :Z),
  union_rel x3 x1 x2 -> 
  e_step x1 x y ->
  e_step x2 x y.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct H.
  unfold e_step.
  exists x0.
  split.
  - split.
    + destruct H.
      destruct union_pg0.
      destruct union_edge.
      sets_unfold in H1.
      assert (H2 : (x3.(pg)).(evalid) x0 \/ (x1.(pg)).(evalid) x0).
      {
        right.
        tauto. 
      }
      apply H1 in H2.
      tauto.
    + destruct H.
      destruct union_pg0.
      destruct union_vertex.
      sets_unfold in H1.
      assert (H2 : (x3 .(pg)).(vvalid) x \/ (x1.(pg)).(vvalid) x).
      {
        right.
        tauto. 
      }
      apply H1 in H2.
      tauto.
    + destruct H.
      destruct union_pg0.
      destruct union_vertex.
      sets_unfold in H1.
      assert (H2 : (x3.(pg)).(vvalid) y \/ (x1.(pg)).(vvalid) y).
      {
        right.
        tauto. 
      }
      apply H1 in H2.
      tauto.
    + destruct H.
      destruct union_pg0.
      sets_unfold in union_src2.
      apply union_src2 in step_evalid.
      rewrite <- step_evalid in step_src.
      tauto.
    + destruct H.
      destruct union_pg0.
      sets_unfold in union_dst2.
      apply union_dst2 in step_evalid.
      rewrite <- step_evalid in step_dst.
      tauto.
  - destruct H.
    apply union_symbol4 in step_evalid.
    rewrite step_evalid.
    tauto.
Qed.
      
(* 经过union_rel得到的新图能够保留原有的c_step *)
Lemma union_rel_c_step_preserves :
  forall {T} (x1 x2 x3: pg_nfa T) (x y :Z) (a: T),
  union_rel x3 x1 x2 -> 
  c_step x1 a x y ->
  c_step x2 a x y.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct H.
  unfold e_step.
  exists x0.
  exists x4.
  split.
  - split.
    + destruct H.
      destruct H.
      destruct union_pg0.
      destruct union_edge.
      sets_unfold in H1.
      assert (H2 : (x3.(pg)).(evalid) x0 \/ (x1.(pg)).(evalid) x0).
      {
        right.
        tauto. 
      }
      apply H1 in H2.
      tauto.
    + destruct H.
      destruct H.
      destruct union_pg0.
      destruct union_vertex.
      sets_unfold in H1.
      assert (H2 : (x3 .(pg)).(vvalid) x \/ (x1.(pg)).(vvalid) x).
      {
        right.
        tauto. 
      }
      apply H1 in H2.
      tauto.
    + destruct H.
      destruct H.
      destruct union_pg0.
      destruct union_vertex.
      sets_unfold in H1.
      assert (H2 : (x3.(pg)).(vvalid) y \/ (x1.(pg)).(vvalid) y).
      {
        right.
        tauto. 
      }
      apply H1 in H2.
      tauto.
    + destruct H.
      destruct H.
      destruct union_pg0.
      sets_unfold in union_src2.
      apply union_src2 in step_evalid.
      rewrite <- step_evalid in step_src.
      tauto.
    + destruct H.
      destruct H.
      destruct union_pg0.
      sets_unfold in union_dst2.
      apply union_dst2 in step_evalid.
      rewrite <- step_evalid in step_dst.
      tauto.
  - destruct H.
    destruct H.
    apply union_symbol4 in step_evalid.
    rewrite step_evalid.
    tauto.
Qed.

(* 给定一个字符串 str，如果在原图 x1 中，从顶点 v1 到顶点 v2 可以通过字符串 str 实现匹配，
  并且我们通过 G_add_graph 将两个图 x4 和 x2 合并到新的图 x3 中，
  那么 x3 中从 v1 到 v2 也可以通过相同的字符串 str 进行匹配。 *)
Lemma add_graph_match_preserve1 :
  forall {T: Type}(str: list T) (x1 x2 x3 x4: pg_nfa T)(s1 s2:state) (v1 v2 :Z),
  match_str x1 v1 v2 str->
  union_rel empty_nfa x1 x4->
  (s1, x3, s2) ∈ (G_add_graph x4 x2).(nrm)->
  match_str x3 v1 v2 (str).
Proof.
  intros.
  unfold match_str in H.
  unfold match_str.
  revert v2 H.
  induction str.
  2:{
    intros.
    unfold match_str in H.
    simpl in H.
    sets_unfold in H.
    destruct H.
    simpl.
    sets_unfold.
    exists x.
    split.
    destruct H.
    - apply IHstr in H.
      tauto.
    - destruct H.
      unfold char_step.
      unfold char_step in H2.
      sets_unfold in H2.
      sets_unfold.
      destruct H2.
      exists x0.
      destruct H2.
      split.
      2:{
        unfold e_steps.
        unfold e_steps in H3.
        unfold clos_refl_trans in H3.
        unfold clos_refl_trans.
        sets_unfold.
        sets_unfold in H3.
        destruct H3.
        exists x5.
        clear H2.
        revert x0 H3.
        induction x5.
        2:{
          intros.
          simpl.
          sets_unfold.
          simpl in H3.
          sets_unfold in H3.
          destruct H3.
          exists x6.
          destruct H2.
          split.
          2:{
            apply IHx5 in H3.
            tauto.
          }
          pose proof e_step_add_graph_preserves2(T:=T).
          pose proof H1.
          destruct H5.
          rewrite H6 in H1.
          specialize (H4 x4 x2 x3 x0 x6 s2).
          apply H4 in H1.
          tauto.
          pose proof union_rel_e_step_preserves(T:=T).
          specialize (H7 x1 x4 empty_nfa x0 x6).
          apply H7 in H0.
          tauto.
          tauto.
        }
        intros.
        simpl in H3.
        simpl.
        unfold Rels.id in H3.
        unfold Rels.id.
        simpl.
        simpl in H3.
        tauto. 
      }
      pose proof c_step_add_graph_preserves2(T:=T).
      pose proof H1.
      destruct H5.
      rewrite H6 in H1.
      specialize (H4 x4 x2 x3 x x0 s2 a).
      apply H4 in H1.
      tauto.
      pose proof union_rel_c_step_preserves(T:=T).
      specialize (H7 x1 x4 empty_nfa x x0 a).
      apply H7 in H0.
      tauto.
      tauto.   
  }
  intros.
  simpl.
  simpl in H.
  unfold e_steps.
  unfold e_steps in H.
  unfold clos_refl_trans in H.
  unfold clos_refl_trans.
  sets_unfold.
  sets_unfold in H.
  destruct H.
  exists x.
  revert v1 H.
  induction x.
  2:{
    intros.
    simpl.
    sets_unfold.
    simpl in H.
    sets_unfold in H.
    destruct H.
    exists x0.
    destruct H.
    split.
    2:{
      apply IHx in H2.
      tauto.
    }
    pose proof e_step_add_graph_preserves2(T:=T).
    pose proof H1.
    destruct H4.
    rewrite H5 in H1.
    specialize (H3 x4 x2 x3 v1 x0 s2).
    apply H3 in H1.
    tauto.
    pose proof union_rel_e_step_preserves(T:=T).
    specialize (H6 x1 x4 empty_nfa v1 x0).
    apply H6 in H0.
    tauto.
    tauto.
  }
  intros.
  simpl in H.
  simpl.
  unfold Rels.id in H.
  unfold Rels.id.
  simpl.
  simpl in H.
  tauto.
Qed. 

(* 给定一个字符串 str，如果在图 x2 中，从顶点 v1 到顶点 v2 可以通过字符串 str 实现匹配，
  并且我们通过 G_add_graph 将图 x1 和图 x2 合并到一个新的图 x3 中，
  那么在合并后的图 x3 中，从顶点 v1 到顶点 v2 也能通过字符串 str 实现匹配。 

  证明类似add_graph_match_preserve1故略去 *)
Lemma add_graph_match_preserve2:
  forall {T: Type} (str: list T) (x1 x2 x3: pg_nfa T)(s1 s2:state) (v1 v2 :Z),
  match_str x2 v1 v2 str->
  (s1, x3, s2) ∈ (G_add_graph x1 x2).(nrm)->
  match_str x3 v1 v2 (str).
Proof.
intros.
unfold match_str in H.
unfold match_str.
revert v2 H.
induction str.
2:{
  intros.
  unfold match_str in H.
  simpl in H.
  sets_unfold in H.
  destruct H.
  simpl.
  sets_unfold.
  exists x.
  split.
  destruct H.
  - apply IHstr in H.
    tauto.
  - destruct H.
    unfold char_step.
    unfold char_step in H1.
    sets_unfold in H1.
    sets_unfold.
    destruct H1.
    exists x0.
    destruct H1.
    split.
    2:{
      unfold e_steps.
      unfold e_steps in H2.
      unfold clos_refl_trans in H2.
      unfold clos_refl_trans.
      sets_unfold.
      sets_unfold in H2.
      destruct H2.
      exists x4.
      clear H1.
      revert x0 H2.
      induction x4.
      2:{
        intros.
        simpl.
        sets_unfold.
        simpl in H2.
        sets_unfold in H2.
        destruct H2.
        exists x5.
        destruct H1.
        split.
        2:{
          apply IHx4 in H2.
          tauto.
        }
        pose proof e_step_add_graph_preserves1(T:=T).
        pose proof H0.
        destruct H4.
        rewrite H5 in H0.
        specialize (H3 x1 x2 x3 x0 x5 s2).
        apply H3 in H0.
        tauto.
        pose proof union_rel_e_step_preserves(T:=T).
        specialize (H6 x2 x3 x1 x0 x5).
        apply H6 in H4.
        tauto.
        tauto.
      }
      intros.
      simpl in H2.
      simpl.
      unfold Rels.id in H2.
      unfold Rels.id.
      simpl.
      simpl in H2.
      tauto. 
    }
    pose proof c_step_add_graph_preserves1(T:=T).
    pose proof H0.
    destruct H4.
    rewrite H5 in H0.
    specialize (H3 x1 x2 x3 x x0 s2 a).
    apply H3 in H0.
    tauto.
    pose proof union_rel_c_step_preserves(T:=T).
    specialize (H6 x2 x3 x1 x x0 a).
    apply H6 in H4.
    tauto.
    tauto.   
}
intros.
simpl.
simpl in H.
unfold e_steps.
unfold e_steps in H.
unfold clos_refl_trans in H.
unfold clos_refl_trans.
sets_unfold.
sets_unfold in H.
destruct H.
exists x.
revert v1 H.
induction x.
2:{
  intros.
  simpl.
  sets_unfold.
  simpl in H.
  sets_unfold in H.
  destruct H.
  exists x0.
  destruct H.
  split.
  2:{
    apply IHx in H1.
    tauto.
  }
  pose proof e_step_add_graph_preserves1(T:=T).
  pose proof H0.
  destruct H3.
  rewrite H4 in H0.
  specialize (H2 x1 x2 x3 v1 x0 s2).
  apply H2 in H0.
  tauto.
  tauto.
}
intros.
simpl in H.
simpl.
unfold Rels.id in H.
unfold Rels.id.
simpl.
simpl in H.
tauto.
Qed. 

(* 正则表达式匹配到nfa匹配 *)
Lemma concat_hoare_backward {T: Type}:
  forall (str : list T) (s: state) (r1:reg_exp T)(r2: reg_exp T),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA (Concat_r r1 r2))                           
    (fun (e : elem T) (s2 : state) =>                          
    exp_match (Concat_r r1 r2) str ->MatchR r1/\MatchR r2->match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  split.
  - intros.
    intros contra.
    apply derive_false in contra.
    tauto.
  - intros.
    apply RexMatch_ConcatR in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H3.
    destruct H2.
    repeat destruct H0.
    repeat destruct H6.
    unfold MatchR in H2.
    specialize (H2 x s1 x2 s x1).
    apply H2 in H1.
    2:{
      tauto.
    }
    2:{
       tauto. 
    }
    specialize (H5 x0 x2 x4 x2 x3).
    apply H5 in H3.
    2:{
      tauto.
    }
    2:{
       tauto. 
    }
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H9.
    destruct H9.
    destruct H9.
    clear H2.
    clear H5.
    pose proof (add_graph_match_preserve1(T := T)).
    specialize (H2 x x1.(graph) x3.(graph) x9 x7 x8 x10 x1.(startVertex) x1.(endVertex)).
    apply H2 in H1.
    2:{
      tauto.
    }
    2:{
      tauto.
    }
    pose proof (add_graph_match_preserve2(T := T)).
    specialize (H5 x0 x7 x3.(graph) x9 x8 x10 x3.(startVertex) x3.(endVertex)).
    apply H5 in H3.
    2:{
      tauto.
    }
    pose proof match_str_concat(T:=T).
    specialize (H12 x x0 a x9 x5 x10 x6 s2 x1.(startVertex) x1.(endVertex) x3.(startVertex) x3.(endVertex)).
    apply H12 in H1.
    2:{
      tauto.
    }
    3:{
      tauto.
    }
    rewrite <- H4 in H1.
    destruct H8.
    rewrite H8.
    simpl.
    tauto.
    destruct H9.
    destruct H9.
    destruct union_pg0.
    unfold Sets_disjoint_union in union_vertex.
    destruct union_vertex.
    sets_unfold in H14.
    split.
    + apply H14.
      left.
      destruct H7.
      destruct union_pg0.
      unfold Sets_disjoint_union in union_vertex.
      destruct union_vertex.
      sets_unfold in H15.
      apply H15.
      right.
      pose proof start_end_in_graph(T:=T).
      specialize (H16 x1 s1 x2 r1).
      apply H16 in H0.
      tauto.
    + apply H14.
      right.
      pose proof start_end_in_graph(T:=T).
      specialize (H15 x3 x2 x4 r2).
      apply H15 in H6.
      tauto.
Qed.

(* 正则表达式匹配到nfa匹配 *)

(* 如果能够通过r1生成的nfa的str也能够在通过正则表达式r1 *)
Definition MatchE {T} (r1 : reg_exp T) :=
  forall (str:list T) (s1 s2 s: state) (a: elem T),
  (s1, a, s2) ∈ (regexToNFA r1).(nrm) ->
  match_str a.(graph) a.(startVertex) a.(endVertex) str->
  s1 = s->
  exp_match r1 str .

(* 如果 a 是 x 和 x1 act_concat得到的结果那么存在字符串 str = str2 ++ str1 ，满足 str1 可以匹配 x， str2可以匹配 x1 *)
Lemma NfaMatch_ConcatR{T}:
  forall (str: list T)(x x1 a: elem T)(r1 r2 :reg_exp T)(v1 v2:Z)(s1 s2 s3 s4:state),
  match_str a.(graph) v1 v2 str ->
  (s1, x, s2) ∈ (regexToNFA r1).(nrm)->
  (s2, x1, s3) ∈ (regexToNFA r2).(nrm)->
  (s3, a, s4) ∈ (act_concat x x1).(nrm)->
  exists (str1 str2: list T),
  match_str x.(graph) v1 x.(endVertex) str1 /\ match_str x1.(graph) x1.(startVertex) v2 str2 /\ str = str2 ++ str1.
Proof.
Admitted.

(* nfa匹配到正则表达式匹配 *)
Lemma concat_hoare_forward {T: Type}:
  forall (str : list T) (s: state) (r1:reg_exp T)(r2: reg_exp T),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA (Concat_r r1 r2))                          
    (fun (e : elem T) (s2 : state) =>                          
    MatchE r1 /\ MatchE r2->match_str e.(graph) e.(startVertex) e.(endVertex) str ->exp_match (Concat_r r1 r2) str).
Proof.
  intros.
  unfold Hoare.
  split.
  - intros.
    intros contra.
    pose proof derive_false.
    apply H0 in contra.
    tauto.
  - intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H3.
    destruct H3.
    destruct H3.
    unfold MatchE in H1.
    destruct H1.
    pose proof NfaMatch_ConcatR(T:=T).
    specialize (H6 str x x1 a r1 r2 a.(startVertex) a.(endVertex) s1 x0 x2 s2).
    apply H6 in H2.
    2:{
      tauto.
    }
    2:{
      tauto.
    }
    2:{
      tauto.
    }
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H7.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H10.
    destruct H10.
    destruct H10.
    destruct H9.
    rewrite H9 in H2, H7.
    simpl in H2, H7.
    specialize (H1 x3 s1 x0 s x).
    apply H1 in H0.
    2:{
      tauto.
    }
    2:{
      tauto.
    }
    specialize (H5 x4 x0 x2 x0 x1).
    apply H5 in H3.
    2:{
      tauto.
    }
    2:{
      tauto.
    }
    simpl.
    unfold set_prod.
    exists x3 ,x4.
    tauto.
Qed.


(*********************************************************)
(**                                                      *)
(** Star                                                 *)
(**                                                      *)
(*********************************************************)

(* 引理说明了string step的连接性。
  具体来说：如果有两个字符串片段 `s1` 和 `s2`，
  分别从状态 `v1` 到 `v2` 和从状态 `v2` 到 `v3` 进行string step（即每个字符串片段都能独立地通过一个图 `x` 进行），
  那么它们的拼接字符串 `s1 ++ s2` 将能从状态 `v1` 到状态 `v3` 进行string step。

  本引理证明与match_str_graph_constr_rec类似。 *)
Lemma string_step_concat {T: Type}:
forall (x: pg_nfa T) (s1 s2: list T) (v1 v2 v3: Z),
  string_step x s1 v1 v2 ->
  string_step x s2 v2 v3 ->
  string_step x (s1 ++ s2) v1 v3.
Admitted.

(* 正则表达式匹配到nfa匹配 *)
Theorem star_hoare_backward {T: Type}:
forall (s: state) (r: reg_exp T) (str: list T),
  (forall (s0: state) (str1: list T),
  Hoare 
  (fun s1 : state => s1 = s0) 
  (regexToNFA r)
  (fun (e : elem T) (_ : state) =>
    exp_match r str1 ->
    match_str e.(graph) e.(startVertex) e.(endVertex) str1)) ->
  Hoare
  (fun s1 => s1 = s)
  (regexToNFA (Star_r r))
  (fun(e : elem T) (s2 : state) =>
    exp_match (Star_r r) str -> match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  split.
  + intros.
    unfold not.
    intros.
    pose proof derive_false T (Star_r r) s1 H1.
    tauto.
  + intros.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    destruct H10.
    destruct H10.
    destruct H11.
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H13.
    destruct H14.
    destruct H14.
    destruct H14.
    destruct H15.
    destruct H6.
    unfold match_str.
    rewrite H6.
    simpl.
    assert ((string_step x5 str x1 x.(endVertex)) -> (string_step x5 str x1 x3)).
    intros.
    pose proof start_end_in_graph x s1 x0 r H1.
    destruct H19.
    pose proof add_graph_num_vertex1 x4 x8 x7 empty_nfa x.(graph) H5 x.(endVertex).
    assert ((x7.(pg)).(vvalid) x.(endVertex)).
    tauto.
    pose proof add_vertex_in_graph x8 x10 x9 x7 x1 H7 x.(endVertex).
    assert ((x9.(pg)).(vvalid) x.(endVertex)).
    tauto.
    pose proof add_vertex_in_graph x10 x12 x11 x9 x3 H8 x.(endVertex).
    assert ((x11.(pg)).(vvalid) x.(endVertex)).
    tauto.
    pose proof add_edge_in_graph x14 x16 x15 x11 x13 x1 x.(endVertex) epsilon H10 x.(endVertex).
    assert ((x15.(pg)).(vvalid) x.(endVertex)).
    tauto.
    pose proof add_vertex_in_graph x10 x12 x11 x9 x3 H8 x3.
    assert ((x11.(pg)).(vvalid) x3).
    tauto.
    pose proof add_edge_in_graph x14 x16 x15 x11 x13 x1 x.(endVertex) epsilon H10 x3.
    assert ((x15.(pg)).(vvalid) x3).
    tauto.
    pose proof add_edge_e_step x18 x20 x19 x15 x17 x.(endVertex) x3 H28 H32 H12.
    pose proof add_edge_preserve_e_step x22 x24 x23 x19 x21 x.(endVertex) x.(startVertex) x.(endVertex) x3 H33 H14.
    rewrite <- H15 in H34.
    pose proof e_step_extend_string_step2 x5 x1 x.(endVertex) x3 str H34 H18.
    tauto.
    apply H18.
    clear H18.
    destruct H2.
    revert H2.
    revert str.
    induction x25.
    2:{
      intros.
      simpl in H2.
      unfold set_prod in H2.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H18.
      pose proof IHx25 x27 H18.
      rewrite H19.
      pose proof H s1 x26.
      unfold Hoare in H21.
      destruct H21.
      pose proof H22 s1 x x0.
      assert (match_str x.(graph) x.(startVertex) x.(endVertex) x26).
      tauto.
      clear H23 H22 H21.
      unfold match_str in H24.
      pose proof start_end_in_graph x s1 x0 r H1.
      destruct H21.
      pose proof add_graph_num_vertex1 x4 x8 x7 empty_nfa x.(graph) H5 x.(startVertex).
      assert ((x7.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_graph_num_vertex1 x4 x8 x7 empty_nfa x.(graph) H5 x.(endVertex).
      assert ((x7.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x8 x10 x9 x7 x1 H7 x.(startVertex).
      assert ((x9.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_vertex_in_graph x8 x10 x9 x7 x1 H7 x.(endVertex).
      assert ((x9.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x10 x12 x11 x9 x3 H8 x.(startVertex).
      assert ((x11.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_vertex_in_graph x10 x12 x11 x9 x3 H8 x.(endVertex).
      assert ((x11.(pg)).(vvalid) x.(endVertex)).
      tauto.
      clear H34 H32 H30 H28 H26 H23.
      pose proof add_edge_in_graph x14 x16 x15 x11 x13 x1 x.(endVertex) epsilon H10 x.(startVertex).
      assert ((x15.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_edge_in_graph x14 x16 x15 x11 x13 x1 x.(endVertex) epsilon H10 x.(endVertex).
      assert ((x15.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x.(endVertex) x3 epsilon H12 x.(startVertex).
      assert ((x19.(pg)).(vvalid) x.(startVertex)).
      tauto.
      pose proof add_edge_in_graph x18 x20 x19 x15 x17 x.(endVertex) x3 epsilon H12 x.(endVertex).
      assert ((x19.(pg)).(vvalid) x.(endVertex)).
      tauto.
      clear H36 H32 H28 H23.
      pose proof add_edge_e_step x22 x24 x23 x19 x21 x.(endVertex) x.(startVertex) H37 H34 H14.
      rewrite <- H15 in H23.
      pose proof e_step_extend_string_step2 x5 x1 x.(endVertex) x.(startVertex) x27 H23 H20.
      pose proof add_graph_preserve_string_step2 x4 x8 x7 empty_nfa x.(graph) x.(startVertex) x.(endVertex) x26 H5 H24.
      pose proof add_vertex_preserve_string_step x8 x10 x9 x7 x1 x.(startVertex) x.(endVertex) x26 H7 H32.
      pose proof add_vertex_preserve_string_step x10 x12 x11 x9 x3 x.(startVertex) x.(endVertex) x26 H8 H36.
      pose proof add_edge_preserve_string_step x14 x16 x15 x11 x13 x1 x.(endVertex) x.(startVertex) x.(endVertex) epsilon x26 H10 H38.
      pose proof add_edge_preserve_string_step x18 x20 x19 x15 x17 x.(endVertex) x3 x.(startVertex) x.(endVertex) epsilon x26 H12 H39.
      pose proof add_edge_preserve_string_step x22 x24 x23 x19 x21 x.(endVertex) x.(startVertex) x.(startVertex) x.(endVertex) epsilon x26 H14 H40.
      rewrite <- H15 in H41.
      clear H24 H21 H22 H25 H27 H29 H31 H33 H35 H26 H30 H24 H37 H23 H32 H36 H38 H39 H40 H34 H20.
      pose proof string_step_concat x5 x27 x26 x1 x.(startVertex) x.(endVertex) H28 H41.
      apply H20.
    }
    intros.
    simpl in H2.
    sets_unfold in H2.
    rewrite <- H2.
    simpl.
    unfold e_steps.
    unfold clos_refl_trans.
    unfold Sets.indexed_union.
    simpl.
    exists Nat.one.
    simpl.
    sets_unfold.
    exists x.(endVertex).
    split.
    * pose proof add_vertex_in_graph x8 x10 x9 x7 x1 H7 x1.
      assert ((x9.(pg)).(vvalid) x1).
      tauto.
      pose proof add_vertex_in_graph x10 x12 x11 x9 x3 H8 x1.
      assert ((x11.(pg)).(vvalid) x1).
      tauto.
      pose proof start_end_in_graph x s1 x0 r H1.
      destruct H22.
      pose proof add_graph_num_vertex1 x4 x8 x7 empty_nfa x.(graph) H5 x.(endVertex).
      assert ((x7.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x8 x10 x9 x7 x1 H7 x.(endVertex).
      assert ((x9.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_vertex_in_graph x10 x12 x11 x9 x3 H8 x.(endVertex).
      assert ((x11.(pg)).(vvalid) x.(endVertex)).
      tauto.
      pose proof add_edge_e_step x14 x16 x15 x11 x13 x1 x.(endVertex) H21 H29 H10.
      pose proof add_edge_preserve_e_step x18 x20 x19 x15 x17 x.(endVertex) x3 x1 x.(endVertex) H30 H12.
      pose proof add_edge_preserve_e_step x22 x24 x23 x19 x21 x.(endVertex) x.(startVertex) x1 x.(endVertex) H31 H14.
      rewrite H15.
      apply H32.
    * reflexivity.
Qed.

(* 如果list可以在a（A的star）上从a的起始点走string_step到a的终点，那么它也可以在a上从A的起始点走string_step到A的终点 *)
Lemma act_star_shrink {T: Type}:
forall (s1 s2: state) (A: elem T) (a : elem T) (l: list T),
  (s1, a, s2) ∈ (act_star A).(nrm) ->
  string_step a.(graph) l a.(startVertex) a.(endVertex) ->
  (string_step a.(graph) l A.(endVertex) A.(endVertex)).
Admitted.

(* 如果一个正则表达式r匹配一个字符串l，那么字符串l可以在nfa G中通过 string_step 从 x 到 y。 *)
Definition string_step_regex {T} (G: pg_nfa T) (r: reg_exp T): Z -> Z -> Prop :=
  fun x y => (forall l, exp_match r l -> string_step G l x y).

(* Fixpoint描述了n步的字符串匹配。它表示从状态x到状态y的n步字符串转换，其中每一步都可能匹配一个正则表达式r。 *)
Fixpoint string_n_step_regex {T} (n: nat) (G: pg_nfa T) (r: reg_exp T) : Z -> Z -> Prop :=
  match n with
  | O => (fun x y => x = y)
  | S n' => (string_step_regex G r) ∘ (string_n_step_regex n' G r)
  end.

Lemma act_star_loop {T: Type}:
forall (s1 s2 s3: state) (A: elem T) (a : elem T) (r: reg_exp T),
  (s1, A, s2) ∈ (regexToNFA r).(nrm) ->
  (s2, a, s3) ∈ (act_star A).(nrm) ->
  (forall (s0: state) (str1: list T),
  Hoare 
  (fun s1 : state => s1 = s0) 
  (regexToNFA r)
  (fun (e : elem T) (_ : state) =>
    match_str e.(graph) e.(startVertex) e.(endVertex) str1 ->
    exp_match r str1)) ->
  forall n, string_n_step_regex n a.(graph) r A.(endVertex) A.(endVertex).
Admitted.

(* act_star_loop will be used to prove act_star_aux *)
(* 扩展了act_star操作，表明如果通过act_star操作的步骤匹配了字符串，那么该字符串就匹配了正则表达式Star_r r *)
Lemma act_star_aux {T: Type}:
forall (s1 s2 s3: state) (A: elem T) (a : elem T) (r: reg_exp T) (str: list T),
  (s1, A, s2) ∈ (regexToNFA r).(nrm) ->
  (s2, a, s3) ∈ (act_star A).(nrm) ->
  (forall (s0: state) (str1: list T),
  Hoare 
  (fun s1 : state => s1 = s0) 
  (regexToNFA r)
  (fun (e : elem T) (_ : state) =>
    match_str e.(graph) e.(startVertex) e.(endVertex) str1 ->
    exp_match r str1)) ->
  string_step a.(graph) str A.(endVertex) A.(endVertex) ->
  exp_match (Star_r r) str.
Admitted.

(* nfa匹配到正则表达式匹配 *)
Theorem star_hoare_forward {T: Type}:
forall (s: state) (r: reg_exp T) (str: list T),
  (forall (s0: state) (str1: list T),
  Hoare 
  (fun s1 : state => s1 = s0) 
  (regexToNFA r)
  (fun (e : elem T) (_ : state) =>
    match_str e.(graph) e.(startVertex) e.(endVertex) str1 ->
    exp_match r str1)) ->
  Hoare
  (fun s1 => s1 = s)
  (regexToNFA (Star_r r))
  (fun(e : elem T) (s2 : state) =>
    match_str e.(graph) e.(startVertex) e.(endVertex) str -> exp_match (Star_r r) str).
Proof.
  intros.
  unfold Hoare.
  split.
  + intros.
    unfold not.
    intros.
    pose proof derive_false T (Star_r r) s1 H1.
    tauto.
  + intros.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    destruct H10.
    destruct H10.
    destruct H11.
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H13.
    destruct H14.
    destruct H14.
    destruct H14.
    destruct H15.
    destruct H6.
    rewrite H6 in H2.
    simpl in H2.
    unfold match_str in H2.
    pose proof act_star_shrink x0 s2 x a str.
    assert ((x0, a, s2) ∈ (act_star x).(nrm)).
    simpl.
    exists x1.
    exists x2.
    split.
    tauto.
    exists x3.
    exists x4.
    split.
    tauto.
    exists x5.
    exists x6.
    split.
    exists x7.
    exists x8.
    split.
    tauto.
    exists x9.
    exists x10.
    split.
    tauto.
    exists x11.
    exists x12.
    split.
    tauto.
    exists x13.
    exists x14.
    split.
    tauto.
    exists x15.
    exists x16.
    split.
    tauto.
    exists x17.
    exists x18.
    split.
    tauto.
    exists x19.
    exists x20.
    split.
    tauto.
    exists x21.
    exists x22.
    split.
    tauto.
    exists x23.
    exists x24.
    split.
    tauto.
    tauto.
    tauto.
    pose proof H18 H19.
    rewrite H6 in H20.
    simpl in H20.
    pose proof H20 H2.
    clear H18 H20.
    pose proof act_star_aux s1 x0 s2 x a r str H1 H19 H.
    rewrite H6 in H18.
    simpl in H18.
    pose proof H18 H21.
    simpl.
    tauto.
Qed.

    
(*********************************************************)
(**                                                      *)
(** 总命题                                                *)
(**                                                      *)
(*********************************************************)

(* 正则表达式匹配推导到nfa匹配 *)
Lemma regexToNFA_hoare_backward{T:Type}:
forall (str : list T) (s: state) (r :reg_exp T),
Hoare
  (fun s1 => s1 = s)                  
  (regexToNFA r)                          
  (fun (e : elem T) (s2 : state) =>                          
  exp_match r str ->match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  split.
  intros.
  intros contra.
  pose proof derive_false.
  specialize (H0 T r s1).
  tauto.
  intros.
  revert s1 s2 s a str H0 H H1.
  induction r.
  - pose proof empty_string_hoare_backward(T:=T).
    intros.
    specialize (H str s).
    apply H in H0.
    tauto.
    tauto.
    tauto.
  - pose proof char_set_hoare_backward(T:=T).
    intros.
    specialize (H str s).
    apply H in H0.
    tauto.
    tauto.
    tauto.
  - pose proof concat_hoare_backward(T:=T).
    intros.
    specialize (H str s r1 r2).
    unfold Hoare in H.
    destruct H.
    specialize (H3 s1 a s2).
    apply H3 in H2.
    tauto.
    tauto.
    tauto.
    split.
    unfold MatchR.
    intros.
    specialize (IHr1 s0 s3 s4 a0 str0).
    apply IHr1 in H4.
    tauto.
    tauto.
    tauto.
    unfold MatchR.
    intros.
    specialize (IHr2 s0 s3 s4 a0 str0).
    apply IHr2 in H4.
    tauto.
    tauto.
    tauto.
  - pose proof union_hoare_backward(T:=T).
    intros.
    specialize (H s r1 r2 str).
    destruct H.
    intros.
    unfold Hoare.
    split.
    intros.
    intros contra.
    pose proof derive_false.
    specialize (H3 T r1 s3).
    tauto.
    intros.
    specialize (IHr1 s3 s4 s0 a0 str).
    tauto.
    intros.
    unfold Hoare.
    split.
    intros.
    intros contra.
    pose proof derive_false.
    specialize (H3 T r2 s3).
    tauto.
    intros.
    specialize (IHr2 s3 s4 s0 a0 str).
    tauto.
    specialize (H3 s1 a s2).
    apply H3 in H1.
    tauto.
    tauto.
    tauto.
  - pose proof star_hoare_backward(T:=T).
    intros.
    specialize (H s r str).
    destruct H.
    intros.
    unfold Hoare.
    split.
    intros.
    intros contra.
    pose proof derive_false.
    specialize (H3 T r s3).
    tauto.
    intros.
    specialize (IHr s3 s4 s0 a0 str1).
    apply IHr in H3.
    tauto.
    tauto.
    tauto.
    specialize (H3 s1 a s2).
    apply H3 in H1.
    tauto.
    tauto.
    tauto.
Qed.

(* nfa匹配推导正则表达式匹配 *)
Lemma regexToNFA_hoare_forward{T:Type}:
forall (str : list T) (s: state) (r :reg_exp T),
Hoare
  (fun s1 => s1 = s)                  
  (regexToNFA r)                          
  (fun (e : elem T) (s2 : state) =>                          
  match_str e.(graph) e.(startVertex) e.(endVertex) str ->exp_match r str).
Proof.
  intros.
  unfold Hoare.
  split.
  intros.
  intros contra.
  pose proof derive_false.
  specialize (H0 T r s1).
  tauto.
  intros.
  revert s1 s2 s a str H0 H H1.
  induction r.
  - pose proof empty_string_hoare_forward(T:=T).
    intros.
    specialize (H str s).
    apply H in H0.
    tauto.
    tauto.
    tauto.
  - pose proof char_set_hoare_forward(T:=T).
    intros.
    specialize (H str s).
    apply H in H0.
    tauto.
    tauto.
    tauto.
  - pose proof concat_hoare_forward(T:=T).
    intros.
    specialize (H str s r1 r2).
    unfold Hoare in H.
    destruct H.
    specialize (H3 s1 a s2).
    apply H3 in H2.
    tauto.
    tauto.
    tauto.
    split.
    unfold MatchE.
    intros.
    specialize (IHr1 s0 s3 s4 a0 str0).
    apply IHr1 in H4.
    tauto.
    tauto.
    tauto.
    unfold MatchE.
    intros.
    specialize (IHr2 s0 s3 s4 a0 str0).
    apply IHr2 in H4.
    tauto.
    tauto.
    tauto.
  - pose proof union_hoare_forward(T:=T).
    intros.
    specialize (H s r1 r2 str).
    destruct H.
    intros.
    unfold Hoare.
    split.
    intros.
    intros contra.
    pose proof derive_false.
    specialize (H3 T r1 s3).
    tauto.
    intros.
    specialize (IHr1 s3 s4 s0 a0 str).
    tauto.
    intros.
    unfold Hoare.
    split.
    intros.
    intros contra.
    pose proof derive_false.
    specialize (H3 T r2 s3).
    tauto.
    intros.
    specialize (IHr2 s3 s4 s0 a0 str).
    tauto.
    specialize (H3 s1 a s2).
    apply H3 in H1.
    tauto.
    tauto.
    tauto.
  - pose proof star_hoare_forward(T:=T).
    intros.
    specialize (H s r str).
    destruct H.
    intros.
    unfold Hoare.
    split.
    intros.
    intros contra.
    pose proof derive_false.
    specialize (H3 T r s3).
    tauto.
    intros.
    specialize (IHr s3 s4 s0 a0 str1).
    apply IHr in H3.
    tauto.
    tauto.
    tauto.
    specialize (H3 s1 a s2).
    apply H3 in H1.
    tauto.
    tauto.
    tauto.
Qed.
