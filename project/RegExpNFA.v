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
  fun s => exists s1 s2, s1 ∈ A /\ s2 ∈ B /\ s = s1 ++ s2.

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

Lemma empty_set_equiv : ∅ == (fun _ : Z => False).
Proof.
  unfold Sets.empty.
  simpl.
  intros x.
  split.
  - tauto.
  - tauto.
Qed.



Lemma e_step_union_preserves :
forall T (g0 g: pg_nfa T) g1 x y (s: state),
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

Lemma c_step_union_preserves :
forall T (g0 g: pg_nfa T) g1 x y (s: state) (c: T),
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

Lemma after_G_add_graph_all_edge_number_become_larger :
forall {T: Type} (pg1 pg2: pg_nfa T) (s1 s2: state) (g: pg_nfa T),
  (s1, g, s2) ∈ (G_add_graph pg1 pg2).(nrm) ->
  forall gv, gv ∈ g.(pg).(evalid) -> gv <= s2.(max_e).
Admitted.

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


Lemma vvalid_range :
  forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
  (s1, elem1, s2) ∈ (regexToNFA r).(nrm) ->
  forall gv, gv ∈ elem1.(graph).(pg).(vvalid) -> s1.(max_v) < gv <= s2.(max_v).
Proof.
  intros.
  induction r.
  - 
    destruct H.
    destruct H.
    destruct H.
    destruct H.
Admitted.

Lemma evalid_range :
  forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
  (s1, elem1, s2) ∈ (regexToNFA r).(nrm) ->
  forall ge, ge ∈ elem1.(graph).(pg).(evalid) -> s1.(max_e) < ge <= s2.(max_e).
Proof.
  intros.
  induction r.
Admitted.

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
    pose proof (vvalid_range elem1 s1 s2 r1 H v Hcontra1).
    pose proof (vvalid_range elem2 s2 s3 r2 H0 v Hcontra2).
    lia.
  - intros Hcontra2.
    destruct Hcontra2 as [e [Hcontra1 Hcontra2]].
    pose proof (evalid_range elem1 s1 s2 r1 H e Hcontra1).
    pose proof (evalid_range elem2 s2 s3 r2 H0 e Hcontra2).
    lia.    
Qed.
        
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
      pose proof after_G_add_graph_all_edge_number_become_larger x3 x1.(graph) x4 x6 x5 H2.
      pose proof H7 x7.
      pose proof H8 H4.
      rewrite H5 in H6.
      rewrite H6 in H9.
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
      



Lemma concat_hoare_backward {T: Type}:
  forall (str : list T) (s: state) (r1:reg_exp T)(r2: reg_exp T),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA (Concat_r r1 r2))                           
    (fun (e : elem T) (s2 : state) =>                          
    exp_match (Concat_r r1 r2) str ->match_str e.(graph) e.(startVertex) e.(endVertex) str).
Proof.
  intros.
  unfold Hoare.
  split.
  - intros.
    intros contra.
    apply derive_false in contra.
    tauto.
  - intros.
  

