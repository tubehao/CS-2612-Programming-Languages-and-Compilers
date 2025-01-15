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

Lemma empty_string_hoare {T: Type}:
  forall (Σ: Type) (s: state),
  Hoare
    (fun s1 => s1 = s)                  
    (regexToNFA EmptyStr_r)                           
    (fun (e : elem T) (s2 : state) =>                          
      match_str e.(graph) e.(startVertex) e.(endVertex) nil).
Proof.
  intros.
  unfold Hoare.
  unfold regexToNFA.
  split.
  - intros.
    unfold act_singleton.
    unfold StateRelMonad.err.
    intros contra.
    destruct contra.
    + unfold get_new_vertex in H0.
      unfold StateRelMonad.err in H0.
      tauto.
    + destruct H0.
      destruct H0 as [].
      destruct H0.
      unfold StateRelMonad.err in H1.
      destruct H1.
      * unfold get_new_vertex in H1.
        unfold StateRelMonad.err in H1.
        tauto.
      * destruct H1. 
        destruct H1 as [].
        destruct H1.
        unfold StateRelMonad.err in H2.
        destruct H2.
        -- unfold StateRelMonad.err in H2.
           unfold graph_constr in H2.
           destruct H2.
           ++ unfold StateRelMonad.err in H2.
              destruct H2.
           ++ destruct H2.
              destruct H2 as [].
              destruct H2.
              unfold StateRelMonad.err in H3.
              unfold StateRelMonad.nrm in H2.
              simpl in H2.
              destruct H2.
              destruct H3.
              ** unfold StateRelMonad.nrm in H0.
                 destruct H0.
                 destruct H5.
                 unfold StateRelMonad.nrm in H1.
                 destruct H1.
                 destruct H7.
                 rewrite H1 in H8.
                 simpl in H8.
                 rewrite <- H6 in H8.
                 destruct H2.
                 destruct add_vertex_pg0.
                 unfold empty_nfa in add_vertex_vertex.
                 destruct add_vertex_vertex.
                 simpl in H9.
                 unfold G_add_vertex in H3.
                 unfold StateRelMonad.err in H3.
                 apply H9 in H3.
                 destruct H3.
                 --- tauto.
                 --- rewrite H8 in H3.
                     unfold Sets.singleton in H3.
                     lia.
              ** destruct H3.
                 destruct H3 as [].
                 destruct H3.
                 unfold StateRelMonad.err in H5.
                 unfold graph_constr_rec in H5.
                 destruct H5.
                 --- tauto.
                 --- destruct H5.
                     destruct H5 as [].
                     destruct H5.
                     unfold StateRelMonad.err in H6.
                     destruct H6.
                     +++ unfold G_add_edge in H6.
                         unfold StateRelMonad.err in H6.
                         unfold StateRelMonad.nrm in H3.
                         unfold G_add_vertex in H3.
                         destruct H3.
                         destruct H3.
                         destruct add_vertex_pg0.
                         apply add_vertex_edge in H6.
                         destruct H2.
                         destruct add_vertex_pg0.
                         apply add_vertex_edge0 in H6.
                         simpl in H6.
                         tauto.
                    +++ destruct H6.
                        destruct H6.
                        destruct H6.
                        tauto.
        -- destruct H2.
           destruct H2 as [].
           destruct H2.
           unfold ret_nfa in H3.
           tauto.
  - intros.
 unfold StateRelMonad.nrm in H0.
      destruct H0.
      destruct H0 as [].
      destruct H0.
      unfold StateRelMonad.nrm in H1.
      destruct H1.
      destruct H1 as [].
      destruct H1.
      unfold StateRelMonad.nrm in H2.
      destruct H2.
      destruct H2 as [].
      destruct H2.
      destruct H3.
      rewrite H3.
      simpl.
      destruct H2.
      destruct H2 as [].
      destruct H2.
      destruct H5.
      destruct H5 as [].
      destruct H5.
      destruct H6.
      destruct H6.
      destruct H6.
      unfold StateRelMonad.nrm in H7.
      destruct H7.
      destruct H7.
      destruct H7.
      destruct H7.
      destruct H7.
      destruct add_edge_pg0.
      destruct H8.
      rewrite H7.
      unfold e_steps.
      unfold e_step.
      unfold clos_refl_trans.
      unfold Sets.indexed_union.
      simpl.
      exists Nat.one.
      unfold nsteps.
      simpl. 
      unfold Rels.id.
      simpl.
      sets_unfold.
      exists x1.
      split.
      * exists x9.
        split.
        -- split.
           
           ++ unfold StateRelMonad.nrm in H5.
              destruct H5.
              destruct H5.
              destruct add_vertex_pg0.
              unfold StateRelMonad.nrm in H2.
              destruct H2.
              destruct H2.
              destruct add_vertex_pg0.
              unfold Sets_disjoint_union in add_edge_edge.
              destruct add_edge_edge.
              rewrite <- add_vertex_edge in H2.
              rewrite <- add_vertex_edge in H11.
              rewrite <- add_vertex_edge0 in H2.
              rewrite <- add_vertex_edge0 in H11.
              simpl in H2.
              simpl in H11.
              apply H11.
              sets_unfold.
              tauto.
          ++  unfold StateRelMonad.nrm in H5.
              destruct H5.
              destruct H5.
              destruct add_vertex_pg0.
              unfold StateRelMonad.nrm in H2.
              destruct H2.
              destruct H2.
              destruct add_vertex_pg0.
              unfold Sets_disjoint_union in add_vertex_vertex.
              destruct add_vertex_vertex.
              unfold Sets_disjoint_union in add_vertex_vertex0.
              destruct add_vertex_vertex0.
              rewrite <- H13 in H11.
              apply add_edge_vertex.
              apply H11.
              sets_unfold.
              tauto.
          ++ 
              unfold StateRelMonad.nrm in H5.
              destruct H5.
              destruct H5.
              destruct add_vertex_pg0.
              unfold StateRelMonad.nrm in H2.
              destruct H2.
              destruct H2.
              destruct add_vertex_pg0.
              unfold Sets_disjoint_union in add_vertex_vertex.
              destruct add_vertex_vertex.
              unfold Sets_disjoint_union in add_vertex_vertex0.
              destruct add_vertex_vertex0.
              rewrite <- H13 in H11.
              apply add_edge_vertex.
              apply H11.
              sets_unfold.
              tauto.
          ++  tauto.
          ++  tauto.
        --  tauto.
      * tauto.
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


Lemma vvalid_range :
  forall {T: Type} (elem1: elem T) (s1 s2: state) (r: reg_exp T),
  (s1, elem1, s2) ∈ (regexToNFA r).(nrm) ->
  forall gv, gv ∈ elem1.(graph).(pg).(vvalid) -> s1.(max_v) < gv <= s2.(max_v).
Proof.
  intros.
  induction r.
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
      



        
  - unfold StateRelMonad.err in H.
    sets_unfold in H.
    unfold regexToNFA in H.
    destruct H.
    + unfold StateRelMonad.err in H.
      destruct H.
    + destruct H.
      destruct H.
      destruct H.
      unfold StateRelMonad.err in H0.
      destruct H0.
      unfold StateRelMonad.err in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H0.
      unfold StateRelMonad.err in H1.
      destruct H1.
      * unfold StateRelMonad.err in H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H2.
        --  unfold StateRelMonad.err in H2.
            simpl in H2.
            sets_unfold in H2.
            destruct H1.
            destruct H1.
            destruct add_vertex_pg0.
            unfold Sets_disjoint_union in add_vertex_vertex;destruct add_vertex_vertex.
            unfold empty_nfa in H4.
            simpl in H4.
            apply H4 in H2.
            unfold Sets.singleton in H2.
            sets_unfold in H2.
            destruct H0.
            destruct H.
            destruct H5.
            rewrite H0 in H7.
            destruct H6.
            rewrite <- H8 in H7.
            destruct H2.
            ++  tauto.
            ++  lia.
        --  destruct H2.
            destruct H2.
            destruct H2.
            destruct H3.
            ++  destruct H3.
            ++  destruct H3.
                destruct H3.
                destruct H3.
                destruct H4.
                **  unfold StateRelMonad.err in H4.
                    simpl in H4.
                    sets_unfold in H4.
                    destruct H1.
                    destruct H2.
                    destruct H1.
                    destruct H2.
                    destruct add_vertex_pg0.
                    destruct add_vertex_pg1.
                    apply add_vertex_edge0 in H4.
                    apply add_vertex_edge in H4.
                    unfold empty_nfa in H4.
                    simpl in H4.
                    tauto.
                **  destruct H4.
                    destruct H4.
                    destruct H4.
                    tauto.
      * destruct H1.
        destruct H1.
        destruct H1.
        destruct H2.
  - unfold StateRelMonad.err in H.
    sets_unfold in H.
    unfold regexToNFA in H.
    destruct H.
    + unfold StateRelMonad.err in H.
      destruct H.
    + destruct H.
      destruct H.
      destruct H.
      unfold StateRelMonad.err in H0.
      destruct H0.
      unfold StateRelMonad.err in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H0.
      unfold StateRelMonad.err in H1.
      destruct H1.
      * unfold StateRelMonad.err in H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H1.
        destruct H2.
        --  unfold StateRelMonad.err in H2.
            simpl in H2.
            sets_unfold in H2.
            destruct H1.
            destruct H1.
            destruct add_vertex_pg0.
            unfold Sets_disjoint_union in add_vertex_vertex;destruct add_vertex_vertex.
            unfold empty_nfa in H4.
            simpl in H4.
            apply H4 in H2.
            unfold Sets.singleton in H2.
            sets_unfold in H2.
            destruct H0.
            destruct H.
            destruct H5.
            rewrite H0 in H7.
            destruct H6.
            rewrite <- H8 in H7.
            destruct H2.
            ++  tauto.
            ++  lia.
        --  destruct H2.
            destruct H2.
            destruct H2.
            destruct H3.
            ++  destruct H3.
            ++  destruct H3.
                destruct H3.
                destruct H3.
                destruct H4.
                **  unfold StateRelMonad.err in H4.
                    simpl in H4.
                    sets_unfold in H4.
                    destruct H1.
                    destruct H2.
                    destruct H1.
                    destruct H2.
                    destruct add_vertex_pg0.
                    destruct add_vertex_pg1.
                    apply add_vertex_edge0 in H4.
                    apply add_vertex_edge in H4.
                    unfold empty_nfa in H4.
                    simpl in H4.
                    tauto.
                **  destruct H4.
                    destruct H4.
                    destruct H4.
                    tauto.
      * destruct H1.
        destruct H1.
        destruct H1.
        destruct H2.
  - unfold StateRelMonad.err in H.
    sets_unfold in H.
    unfold regexToNFA in H.
    destruct H.
    + apply IHr1_1 in H.
      tauto.
    + destruct H.
      destruct H.
      destruct H.
      Admitted.
    + unfold StateRelMonad.nrm in H0.
      unfold state.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      destruct H1.
      destruct H1.
      destruct H2.
      destruct H2.
      destruct H2.
 
      destruct H0.
      destruct H4.
      destruct H1.
      destruct H6.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H2.
      destruct H8.
      destruct H8.
      destruct H8.
      destruct H8.
      destruct H10.
      destruct H10.
      destruct H10.
      destruct H10.
      destruct H10.
      destruct H12.
      destruct H10.
      destruct H10.
      destruct H10.
      destruct H12.
      destruct H3.
      destruct H13.

      unfold Rels.concat.
      simpl.

      apply rt_trans_n1.
      subst.
      
      
      unfold Sets.indexed_union.
      unfold nsteps.
      simpl.
      
      
      

      
      
      
      

      


      rewrite H6.
      destruct H5.
      destruct H5.
      destruct add_vertex_pg0.
      apply add

      unfold string_step.
      unfold e_steps.
      
                    
                     
                       
                 
              tauto.

        tauto. 
      tauto.

      intros contra.
      destruct contra.
      tauto.
      case H1.
      * intros.
      unfold graph_constr in H0.
      unfold StateRelMonad.err in H0.
      tauto.
    
    + destruct H0.
      unfold get_new_vertex in
    destruct.
    intros.
    simpl.
    inversion H0; subst.
    unfold ret_nfa in H2.
    simpl in H2.
    inversion H2; subst.
    repeat match goal with
            | H : context [bind _ _] |- _ => simpl in H
            | H : context [get_new_vertex] |- _ => simpl in H
            | H : context [graph_constr _] |- _ => simpl in H
            end.
    subst.
    split.
    + simpl. reflexivity.
    + reflexivity.
Qed.
    




