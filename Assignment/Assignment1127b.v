Require Import Coq.Lists.List.
Import ListNotations.

(************)
(** 习题：  *)
(************)

(** 下面定义的_[suffixes]_函数计算了一个列表的所有后缀。*)

Fixpoint suffixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l' => l :: suffixes l'
  end.

(** 例如 
   
        suffixes []           = [ [] ]
        suffixes [1]          = [ [1]; [] ]
        suffixes [1; 2]       = [ [1; 2]; [2]; [] ]
        suffixes [1; 2; 3; 4] = [ [1; 2; 3; 4];
                                  [2; 3; 4]   ;
                                  [3; 4]      ;
                                  [4]         ;
                                  []          ]
      
    接下去，请分三步证明，_[suffixes l]_中的确实是_[l]_的全部后缀。*)

Lemma self_in_suffixes:
  forall A (l: list A), In l (suffixes l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_suffixes:
  forall A (l1 l2: list A),
    In l2 (suffixes (l1 ++ l2)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_suffixes_inv:
  forall A (l2 l: list A),
    In l2 (suffixes l) ->
    exists l1, l1 ++ l2 = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 下面定义的_[prefixes]_函数计算了一个列表的所有前缀。*)

Fixpoint prefixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l0 => nil :: (map (cons a) (prefixes l0))
  end.

(** 例如：
   
        prefixes [1; 2]    = [ []     ;
                               [1]    ;
                               [1; 2] ] 
   
        prefixes [0; 1; 2] = [] ::
                             map (cons 0 (prefixes [1; 2]))
                           = [] ::
                             [ 0 :: []     ;
                               0 :: [1]    ;
                               0 :: [1; 2] ]
                           = [ []        ;
                               [0]       ;
                               [0; 1]    ;
                               [0; 1; 2] ]
      
    接下去，请分三步证明，_[prefixes l]_中的确实是_[l]_的全部前缀。*)

Lemma nil_in_prefixes:
  forall A (l: list A), In nil (prefixes l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_prefixes:
  forall A (l1 l2: list A),
    In l1 (prefixes (l1 ++ l2)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_prefixes_inv:
  forall A (l1 l: list A),
    In l1 (prefixes l) ->
    exists l2, l1 ++ l2 = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


