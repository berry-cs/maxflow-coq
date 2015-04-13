

(* Section 14.3 *)

Inductive ntree (A : Set) : Set :=
               nnode: A -> nforest A ->  ntree A
with nforest (A : Set) : Set :=
          nnil: nforest A
         | ncons: ntree A -> nforest A ->  nforest A.

Fixpoint count (A:Set) (t:ntree A) : nat :=
  match t with
    | nnode a l => 1 + count_list A l
  end
with
count_list (A:Set) (l:nforest A) : nat :=
    match l with
      | nnil => 0
      | ncons t tl => count A t + count_list A tl
    end.
