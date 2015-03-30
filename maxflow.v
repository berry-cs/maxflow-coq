
Require Import Ascii.
Require Import List.
Require Import Le.
Import ListNotations.

(* an edge in the residual graph *)
Record REdge : Set := mk_redge
                        { rsrc : ascii;
                          rdst : ascii;
                          rcap : nat }.

Check (mk_redge "S" "V" 10).

(* an edge in the full graph *)

Record Edge : Set := mk_edge
                       { src : ascii;
                         dst : ascii;
                         cap : nat;
                         flow : nat }.

Definition Graph := list Edge.

Definition RGraph := list REdge.


(* examples *)

Definition G : Graph
  := [ mk_edge "S" "U" 20 0 ;
       mk_edge "S" "V" 10 0 ;
       mk_edge "U" "V" 30 0 ;
       mk_edge "U" "T" 10 0 ;
       mk_edge "V" "T" 20 0
     ].

Definition Gf : RGraph
  := [ mk_redge "S" "U" 20 ;
       mk_redge "S" "V" 10 ;
       mk_redge "U" "V" 30 ;
       mk_redge "U" "T" 10 ;
       mk_redge "V" "T" 20 ].



(*
Fixpoint bottleneck (fst:REdge)
                    (rst : list REdge) : nat
  := match rst with
       | [] => rcap fst
       | h::t => min (rcap fst)
                     (bottleneck h t)
     end.
 *)

Fixpoint bottleneck (res:list REdge) : nat :=
  match res with
    | [] => 0
    | h :: [] => rcap h
    | h::t => min (rcap h)
                  (bottleneck t)
  end.


(* 
If bottleneck (re::res) produces n, then
n is less than/equal the capacity of every
edge in the list (re::res).
*)
Lemma bottleneck_picks_min :
  forall res re n,
    bottleneck (re::res) = n ->
    forall re', In re' (re :: res) ->
                n <= rcap re'.
Proof.
  intros res.
  induction res as [ | h t ].
  (* Case res = [] *)
  simpl.
  intros res n Hc re' Hin.
  destruct Hin.
  rewrite <- H; rewrite <- Hc; trivial.
  inversion H.

  (* Case res = h :: t *)
  intros re n Hc re' Hin.
  assert (min (rcap re)
              (bottleneck (h::t)) = n)
  as Hc'; auto.
  assert (forall re'',
            In re'' (h :: t) ->
            bottleneck (h :: t) <= rcap re'').
    intros re'' HIn''.
    apply IHt with h; auto.

    assert (rcap re < bottleneck (h::t)
            \/ bottleneck (h::t) <= rcap re).

    
Qed.



(* end *)