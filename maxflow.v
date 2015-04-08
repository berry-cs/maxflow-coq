
Require Import Ascii.
Require Import List.
Require Import Le.
Require Import EqNat.
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

Definition blankREdge : REdge
  := mk_redge " " " " 0.

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
Require Import Compare_dec.

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

    destruct (le_lt_dec (rcap re) (bottleneck (h::t))) as [H1 | h1].

    replace(bottleneck(re :: h :: t)) with (min (rcap re) (bottleneck (h::t))) in Hc; auto.

    rewrite (min_l _ _ H1) in Hc.

    destruct Hin.
    rewrite <- Hc.
    rewrite H0.
    trivial.
    
    assert (bottleneck (h :: t) <= rcap re').
    apply H; auto.
    rewrite <- Hc.
    rewrite H1.
    auto.

    
    replace(bottleneck(re :: h :: t)) with (min (rcap re) (bottleneck (h::t))) in Hc; auto.
    rewrite (min_r (rcap re) (bottleneck (h::t))) in Hc; auto with arith.

    destruct Hin.
    rewrite <-H0.
    rewrite <-Hc'.
    auto with arith.
    rewrite <-Hc.
    apply H.
    auto.
    
Qed.


Fixpoint largest_cap (rG: RGraph) : nat :=
  match rG with
    |[] => 0
    |h :: [] => rcap h
    |h :: t => (max (rcap h) (largest_cap t))
  end.

Definition edge_equal (rE1 rE2: REdge) : bool :=
   (andb (beq_nat (nat_of_ascii (rsrc rE1)) (nat_of_ascii (rsrc rE2))) (beq_nat (nat_of_ascii (rdst rE1)) (nat_of_ascii (rdst rE2)))).

Fixpoint contains_edge (rG: RGraph) (rE: REdge) : bool :=
  match rG with
    |[] => false
    |h :: t => (orb (edge_equal h rE) (contains_edge t rE))
  end.


Definition non_zero_edge (rE: REdge) : bool :=
  (negb (beq_nat 0 (rcap rE))).

Fixpoint all_vert_paths (rG: RGraph) (v: ascii) : RGraph :=
  match rG with
    |[] => []
    | h :: t => if (beq_nat (nat_of_ascii v) (nat_of_ascii (rsrc h)))
                    then h :: (all_vert_paths t v)
                    else (all_vert_paths t v)
  end.

Fixpoint select_edge (rG: RGraph) (v: ascii) : REdge :=
  match rG with
    |[] => blankREdge
    |h :: t => if (beq_nat (rcap h) (largest_cap (all_vert_paths rG v)))
                    then h
                    else (select_edge t v)
  end.

Compute (select_edge Gf "S").

Fixpoint st_path (rG: RGraph) (v: ascii) : RGraph
    






    






(* End *)