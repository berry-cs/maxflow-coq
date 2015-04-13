
Require Import Ascii.
Require Import List.
Require Import Le.
Require Import EqNat.
Import ListNotations.            
(* an edge in the residual graph *)
Record REdge : Set := mk_redge
                        { rsrc : ascii;
                          rdst : ascii;
                          rcap : nat;
                          dir  : bool}.

Check (mk_redge "S" "V" 10 true).
                              
                               
(* an edge in the full graph *)

Record Edge : Set := mk_edge
                       { src : ascii;
                         dst : ascii;
                         cap : nat;
                         flow : nat }.

Record Graph : Set := mk_graph
                             { source : ascii;
                               sink : ascii;
                               edges: list Edge
                              }.

Definition RGraph := list REdge.


(* examples *)

Definition G : Graph
  := mk_graph    "S"
                 "T"    
              [ mk_edge "S" "U" 20 0 ;
                mk_edge "S" "V" 10 0 ;
                mk_edge "U" "V" 30 0 ;
                mk_edge "U" "T" 10 0 ;
                mk_edge "V" "T" 20 0
              ].


Definition blankREdge : REdge
  := mk_redge " " " " 0 false.

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

Fixpoint find_outgoing (Gf: list REdge) (s:ascii) : list REdge :=
     match Gf with
        |[] => []
        |h :: t => if(ascii_dec (rsrc h) s)
                   then ( h :: (find_outgoing t s))
                   else (find_outgoing t s)
     end.


Fixpoint member (s: ascii) (visited: list ascii) : bool :=
  match visited with
    |[] => false
    |h :: t => if(ascii_dec h s)
               then true
               else (member s t)
  end.

SearchAbout nat.
           


Fixpoint graph_residual (G: list Edge) : list REdge :=
  match G with
    |[] => []
    |h::t => if (lt_dec (flow h) 0)
             then (mk_redge (dst h) (src h) (flow h) false)  ::
                    if(lt_dec (flow h) (cap h))
                    then(mk_redge (dst h) (src h) ((cap h) -(flow h)) true) ::
                    (graph_residual t)
                    else (graph_residual t)
             else (if (lt_dec (flow h) (cap h))
                    then(mk_redge (dst h) (src h)  ((cap h)- (flow h)) true) ::
                      (graph_residual t)
                    else (graph_residual t))
  end.

Fixpoint update_edge_flow (G: list Edge) (s t: ascii) (amt: nat) : list Edge :=
  match G with
    |[] => []
    |head :: tail => if (ascii_dec s (src head))
                  then(if (ascii_dec t (dst head))
                       then (mk_edge (src head) (dst head) (cap head) ((flow head) + amt))                              :: tail
                       else (head :: (update_edge_flow tail s t amt)))
                  else (head :: (update_edge_flow tail s t amt)) 
  end.
    

Fixpoint augment_amt (G: list Edge) (P: list REdge) (amt: nat) : list Edge :=
  match P with
    |[] => G
    |h :: t => if (dir h)
               then (augment_amt (update_edge_flow G (rsrc h) (rdst h) amt) t amt)
               else (augment_amt (update_edge_flow G (rsrc h) (rdst h) (0 - amt)) t amt)
  end.

Definition augment (G: list Edge) (P: list REdge) : list Edge :=
  (augment_amt G P (bottleneck P)).

Fixpoint main_loop (G: Graph) (Gf: list REdge) : Graph :=
 match (st_path Gf (source G) (sink G) []) with
         |false => G
         |h :: t => (main_loop (mk_graph (source G) (sink G) (augment (edges G)
                                         (st_path Gf (source G) (sink G) []))
                                         (graph_residual (augment (edges G)
                                         (st_path Gf (source G) (sink G) [])))))
 end.
         
         
Definition max_flow (G: Graph) : Graph :=
  (main_loop G (graph_residual (edges G))).



Fixpoint st_path_any (Gf s_edges: list REdge) (t: ascii) (visited: list ascii) : list REdge \/ bool :=
  match s_edges with
    |[] => false
    |fst ::rst => if(ascii_dec (rdest fst) t)
              then (list (rsrc fst))
              else match st_path Gf (rdest fst) t visited with
                     |false => (st_path_any Gf rst t  (rdst fst) :: visited)
                     |head::tail => fst::head::tail
                   end
  end.

Definition st_path (Gf: list REdge) (s t: ascii) (visited: list ascii) : list REdge \/ bool :=
  if(member s visited)
  then false
         else (st_path_any Gf (find_outgoing Gf s) t s::visited).




Fixpoint largest_cap (rG: RGraph) : nat :=
  match rG with
    |[] => 0
    |h :: [] => rcap h
    |h :: t => (max (rcap h) (largest_cap t))
  end.

Definition edge_equal (rE1 rE2: REdge) : bool :=
  if(ascii_dec (rsrc rE1)(rsrc rE2))
   then if (ascii_dec (rdst rE1) (rdst rE2))
        then true
        else false
    else false.

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
    | h :: t => if (ascii_dec v (rsrc h))
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


Fixpoint find_edge (rG: RGraph) (rE: REdge) : REdge :=
  match rG with
    |[] => blankREdge
    |h :: t => if(edge_equal h rE)
               then h
               else (find_edge t rE)
  end.

Definition reduce_by_REdge (rE: REdge) (n : nat) : REdge :=
  (mk_redge (rsrc rE) (rdst rE) ((rcap rE)-n)).







    






(* End *)