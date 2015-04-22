
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
                               nodes : nat;
                               edges: list Edge
                              }.

Definition RGraph := list REdge.


(* examples *)

Definition G : Graph
  := mk_graph    "S"
                 "T"
                 4
              [ mk_edge "S" "U" 20 0 ;
                mk_edge "S" "V" 10 0 ;
                mk_edge "U" "V" 30 0 ;
                mk_edge "U" "T" 10 0 ;
                mk_edge "V" "T" 20 0
              ].

Definition RG : list REdge
  := [ mk_redge "S" "U" 20 true ;
       mk_redge "U" "T" 10 true ;
       mk_redge "S" "V" 10 true ;
       mk_redge "U" "V" 30 true ;
       mk_redge "V" "T" 20 true ].


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




Fixpoint nodes_of (Gf:list REdge) : list ascii :=
  match Gf with
    | nil => nil
    | (mk_redge s t n d) :: Gf' =>
      (cons s (cons t (nodes_of Gf')))
  end.

Goal nodes_of RG = [ "S" ; "U" ; "U" ; "T" ; "S" ; "V" ; "U" ; "V" ; "V" ; "T" ] % char.
auto. Qed.


(* st_path_valid Gf s t Es
 means that Es is a valid path from s to t in Gf

          s  \in  nodes_of Gf
   ------------------------------  spv_nil
     st_path_valid Gf s s empty


     e = redge s u
     e  \in  Gf
     st_path_valid Gf u t es
   ------------------------------------- spv_cons
     st_path_valid Gf s t (e :: es)

*)
Inductive st_path_valid : (list REdge) -> ascii -> ascii -> list REdge -> Prop :=
| spv_nil  : forall Gf s, In s (nodes_of Gf) -> st_path_valid Gf s s nil
| spv_cons : forall Gf s t u n d e es,
               e = mk_redge s u n d ->
               In e Gf ->
               st_path_valid Gf u t es ->
               st_path_valid Gf s t (e :: es).

Goal (st_path_valid RG "S" "T" [ (mk_redge "S" "U" 20 true) ; (mk_redge "U" "T" 10 true) ]).
Proof.
  apply spv_cons with "U"%char 20 true; simpl; auto.
  apply spv_cons with "T"%char 10 true; simpl; auto.
  apply spv_nil.
  simpl; auto.
Qed.




Fixpoint st_path (Gf: list REdge) (s t: ascii) (visited: list ascii) (n:nat) {struct n}
: option (list REdge) :=
  match n with
    | 0 => None
    | S n' =>
      if (member s visited) then None
      else
        (fix st_path_any (s_edges : list REdge) (visited:list ascii) 
         : option (list REdge) :=
           match s_edges with
             | [] => None
             | fst::rst =>
               if (ascii_dec (rdst fst) t)
               then Some (fst::nil)
               else 
               match st_path Gf (rdst fst) t visited n' with
                 | None => st_path_any rst ((rdst fst) :: visited) 
                 | Some pth => Some (fst :: pth)
               end
           end)
          (find_outgoing Gf s) (s::visited)
  end.
Compute (st_path RG "S" "T" nil 4).



Lemma st_path_correct :
  forall n ns Gf s t vs es,
    nodes_of Gf = ns ->
    incl vs ns ->
    n > length ns ->
    st_path Gf s t vs n = Some es ->
    st_path_valid Gf s t es.
Proof.     
  induction n.
  intros.
  inversion H1.

  intros ns Gf s t vs es H1 H2 H3 H4.
  simpl in H4.
  replace (member s vs) with false in H4;
    [ idtac |
      destruct (member s vs); auto; inversion H4
                                              ].

  assert (exists lo, lo = find_outgoing Gf s).
  exists (find_outgoing Gf s); auto.
  destruct H as [lo Hlo].
  rewrite <- Hlo in H4.
  induction lo as [ | oe lo' ].
  inversion H4.
  destruct (ascii_dec (rdst oe) t).
  inversion H4.
  apply spv_cons with t (rcap oe) (dir oe); auto.
   (* show that e = ... *)
  rewrite <- e.
  replace s with (rsrc oe).
  destruct oe; simpl; auto.

Lemma find_outgoing_src
: forall Gf s lo, find_outgoing Gf s = lo ->
                  forall oe, In oe lo -> rsrc oe = s.
Proof.
  induction Gf as [| fst rst].
  intros.
  simpl in H.
  rewrite <- H in H0.
  inversion H0.

  (* Gf = fst :: rst *)
  simpl.
  intros s lo H.
  destruct (ascii_dec (rsrc fst) s).

  rewrite <- H; simpl; intros oe Hin.
  destruct lo as [ | oe' lo'].
  discriminate H. (* lo cannot be empty *)
  destruct Hin as [Hin1 | Hin2].
  rewrite <- Hin1; auto.
  apply IHrst with (find_outgoing rst s); auto.

  (* here rsrc fst <> s *)
  apply IHrst.
  trivial.
Qed.

  
  apply find_outgoing_src with Gf (oe :: lo'); auto.
  unfold In.
  left; auto.

  (* show e  \in  Gf , from the spv_cons rule *)

  Lemma find_outgoing_in : forall Gf s lo,
                             find_outgoing Gf s = lo ->
                             forall oe, In oe lo -> In oe Gf.
  Proof.
    induction Gf as [ | e Gf'].
    simpl.
    intros s lo H1 oe H2.
    rewrite <- H1 in H2; inversion H2.

    intros s lo H1 oe H2.
    simpl in H1.
    destruct (ascii_dec (rsrc e) s).
    
    (* case rsrc e = s *)
    simpl.
    rewrite <- H1 in H2.
    inversion H2.
    left; auto.
    right; apply IHGf' with s (find_outgoing Gf' s); auto.

    (* case rsrc e <> s *)
    simpl.
    right.
    apply IHGf' with s lo; auto.
Qed.

  apply find_outgoing_in with s (oe :: lo'); auto.
  left; auto.
  apply spv_nil; auto.

  assert (In oe Gf).
  apply find_outgoing_in with s (oe :: lo'); auto.
  left; auto.

  Lemma nodes_of_in :
    forall Gf oe,
      In oe Gf ->
      In (rsrc oe) (nodes_of Gf) /\ In (rdst oe) (nodes_of Gf).
Admitted.
  
  destruct (nodes_of_in Gf oe); auto.
  replace t with (rdst oe); auto.

Qed.




Theorem path_none_lt_n : forall s t : ascii, forall G : Graph, forall visited : list ascii, (st_path (graph_residual G) s t visited (nodes G)) = None -> (lt (length visited) (nodes G)).   
(*
REMOVED
Fixpoint st_path_any (Gf s_edges: list REdge) (t: ascii) (visited: list ascii)
   : option (list REdge) :=
  match s_edges with
    |[] => None
    |fst ::rst => if(ascii_dec (rdest fst) t)
              then (list (rsrc fst))
              else match st_path Gf (rdst fst) t visited with
                     | None => (st_path_any Gf rst t  (rdst fst) :: visited)
                     | Some (head::tail) => Some (fst::head::tail
                   end
  end.
*)

Fixpoint main_loop (G: Graph) (Gf: list REdge) : Graph :=
 match  st_path Gf (source G) (sink G) [] (S (nodes G)) with
         |None => G
         |Some pth =>  main_loop (mk_graph (source G) (sink G) (nodes G) (augment (edges G) 
                                        pth) )
                                        (graph_residual (augment (edges G)
                                        pth))
 end.
         
         
Definition max_flow (G: Graph) : Graph :=
  (main_loop G (graph_residual (edges G))).







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