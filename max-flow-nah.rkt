#lang racket

(require test-engine/racket-tests)


;; -------------------------------------------------------------------
;; -------------------------------------------------------------------
;;                       ____________________
;;                      /\                   \
;;                      \_| DATA DEFINITIONS |
;;                        |                  |
;;                        |   _______________|_
;;                        \_/_________________/
;;
;; -------------------------------------------------------------------
;; -------------------------------------------------------------------

;; A Node is a natural number
;; Capacity, Flow are natural numbers

(define-struct edge (src dest cap flow) #:transparent)
;; an edge in the graph, with total capacity, and current flow

(define-struct graph (source sink nodes edges) #:transparent)
;; A Graph is (graph node node (listof edge))


(define-struct redge (src dest cap fwd?) #:transparent)
;; represents an edge in the residual graph
;; we represent a residual graph implicitly as a list of redges

;; A Path is (ne-listof redge)    (non-empty)
;; represents a path in a residual graph


;; A [Maybe X] is either:
;;  - false, or
;;  - X




;; -------------------------------------------------------------------
;; -------------------------------------------------------------------
;;                       ____________________
;;                      /\                   \
;;                      \_| SAMPLE GRAPH     |
;;                        |                  |
;;                        |   _______________|_
;;                        \_/_________________/
;;
;; -------------------------------------------------------------------
;; -------------------------------------------------------------------


(define S 0)
(define T 1)
(define U 2)
(define V 3)

(define G1 (graph S T 4
                  (list (make-edge S U 20 0)
                        (make-edge U T 10 0)
                        (make-edge S V 10 0)
                        (make-edge U V 30 0)
                        (make-edge V T 20 0))))
(define RG1 (list (make-redge S U 20 true)
                 (make-redge U T 10 true)
                 (make-redge S V 10 true)
                 (make-redge U V 30 true)
                 (make-redge V T 20 true)))
(define P1 (list (make-redge S U 20 true)
                 (make-redge U V 30 true)
                 (make-redge V T 20 true)))

(define G1a (graph S T 4
                   (list (make-edge S U 20 20)
                         (make-edge U T 10 0)
                         (make-edge S V 10 0)
                         (make-edge U V 30 20)
                         (make-edge V T 20 20))))
(define RG1a (list (make-redge U S 20 false)
                 (make-redge U T 10 true)
                 (make-redge S V 10 true)
                 (make-redge V U 20 false)
                 (make-redge U V 10 true)
                 (make-redge T V 20 false)))
(define P1a (list (make-redge S V 10 true)
                  (make-redge V U 20 false)
                  (make-redge U T 10 true)))




;; -------------------------------------------------------------------
;; -------------------------------------------------------------------
;;                       ____________________
;;                      /\                   \
;;                      \_| THE ALGORITHM    |
;;                        |                  |
;;                        |   _______________|_
;;                        \_/_________________/
;;
;; -------------------------------------------------------------------
;; -------------------------------------------------------------------



;; max-flow : Graph -> Graph
;; computes the max flow along given graph

(check-expect (max-flow G1)
              (graph S T 4
                     (list (make-edge S U 20 20)
                           (make-edge U T 10 10)
                           (make-edge S V 10 10)
                           (make-edge U V 30 10)
                           (make-edge V T 20 20))))

(define (max-flow G)
  (define Gf (graph->residual (graph-edges G)))
  (main-loop G Gf))



;; main-loop : Graph (listof redge) -> Graph
;; finds an s-t path in the residual graph Gf,  uses it to augment the
;; graph G, and recomputes the residual graph before repeating the process
;; produces the graph G, with no further changes, if no path is found
(define (main-loop G Gf)
  (define P (st-path Gf (graph-source G) (graph-sink G) '() (graph-nodes G)))
  (cond
    [(false? P) G]
    [else
     (define newGedges (augment (graph-edges G) P))
     (define newGf (graph->residual newGedges))
     (main-loop (graph (graph-source G) (graph-sink G) (graph-nodes G) newGedges) newGf)]))




;; update-edge-flow : (listof edge) Node Node Number -> (listof edge)
;; adds the given amount to the edge between n1 and n2 in the graph's edges

(check-expect (update-edge-flow (graph-edges G1) S V 10)
              (list (make-edge S U 20 0)
                 (make-edge U T 10 0)
                 (make-edge S V 10 10)
                 (make-edge U V 30 0)
                 (make-edge V T 20 0)))
(check-expect (update-edge-flow (graph-edges G1a) U V -10)
              (list (make-edge S U 20 20)
                 (make-edge U T 10 0)
                 (make-edge S V 10 0)
                 (make-edge U V 30 10)
                 (make-edge V T 20 20)))

(define (update-edge-flow G s t amt)
  (match G
    ['() '()]   ;; really shouldn't  happen
    [(cons (edge n1 n2 cap flw) rst)
     (if (and (= s n1) (= t n2))
         (cons (edge n1 n2 cap (+ flw amt)) rst)
         (cons (edge n1 n2 cap flw) 
               (update-edge-flow rst s t amt)))]))




;; augment : (listof edge) Path -> (listof edge)
;; computes the bottleneck along the given path and uses that amount
;; to augment all edges in the graph along that path
(check-expect (augment (graph-edges G1a) P1a)
              (list (make-edge S U 20 20)
                    (make-edge U T 10 10)
                    (make-edge S V 10 10)
                    (make-edge U V 30 10)
                    (make-edge V T 20 20)))

(define (augment G P)
  (augment/amt G P (bottleneck P)))




;; augment/amt : Graph Path Number -> Graph
;; augments all edges in the path by the given amount

(define (augment/amt G P amt)
  (match P
    ['() G]
    [(cons (redge n1 n2 cap #t) rst)
     (augment/amt (update-edge-flow G n1 n2 amt) rst amt)]
    [(cons (redge n1 n2 cap #f) rst)
     (augment/amt (update-edge-flow G n2 n1 (- amt)) rst amt)]))




;; bottleneck : Path -> Number
;; compute the largest possible magnitude of flow along the
;; given path of residual edges
(check-expect (bottleneck P1) 20)
(check-expect (bottleneck P1a) 10)
(check-expect (bottleneck (list (redge 0 2 20 #t) (redge 2 1 10 #t))) 10)

(define (bottleneck P)
  (match P
    [(cons (redge n1 n2 cap fw?) '()) cap]
    [(cons (redge n1 n2 cap fw?) rst)
     (min cap (bottleneck rst))]))




;; graph->residual : (listof edge) -> (listof redge)
;; compute the residual graph given a graph with capacities and flows
(check-expect (graph->residual (graph-edges G1)) RG1)
(check-expect (graph->residual (graph-edges G1a)) RG1a)

(define (graph->residual G)
  (match G 
    ['() '()]
    [(cons (edge n1 n2 cap flw) rst)
     (define Gf-rst (graph->residual rst))
     (define Gf-fwd
       (if (< flw cap)
           (cons (redge n1 n2 (- cap flw) true) Gf-rst)
           Gf-rst))
     (define Gf-bkwd
       (if (> flw 0)
           (cons (redge n2 n1 flw false) Gf-fwd)
           Gf-fwd))
     Gf-bkwd]))




;; st-path : (listof redge) Node Node (listof Node) -> [Maybe Path]
;; finds any path from s to t in the given list of redges (residual graph)
;; succeeds if there is a path, that does not pass through any of the visited
;; list of nodes
(check-expect (st-path RG1 S T empty 4)
              (list  (redge 0 2 20 #t)
                     (redge 2 1 10 #t)))

(define (st-path Gf s t visited num-unvisited)
  ;; st-path/any : (listof redge) (listof redge) Node (listof Node) -> [Maybe Path]
  ;; finds a path from any of the outgoing edges from s to t, ...
  (define (st-path/any s-edges visited num-unvisited)
    (match s-edges
      ['() #f]
      [(cons (redge n1 n2 cap fw?) rst)
       (if (= n2 t)
           (list (first s-edges))
           (match (st-path Gf n2 t visited num-unvisited)
             [#f (st-path/any rst (cons n2 visited) (sub1 num-unvisited))]
             [lst (cons (first s-edges) lst)]))]))
  
  (cond
    [(= 0 num-unvisited) #f]
    [(member s visited) #f]
    [else 
     (define all-out (find-outgoing Gf s))
     (st-path/any all-out (cons s visited) (sub1 num-unvisited))]))

       
     

;; find-outgoing : (listof redge) Node (listof Node) -> (listof redge)
;; produce a list of all outgoing nodes from the given node

(define (find-outgoing Gf s )
  (match Gf
    ['() '()]
    [(cons (redge n1 n2 cap fw?) rst)
     (if (= s n1)
         (cons (first Gf) (find-outgoing rst s ))
         (find-outgoing rst s ))]))



;; test from:
;;    http://www.geeksforgeeks.org/ford-fulkerson-algorithm-for-maximum-flow-problem/

(check-expect 
 (max-flow (graph 0 5 6
                  (list (edge 0 1 16 0)
                        (edge 0 2 13 0)
                        (edge 1 2 10 0)
                        (edge 2 1 4 0)
                        (edge 1 3 12 0)
                        (edge 2 4 14 0)
                        (edge 3 2 9 0)
                        (edge 4 3 7 0)
                        (edge 3 5 20 0)
                        (edge 4 5 4 0))))
 (graph 0 5 6
        (list (edge 0 1 16 16) ; this is slightly different
              (edge 0 2 13 7)  ; than the solution on that web
              (edge 1 2 10 4)  ; page, but gives the same max flow 
              (edge 2 1 4 0)   ; value, and I think everything works out
              (edge 1 3 12 12)
              (edge 2 4 14 11)
              (edge 3 2 9 0)
              (edge 4 3 7 7)
              (edge 3 5 20 19)
              (edge 4 5 4 4))))



(test)






