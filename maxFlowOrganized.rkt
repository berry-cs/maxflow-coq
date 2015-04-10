;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname maxFlowOrganized) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f ())))
; residual edge in a residual Graph
; a residual edge is a starting point, ending point, and a capacity
(define-struct REdge (start end capacity))

; edge in a normal Graph
; a edge is a starting point, ending point, a capacity, and a current flow
(define-struct Edge (start end capacity flow))

; a graph is a list of Edges 
; original graph
(define G (list (make-Edge "S" "U" 20 0)
                (make-Edge "S" "V" 10 0)
                (make-Edge "U" "V" 30 0)
                (make-Edge "U" "T" 10 0)
                (make-Edge "V" "T" 20 0)))

; a RGraph is a list of REdges
; residual graph
(define Gf (list (make-REdge "S" "U" 20)
                (make-REdge "S" "V" 10)
                (make-REdge "U" "V" 30)
                (make-REdge "U" "T" 10)
                (make-REdge "V" "T" 20)))

(define Gf2 (list (make-REdge "U" "S" 20)
                (make-REdge "S" "V" 10)
                (make-REdge "U" "V" 10)
                (make-REdge "V" "U" 20)
                (make-REdge "U" "T" 10)
                (make-REdge "T" "V" 20)))



; a path is a list of edges

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Main-loop runs the whole algorithm
; main-loop; Graph -> Graph

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; updates the graph to represent the path taken by the algorithm
; update-graph: Graph -> Graph

; updates the residual graph to represent the path taken by the algorithm
; update-residual: RGraph -> RGraph


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; augment removes forward edges whos capacity has been reached. 
; augment: Graph Path bottleneck -> Graph


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;find-st-path finds a path from the S node to the T node and returns false if one couldnt be found. 
;find-st-path: RGraph -> Path

(check-expect (find-st-Path Gf)
              (list 
               (make-REdge "S" "U" 20)
               (make-REdge "U" "V" 30)
               (make-REdge "V" "T" 20)))

(check-expect (find-st-Path Gf2)
              (list 
               (make-REdge "S" "V" 10)
               (make-REdge "V" "U" 20)
               (make-REdge "U" "T" 10)))



(define (find-st-Path RG)
  (st-path RG "S" (list "S")))

;st-path looks for edges that havent already been searched over in an attempt to reach the T node. produces false if no edge can be found. 
;st-path: RGraph targetNode (List nodes) -> Path
(define (st-path RG atNode visited) 
  (local[
         (define selectedREdge (select-edge (all-node-paths RG atNode) visited))
           ]
  (cond
   [(equal? atNode "T") null] 
   [else
    (cons selectedREdge (st-path RG (REdge-end selectedREdge ) (cons atNode visited) )
           )])))


;all-node-paths finds our target node and produces a list of all the edges that radiate out from that node
;all-node-paths: RGraph target -> (list REdges)

(check-expect (all-node-paths Gf "S")
              (list 
                (make-REdge "S" "U" 20)
                (make-REdge "S" "V" 10)
                ))

(check-expect (all-node-paths Gf "U")
              (list 
                (make-REdge "U" "V" 30)
                (make-REdge "U" "T" 10)))

(check-expect (all-node-paths Gf "V")
              (list 
                (make-REdge "V" "T" 20)))

(define (all-node-paths RG node)
  (filter (lambda (x) (equal? node (REdge-start x))) RG))

;select-edge takes in a list of edges and produces the largest capacity edge unless it has already been traversed. produces false if no edge
;can be found
;select-edge: (list REdges) (list nodes) -> edge
(define (select-edge paths nodes)
  (local
    [(define uniquePaths (filter (lambda (RE) (not (contained-in-nodes RE nodes))) paths))]
      (select-edge-loop uniquePaths (largest-cap uniquePaths))
  ))

(check-expect (select-edge-loop 
               (list 
                (make-REdge "S" "U" 20)
                (make-REdge "S" "V" 10)
                ) 
               20)
                (make-REdge "S" "U" 20)
                )

;;(check-expect (select-edge-loop 
;;               (list 
;;                (make-REdge "S" "U" 20)
;;                (make-REdge "S" "V" 10)
;;                ) 
;;               30)
;;                (make-REdge "S" "U" 20)
;;               )


(define (select-edge-loop paths cap)
  (cond
    [(empty? paths) false]
    [else (if (equal? cap (REdge-capacity (first paths)))
              (first paths)
              (select-edge-loop (rest paths)))]
  ))

  
 ;;(first (filter (lambda (x) (= (REdge-capacity x) 
 ;;                    (largest-cap paths))) paths)))

;largest-cap searches for the largest capacity on a list of edges. returns false if there isnt any paths in the list.
;largest-cap: (list REDges) -> nat

(check-expect (largest-cap Gf)
              30)

(check-expect (largest-cap
              (list 
               (make-REdge "S" "U" 20)
               (make-REdge "U" "V" 10)
               (make-REdge "V" "T" 20)))
              20)

(define (largest-cap RE) 
(cond
  [(empty? RE) 0]
  [else (max (REdge-capacity (first RE)) (largest-cap (rest RE)))]))

; contained-in-nodes checks to see if the destenation of a REdge is in the list of visited nodes. 
; contained-in-nodes: REdge (list node) -> bool

(check-expect (contained-in-nodes
                (make-REdge "S" "U" 20)
                (list "S" "V" "U"))
                true
                )

(check-expect (contained-in-nodes
                (make-REdge "S" "U" 20)
                (list "S" "V"))
                false
                )

(define (contained-in-nodes RE nodes) 
  (cond
    [(empty? nodes) false]
    [else (if (equal? (REdge-end RE) (first nodes))
              true
              (contained-in-nodes RE (rest nodes))) ]))






