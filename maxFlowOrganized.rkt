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

; main-loop runs the whole algorithm
; main-loop; Graph -> Graph

(define (main-loop G)
  (local [
          (define RG (create-residual G))
          (define stPath (find-st-path RG))
          ]
    (if (false? stPath)
        G
        (main-loop (augment G stPath))
    )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; create the residual graph by modifying the graph
; create-residual: Graph -> RGraph

(check-expect (create-residual 
               (list 
                (make-Edge "S" "U" 20 20)
                (make-Edge "S" "V" 10 0)
                (make-Edge "U" "V" 30 20)
                (make-Edge "U" "T" 10 0)
                (make-Edge "V" "T" 20 20)))
              (list
               (make-REdge "U" "S" 20)
               (make-REdge "S" "V" 10)
               (make-REdge "U" "V" 10)
               (make-REdge "V" "U" 20)
               (make-REdge "U" "T" 10)
               (make-REdge "T" "V" 20))
              )

(define (create-residual G)
  (cond
    [(empty? G) empty]
    [(cons? G) (append (create-REdges (first G)) (create-residual (rest G))) ]
    )
  )

;create-REdges creates the REdge(s) associated with a singe edge both reverse and forward
;create-REdges: Edge -> (list REdges)

(define (create-REdges e)
  (cond
    [(= 0 (Edge-flow e)) (list (make-REdge (Edge-start e) (Edge-end e) (Edge-capacity e)))]
    [(= (Edge-capacity e) (Edge-flow e)) (list (make-REdge (Edge-end e) (Edge-start e) (Edge-capacity e)))]
    [else (list (make-REdge (Edge-start e) (Edge-end e) (- (Edge-capacity e) (Edge-flow e))) (make-REdge (Edge-end e) (Edge-start e) (Edge-flow e)))]
  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; augment removes forward edges whos capacity has been reached. 
; augment: Graph Path -> Graph

(check-expect (augment G
              (list 
               (make-REdge "S" "U" 20)
               (make-REdge "U" "V" 30)
               (make-REdge "V" "T" 20)))
              (list 
                (make-Edge "S" "U" 20 20)
                (make-Edge "S" "V" 10 0)
                (make-Edge "U" "V" 30 20)
                (make-Edge "U" "T" 10 0)
                (make-Edge "V" "T" 20 20)))

(check-expect (augment (list 
                (make-Edge "S" "U" 20 20)
                (make-Edge "S" "V" 10 0)
                (make-Edge "U" "V" 30 20)
                (make-Edge "U" "T" 10 0)
                (make-Edge "V" "T" 20 20))
              (list 
               (make-REdge "S" "V" 10)
               (make-REdge "V" "U" 20)
               (make-REdge "U" "T" 10)))
              (list 
                (make-Edge "S" "U" 20 20)
                (make-Edge "S" "V" 10 10)
                (make-Edge "U" "V" 30 10)
                (make-Edge "U" "T" 10 10)
                (make-Edge "V" "T" 20 20))
              )
              
              

(define (augment G P) 
  (local[
         (define bottleneck (bottleneck-path P))
         ]
  (augment-loop G P bottleneck)
  ))

(define (augment-loop G P bottleneck)
  (cond
    [(empty? G) empty]
    [(cons? G) (cons (modify-edge (first G) P bottleneck) (augment-loop (rest G) P bottleneck))]
    ))


;modify-edge takes an edge from the graph and compares it to an REdge path. 
;modify-edge: edge (list REdges) nat -> edge

(define (modify-edge e P bottleneck) 
  (cond
    [(empty? P) e]
    [(cons? P) (cond 
                 [(forward-edge? e (first P)) (make-Edge (Edge-start e) (Edge-end e) (Edge-capacity e) (+ (Edge-flow e) bottleneck))]
                 [(backward-edge? e (first P)) (make-Edge (Edge-start e) (Edge-end e) (Edge-capacity e) (- (Edge-flow e) bottleneck))]
                 [else (modify-edge e (rest P) bottleneck)])
               ]))

;backward-edge? checks to see if a REdge is a backwards edge of an edge
;backward-edge?: edge REdge -> bool
(define (backward-edge? e re)
  (and (equal? (Edge-start e) (REdge-end re)) (equal? (Edge-end e) (REdge-start re))))

;forward-edge? checks to see if a REdge is a forward edge of an edge
;forward-edge? edge REdge -> bool
(define (forward-edge? e re)
  (and (equal? (Edge-start e) (REdge-start re)) (equal? (Edge-end e) (REdge-end re))))
  
;Bottleneck-path finds the smallest capacity on a REdge path
;Bottleneck-path: (list REdge) -> nat

(check-expect (bottleneck-path
              (list 
               (make-REdge "S" "U" 20)
               (make-REdge "U" "V" 30)
               (make-REdge "V" "T" 20)))
              20)

(check-expect (bottleneck-path
              (list 
               (make-REdge "S" "V" 10)
               (make-REdge "V" "U" 20)
               (make-REdge "U" "T" 10)))
              10)

(define (bottleneck-path P)
  (cond
  [(empty? (rest P)) (REdge-capacity (first P))]
  [else (min (REdge-capacity (first P)) (bottleneck-path (rest P)))]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;find-st-path finds a path from the S node to the T node and returns false if one couldnt be found. 
;find-st-path: RGraph -> Path

(check-expect (find-st-path Gf)
              (list 
               (make-REdge "S" "U" 20)
               (make-REdge "U" "V" 30)
               (make-REdge "V" "T" 20)))

(check-expect (find-st-path Gf2)
              (list 
               (make-REdge "S" "V" 10)
               (make-REdge "V" "U" 20)
               (make-REdge "U" "T" 10)))

(check-expect (find-st-path (list (make-REdge "S" "U" 20)
                                  (make-REdge "S" "V" 10)
                                  (make-REdge "U" "V" 30)
                                  (make-REdge "T" "U" 10)
                                  (make-REdge "T" "V" 20)))
              false)



(define (find-st-path RG)
  (st-path RG "S" (list "S")))

;st-path looks for edges that havent already been searched over in an attempt to reach the T node. produces false if no edge can be found. 
;st-path: RGraph targetNode (List nodes) -> Path
(define (st-path RG atNode visited) 
  (st-path-accu RG atNode visited empty)
  )

(define (st-path-accu RG atNode visited accumulated)
  (local[
         (define selectedREdge (select-edge (all-node-paths RG atNode) visited))
           ]
  (cond
   [(equal? atNode "T") (reverse accumulated)] 
   [(empty? selectedREdge) false]
   [else 
    (st-path-accu RG (REdge-end selectedREdge ) (cons atNode visited)  (cons selectedREdge accumulated))])))

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

(define (select-edge-loop paths cap)
  (cond
    [(empty? paths) empty]
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






