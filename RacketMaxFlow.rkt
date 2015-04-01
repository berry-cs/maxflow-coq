;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname RacketMaxFlow) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f ())))


; original graph
(define G (list (list "S" "U" 20 0)
                (list "S" "V" 10 0)
                (list "U" "V" 30 0)
                (list "U" "T" 10 0)
                (list "V" "T" 20 0)))

; residual graph
(define Gf (list (list "S" "U" 20)
                (list "S" "V" 10)
                (list "U" "V" 30)
                (list "U" "T" 10)
                (list "V" "T" 20)))

(define P1 
  (list (list "S" "U" 20) (list "U" "V" 30) (list "V" "T" 20)))

(define P1b
  (list (list "S" "U" 20) (list "U" "V" 20) (list "V" "T" 20)))

;; An Edge is (list v1 v2 cap flo)

;; A REdge is (list v1 v2 flo)   where flo can be negative to indicate a backward edge



;; add-flow/edge : Edge REdge -> Edge

(define (add-flow/edge e re)
  (list (first e) (second e) (third e) (+ (fourth e) (third re))))


;; add-flow : Graph Path -> Graph

(check-expect (add-flow G P1b)
              (list (list "S" "U" 20 20)
                    (list "S" "V" 10 0)
                    (list "U" "V" 30 20)
                    (list "U" "T" 10 0)
                    (list "V" "T" 20 20)))

(define (add-flow G p)
  (map (λ(e) (if (contains-edge? p e)
                 (add-flow/edge e (find-edge p e))
                 e))
       G))



; update-residual : RGraph Graph -> RGraph

(check-expect (update-residual (list 
                                (list "S" "V" 10)
                                (list "U" "V" 10)
                                (list "U" "T" 10)
                                )
                               (list (list "S" "U" 20 0)
                                     (list "S" "V" 10 0)
                                     (list "U" "V" 30 0)
                                     (list "U" "T" 10 0)
                                     (list "V" "T" 20 0)))
              (list (list "U" "S" -20)
                    (list "S" "V" 10)
                    (list "U" "V" 10)
                    (list "V" "U" -20)
                    (list "U" "T" 10)
                    (list "T" "V" -20)
                                ))

(define (update-residual RG G)
  (cond 
    [(empty? G) null]
    [(cons? G) (if (contains-edge? RG (first G))
                   (if (equal-capacity? (find-edge RG (first G)) (first G))
                    (cons (make-REdge (find-edge RG (first G))) (update-residual RG (rest G)))
                    (cons (make-REdge (find-edge RG (first G))) (cons (reverse-REdgeCap (find-edge RG (first G))(first G)) (update-residual RG (rest G)))))
                    (cons (reverse-REdge (first G)) (update-residual RG (rest G))))]
                    ))

;;equal-capacity?: edge edge -> boolean
(define (equal-capacity? re e)
  (equal? (third re) (third e)))

;;reverse-RedgeCap: edge edge -> edge
(define (reverse-REdgeCap re e)
(list (second e) (first e) (- (third re) (third e))))

;;make-REdge: edge -> edge
(define (make-REdge e)
  (list (first e) (second e) (third e)))


;;reverse-REdge: edge -> edge
(define (reverse-REdge e)
  (list (second e) (first e) (- 0 (third e))))


;;removes forward edges whos capacity has been reached
(check-expect (augment-path Gf P1 20)
              (list 
                    (list "S" "V" 10)
                    (list "U" "V" 10)
                    (list "U" "T" 10)
                    ))

(define (augment-path G P amt)
  (filter non-zero-edge?
          (map (λ(e) (if (contains-edge? P e)
                         (reduce-by e amt)
                         e))
               G)))

;; reduce-by : Edge Number -> Edge

(define (reduce-by e amt)
  (if (= 4 (length e))
      (list (first e) (second e) (- (third e) amt) (fourth e))
      (list (first e) (second e) (- (third e) amt) )))


;; contains-edge? : Graph Edge -> Boolean
(define (contains-edge? G e)
  (cond [(empty? G) false]
        [(cons? G) (or (edge-equal? (first G) e)
                       (contains-edge? (rest G) e))]))


;; find-edge? : Graph Edge -> Edge
(define (find-edge G e)
  (cond [(empty? G) (error "edge not found")]
        [(cons? G) (if (edge-equal? (first G) e)
                       (first G)
                       (find-edge (rest G) e))]))



;; edge-equal? : Edge Edge -> Boolean
(define (edge-equal? e1 e2)
  (and (string=? (first e1) (first e2))
       (string=? (second e1) (second e2))))


;; non-zero-edge? : Edge -> Boolean
(define (non-zero-edge? e)
  (not (zero? (third e))))

  
;  (filter (lambda (y) (> (third y) 0))
;          (map (lambda (x) (list (first x) (second x) 
;                                 (- (third x) (bottleneck-path P)))) P)))


;; IN COQ (proof bottleneck_pick_min)
;;finds lowest capacity along path
(define (bottleneck-path P)
  (cond
  [(empty? (rest P)) (third (first P))]
  [else (min (third (first P)) (bottleneck-path (rest P)))]))


;;finds a path from S to T sort of
(define (st-path G node)
  (cond
   [(equal? node "T") null] 
   [else (cons (select-edge G node) (st-path G (second (select-edge G node)))
           )]))


;;Finds an edge with the greatest capacity connected to [node]
(define (select-edge G node)
 (first (filter (lambda (x) (= (third x) 
                      (largest-cap (all-node-paths G node)))) (all-node-paths G node))))
  

;; finds all paths connected to node
(define (all-node-paths G node)
  (filter (lambda (x) (equal? node (first x))) G))


;; IN COQ (no proofs, fixpoint)
;;finds largest capacity in G
;; graph -> nat
(define (largest-cap G) 
(cond
  [(empty? G) 0]
  [else (max (third (first G)) (largest-cap (rest G)))]))
