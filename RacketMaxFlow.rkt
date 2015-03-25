;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname RacketMaxFlow) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #t #t none #f ())))
(define G (list (list "S" "U" 20)
                (list "S" "V" 10)
                (list "U" "V" 30)
                (list "U" "T" 10)
                (list "V" "T" 20)))

(define big-ass-number 9999999999999)




;;removes forward edges whos capacity has been reached
(define (augment-path P)
  (filter (lambda (y) (> (third y) 0)) (map (lambda (x) (list (first x) (second x) (- (third x) (bottleneck-path P)))) P)))

;;finds lowest capacity along path
(define (bottleneck-path P)
  (cond
  [(empty? P) big-ass-number]
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

;;finds largest capacity in G
(define (largest-cap G) 
(cond
  [(empty? G) 0]
  [else (max (third (first G)) (largest-cap (rest G)))]))
