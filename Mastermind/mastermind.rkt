#lang racket

(require "main.rkt")
(require test-engine/racket-tests)

;;---------------------------------------------
;;
;; Mastermind 1.0
;;
;; Generates a random secret. Player has up to
;; NMOVES to guess the secret.
;;
;;---------------------------------------------

;;------------
;;
;; TODO:
;;
;; [ 1 ] Terminate game when player guesses correctly
;; [ 2 ] Notify when user out of turns, etc.
;; [ 3 ] z3.rkt constraints
;;
;;------------

;;---------------------------------------------

;; Constants and Data types

(define HUMANPLAYER #f)
(define NPEGS  4)
(define NCOLS  6)
(define NMOVES 8)

;; A turn is a
;;
;;  (list-of-int int int)
;;
(define-struct turn (guess red white))

;;--------------------------------------------

;; generate-secret: num num -> list-of-num
;;
;; Generates a random list of npegs numbers
;; with values between 0 and ncols - 1.
(define (generate-secret npegs ncols secret)
  (cond
    [(= npegs 0) secret]
    [else (generate-secret
           (- npegs 1)
           ncols
           (cons (random ncols) secret))]))

(define noPegs 0)

;; play-mastermind: void -> void
;;
;; Main loop for game. Generates a secret,
;; and prompts user until user successfully 
;; guesses or runs out of turns. Prints turns
;; taken by player.
(define (play-mastermind)
  
  (set! noPegs 0)
  ;create smt context
  (smt:with-context 
   (smt:new-context)
   
   ; make z3 pegs
   (define z3-pegs (smt:make-fun/list NPEGS () Int))
   
   ; range constraint
   (for ([peg z3-pegs]) (smt:assert (and/s (>=/s peg 0) (</s peg NCOLS))))
   
   ; play for NMOVES turns
   (define current-turn 0)
   
   ; generate the secret
   (define secret (generate-secret NPEGS NCOLS '()))
   
   ; initialize turns to an empty list
   (define turns '())
   
   ; main loop
   (for ([current-turn (in-range NMOVES)])
     
     (letrec (
              ; prompt user or z3 for guess
              [guess (if HUMANPLAYER 
                         (get-human-guess)
                         (if noPegs
                             (for/list ([peg (stream->list (in-range NPEGS))])
                               (if (>= peg (/ NPEGS 2))
                                   (+ 1 noPegs)
                                   noPegs))
                             (get-z3-guess z3-pegs)))]
              ; determine pegs in guess that match straight across
              [red-pegs (score-red secret guess)]
              ; determine pegs in guess that are awarded either red or white
              [red-n-white-pegs (score-white 
                                 secret 
                                 guess 
                                 red-pegs ; indices of pegs marked red 
                                 red-pegs ; initial list of indices already used
                                 ; (so cannot be used for a white peg)
                                 0)])     ; initial index in guess list
       
       ; add turn to turns list
       (set! turns (cons (make-turn guess
                                    ; number of awarded red pegs
                                    (length red-pegs)
                                    ; number of awarded white pegs
                                    (- (length red-n-white-pegs) (length red-pegs)))
                         turns)))
     
     
     (generate-constraints (car turns) z3-pegs)
     
     ; print turns
     (display "\n")
     (print-turns turns)
     (display "\n"))))

;; print-turns list-of-turns -> void
;;
;; Print the game so far.
(define (print-turns turns)
  (if (null? turns)
      #f
      (let ([turn (first turns)])
        (printf "~a  r:~a w:~a\n" (turn-guess turn) (turn-red turn) (turn-white turn))
        (print-turns (rest turns)))))

;; a helper to convert non-negative int to list
(define (int->list n) 
  (if (zero? n) 
      `()
      (append (int->list (quotient n 10)) 
              (list (remainder n 10)))))

;; get-human-guess: list-of-num -> list-of-num
;;
;; Asks player for guess, and returns
;; the player's guess as a list of numbers.
(define (get-human-guess) 
  (display "Please enter a guess:\n")
  (define guess (int->list (read)))
  (cond
    [(list? guess) guess]
    [else (begin
            (display "it's not a list.\n")
            (get-human-guess))]))

;; get-human-guess: list-of-num -> list-of-num
;;
;; Asks player for guess, and returns
;; the player's guess as a list of numbers.
(define (get-z3-guess z3-pegs)
  (smt:check-sat)
  (map smt:eval z3-pegs))

;; score-red: list-of-num list-of-num -> list-of-num
;;
;; Returns a list of indices for those pegs that
;; earned a red. For example, if
;;
;; S: 1 2 3 4
;; G: 2 2 3 4
;;
;; then (3 2 1) is returned.
(define (score-red secret guess)
  
  ; recursive helper
  (define (score-red-helper secret guess 
                            pegs curr-idx)
    
    ; check if at end of secret
    (if (null? secret)
        
        ; reached end of secret; return index of
        ; pegs awarded a red (if any)
        pegs
        
        ; else, compare first pegs in secret and guess
        (if (= (first secret) (first guess))
            
            ; same color! remember index, and look at remaining
            ; pegs
            (score-red-helper (rest secret) (rest guess)
                              (cons curr-idx pegs)
                              (+ curr-idx 1))
            
            ; wrong color; look at remaining pegs
            (score-red-helper (rest secret) (rest guess)
                              pegs
                              (+ curr-idx 1)))))
  
  ; call helper
  (score-red-helper secret guess '() 0)
  
  )

;; score-white: list-of-num list-of-num 
;;              list-of-num list-of-num num -> list-of-num
;;
;; Returns a list of indices for those pegs in the secret
;; used to score either a red or white for the guess. When
;; this function is initially called, red-pegs == pegs-used.
;;
;; For example, with
;;
;; S: 1 2 4 2
;; G: 2 2 3 1
;;
;; score-white should be called via
;;
;;   (score-white '(1 2 4 2) '(2 2 3 1) '(1) '(1) 0)
;;
;; It will return '(0 3 1).
(define (score-white secret guess red-pegs pegs-used curr-idx)
  
  ; check if any pegs remain to be checked
  (if (null? guess)
      
      ; reached end of guess; return pegs used for scoring
      pegs-used
      
      ; otherwise, at least one more peg to check
      
      ; check if peg already marked for red score
      (if (ormap (λ (used-peg) (= used-peg curr-idx)) red-pegs)
          
          ; red peg already scored; skip to next peg in guess
          (score-white secret 
                       (rest guess)
                       red-pegs
                       pegs-used
                       (+ curr-idx 1))
          
          ; peg didn't recv a red peg already; check for white,
          ; and recurse on remaining pegs in guess
          (score-white secret 
                       (rest guess) 
                       red-pegs
                       ; check if peg matches anything unused in secret
                       (check-peg secret 
                                  (first guess) 
                                  pegs-used
                                  0)
                       (+ curr-idx 1)))))

;; check-peg: list-of-num number list-of-num num -> list-of-num
;;
;; Returns a list of indices used after
;; checking if peg can receive a white
;; score.
(define (check-peg secret peg pegs-used pos)
  
  ; check if reached end of secret
  (if (null? secret)
      
      ; end of secret; return pegs used
      pegs-used
      
      ; otherwise, compare firt peg in secret with peg
      (if (= (first secret) peg)
          
          ; same color; check if peg in secret already used
          (if (ormap (λ (used-peg) (= used-peg pos)) 
                     pegs-used)
              
              ; peg already used; move on to next peg in secret
              (check-peg (rest secret) 
                         peg 
                         pegs-used 
                         (+ pos 1))
              
              ; peg not used; add to front of list, and return
              (cons pos pegs-used))
          
          ; diff color; skip to next peg in secret
          (check-peg (rest secret) peg pegs-used (+ pos 1)))))

;; generate-constraints: turn -> void
;;
;; generate z3 constraints based on red and white score
(define (generate-constraints turn z3-pegs)
  
  ; get all possible assignments of red pegs to positions
  (define red-combos (combinations (stream->list (in-range NPEGS)) (turn-red turn)))
  (define white-combos (combinations (stream->list (in-range NPEGS)) (turn-white turn)))
  
  ;(display (turn-guess turn))
  ;(display (turn-red turn))
  ;(display (turn-white turn))
  ;(display z3-pegs)
    
  (if (and (= 0 (turn-red turn)) (= 0 (turn-white turn)))
      (begin (if noPegs 
                 (set! noPegs (+ 2 noPegs))
                 '())
             (for/list ([guess (turn-guess turn)])
               (for/list ([peg z3-pegs])
                 (smt:assert (not/s (=/s guess peg))))))
      ; big or gate (this will be a list of smaller lists that represent and-gates)
      (begin (set! noPegs #f)
             (let ([or-gate '()])
               
               ; for each possible assignment of red pegs to positions
               (map (λ (combo)
                      
                      ; little and gate (this will be a list of NPEGS lists.  each small lists represents 
                      ; whether a red peg is assigned to a Position
                      (let ([and-gate '()])
                        
                        ; for each position in range 0 to NPEGS-1
                        (map (λ (position)
                               
                               ; if the position is in the assignment of red pegs
                               (if (ormap (λ (element-in-combo) (= element-in-combo position)) combo)
                                   
                                   ; add a sexp to the and gate that will represent that for this 
                                   ; assignment of red markers to positions, the guess at this position
                                   ; is equal to the secret at this position.
                                   ; the first element of the sexp is '1' which we will later parse to 
                                   ; mean "=/s"
                                   (set! and-gate (append and-gate (list `(1 ,position))))
                                   
                                   
                                   ; add a sexp to the and gate that will represent that for this 
                                   ; assignment of red markers to positions, the guess at this position
                                   ; is not equal to the secret at this position.
                                   ; the first element of the sexp is '0' which we will later parse to 
                                   ; mean "not =/s"
                                   (set! and-gate (append and-gate (list `(0 ,position))))))
                             
                             ; for inner map
                             (stream->list (in-range NPEGS)))
                        
                        ;(display "\n")
                        ;(display and-gate)
                        
                        ; append the and-gate to the or-gate
                        (set! or-gate (append or-gate (list and-gate))))) 
                    
                    ; for outer map
                    red-combos)
               
               ;(display "\n\n")
               ;(display or-gate)
               
               ; builds the high-level or gate for red constraints
               (define (build-red-big-or-gate input-list)
                 
                 ; map each list in the or-gate to the build-red-little-and-gate function and apply "or"
                 (apply or/s (map (λ (and-gate) (build-red-little-and-gate and-gate (and/s ))) or-gate)))
               
               ; builds the low-level and gate for red constraints
               (define (build-red-little-and-gate input-list gate)
                 
                 ; recursively build and gate
                 (if (null? input-list)
                     
                     ; if the input-list is null, the gate should be complete.
                     gate
                     
                     ; recursively call the function
                     (build-red-little-and-gate 
                      
                      ; pass everything but the first peg as the input-list
                      (cdr input-list)
                      
                      ; check the value of the first element of the tuple
                      (if (eq? (caar input-list) 1)
                          
                          ; a "1" expresses that for this assignment of red pegs to positions,
                          ; this position has a red peg (val of guess at this idx == val of secret at this idx)
                          (and/s gate (=/s (list-ref z3-pegs (cadar input-list)) 
                                           (list-ref (turn-guess turn) (cadar input-list))))
                          
                          ; a "0" expresses that for this assignment of red pegs to positions,
                          ; this position has a red peg (val of guess at this idx != val of secret at this idx)
                          (and/s gate (not/s 
                                       (=/s (list-ref z3-pegs (cadar input-list)) 
                                            (list-ref (turn-guess turn) (cadar input-list)))))))))
               
               ; pass the big red or gate assertion to z3
               (smt:assert (build-red-big-or-gate or-gate)))
             
             ; another big or gate for white constraints
             (let ([or-gate '()])
               
               ; for each possible assignment of white pegs to positions
               (map (λ (combo)
                      
                      ; little and gate (this will be a list of NPEGS lists.  each small lists represents 
                      ; whether a white peg is assigned to a Position
                      (let ([and-gate '()])
                        
                        ; for each position in range 0 to NPEGS-1
                        (map (λ (position)
                               
                               ; if the position is in the assignment of white pegs
                               (if (ormap (λ (element-in-combo) (= element-in-combo position)) combo)
                                   
                                   ; add a sexp to the and gate that will represent that for this 
                                   ; assignment of white markers to positions, the guess at this position
                                   ; is not equal to the secret at this position, but it is equal to another.
                                   ; the first element of the sexp is '1' which we will later parse to 
                                   ; mean "not =/s and =/s to another peg"
                                   (set! and-gate (append and-gate (list `(1 ,position))))
                                   
                                   
                                   ; add a sexp to the and gate that will represent that for this 
                                   ; assignment of white markers to positions, the guess at this position
                                   ; is not equal to the secret at any position.
                                   ; the first element of the sexp is '0' which we will later parse to 
                                   ; mean "not =/s for all pegs"
                                   (set! and-gate (append and-gate (list `(0 ,position))))))
                             
                             ; for inner map
                             (stream->list (in-range NPEGS)))
                        
                        ;(display "\n")
                        ;(display and-gate)
                        
                        ; append the and-gate to the or-gate
                        (set! or-gate (append or-gate (list and-gate))))) 
                    
                    ; for outer map
                    white-combos)
               
               ; builds the high-level or gate for white constraints
               (define (build-white-big-or-gate input-list)
                 
                 ; map each list in the or-gate to the build-white-little-and-gate function and apply "or"
                 (apply or/s (map (λ (and-gate) (build-white-little-and-gate and-gate (and/s ))) or-gate)))
               
               ; builds the low-level and gate for white constraints
               (define (build-white-little-and-gate input-list gate)
                 
                 ; recursively build and gate
                 (if (null? input-list)
                     
                     ; if input list is null, return the gate (which should be finished building)
                     gate
                     
                     ; if input list is not null, then it will recursively call itself
                     (build-white-little-and-gate 
                      
                      ; pass everything but the first peg as the input-list
                      (cdr input-list)
                      
                      ; check the value of the first element of the tuple
                      (if (eq? (caar input-list) 1)
                          
                          ; then
                          ; a "1" expresses that for this assignment of white pegs to positions,
                          ; this position has a white peg (val of guess at this idx != val of secret at this idx
                          ; and idx == val of secret at a different idx)
                          (and/s gate
                                 ; These two statements say that val of guess at this idx != val of secret at this idx
                                 (and/s (not/s (=/s (list-ref z3-pegs (cadar input-list))
                                                    (list-ref (turn-guess turn) (cadar input-list))))
                                        ; but val of guess at this idx == val of secret at some idx
                                        (or/s (apply or/s
                                                     ;iterates though each peg in the z3 logic
                                                     (for/list ([peg z3-pegs])
                                                       ;to say that the guess at this idx might equal it.
                                                       (=/s (list-ref (turn-guess turn) (cadar input-list)) peg))))))
                          
                          ; else
                          ; a "0" expresses that for this assignment of white pegs to positions,
                          ; this position has no peg.  assume nothing.  add nothing.
                          gate))))
               
               ; pass the big white or gate assertion to z3
               (smt:assert (build-white-big-or-gate or-gate))))))

;; returns a list of all subsets of the list entered
(define (subsets x)
  (if (null? x)
      ; if empty, return a list with an empty list in it.
      '(())
      ; one element at a time, recursively build subsets
      (let ((current (subsets (cdr x))))
        (append (map (λ (lis) (cons (car x) lis)) current) current))))

;; return a list with all combinations of size k from the list n-list
(define (combinations n-list k)
  
  (define (combinations-helper x p-set combos-list)
    (if (null? p-set)
        
        ; if empty, return the combos-List
        combos-list
        
        ; if the length of the first element is equal to x (aka k)
        (if (= (length (car p-set)) x)
            
            ; add it to the combos-lists and recurse
            (combinations-helper x (cdr p-set) (append combos-list (list (car p-set))))
            
            ; otherwise just recurse
            (combinations-helper x (cdr p-set) combos-list))))
  
  (combinations-helper k (subsets n-list) '()))

;; Fire up game
(play-mastermind)

(define (forever)
  (play-mastermind)
  (forever))

; run 'till it breaks or you are pretty sure it won't
; formal verification huh?
#;(forever)

;;-----------------------------------------------

;; TESTS

(check-expect (score-red '() '()) '())
(check-expect (score-red '(1 2 3) '(4 5 6)) '())
(check-expect (score-red '(2) '(2)) '(0))
(check-expect (score-red '(2 3 5) '(5 3 2)) '(1))
(check-expect (check-peg '() 3 '() 0) '())
(check-expect (check-peg '(3) 3 '() 0) '(0))
(check-expect (check-peg '(4 2 2) 2 '() 0) '(1))
(check-expect (check-peg '(4 2 2) 2 '(1) 0) '(2 1))
(check-expect (check-peg '(1 3 4 5 4) 4 '(2 4) 0) '(2 4))
(check-expect (check-peg '(3 4 3 2) 2 '(0) 0) '(3 0))
(check-expect (check-peg '(3 4 3 2) 2 '(3 0) 0) '(3 0))
(check-expect (check-peg '(3 4 3 2) 3 '(3 0) 0) '(2 3 0))

(check-expect (score-white '() '() '() '() 0) '())
(check-expect (score-white '(1 2) '() '(2 3) '(2 3) 0) '(2 3))
(check-expect (score-white '(2 2 3 4) '(1 1 2 2) '() '() 0) '(1 0))
(check-expect (score-white '(2 2 3 4) '(1 1 3 2) '(2) '(2) 0) '(0 2))
(check-expect (score-white '(2 3 4 2 8 9 0 1 2) '(3 9 8 2 0 9 8 2 0) '(5 3) '(5 3) 0) '(0 6 4 1 5 3))
(check-expect (score-white '(3 3 1 3) '(3 2 4 2) '(0) '(0) 0) '(0))
(check-expect (score-white '(3 4 3 2) '(3 2 2 3) '(0) '(0) 0) '(2 3 0))
(check-expect (score-white '(3 4 3 2) '(3) '(0) '(3 0) 3) '(2 3 0))

; comment out (play-matermind) and uncomment the line below to run tests
;(test)
