---
title: "SICP Solutions in Clojure Chapter 3"
date: 2021-04-12T18:16:52+08:00
categories: ["IT", "science"]
tags: ["algorithms", "principles", "LISP"]
draft: true
---


### Exercise 3.1

```clojure
(defn make-accumulator [initial]
  (let [sum (atom initial)]
    (fn [x]
      (swap! sum (partial + x)))))
```

### Exercise 3.2

```clojure
(defn make-monitored [f]
  (let [counter (atom 0)]
    (fn [x]
      (condp = x
        'how-many-calls?
          @counter
        'reset-count
          (swap! counter (constantly 0))
        (do
          (f x)
          (swap! counter inc))))))
```

### Exercise 3.3

```clojure
(defn make-account [initial-balance password]
  (let [balance (atom initial-balance)]
    (fn [pass operate]
      (cond
        (not= pass password)
          (constantly "Incorrect password")
        (= operate 'withdraw)
          (fn [x]
            (if (>= @balance x)
              (swap! balance #(- % x))
              "Insufficient funds"))
        (= operate 'deposit)
          (fn [x]
            (swap! balance (partial + x)))
        :else
          (throw (Exception. "Unknown request: MAKE-ACCOUNT"))))))
```

### Exercise 3.4

```clojure
(defn make-account [initial-balance password call-the-cops]
  (let [balance (atom initial-balance)
        consecutive-wrong-pass (atom 0)]
    (fn [pass operate]
      (cond
        (not= pass password)
          (do
            (if (> (swap! consecutive-wrong-pass inc) 3)
              (call-the-cops))
            (constantly "Incorrect password"))
        :else
          (do
            (swap! consecutive-wrong-pass (constantly 0))
            (cond
              (= operate 'withdraw)
                (fn [x]
                  (if (>= @balance x)
                    (swap! balance #(- % x))
                    "Insufficient funds"))
              (= operate 'deposit)
                (fn [x]
                  (swap! balance (partial + x)))
              :else
                (throw (Exception. "Unknown request: MAKE-ACCOUNT"))))))))
```

### Exercise 3.5

```clojure
(defn random-in-range [a b] ;;Include left, exclude right border.
  (+ a (rand-int (- b a))))

(defn monte-carlo [trials experiment]
  (->>
    (repeatedly experiment)
    (take trials)
    (map (fn [x] (if x 1 0)))
    (reduce +)
    (#(/ % trials))))

(defn monte-carlo-integration [p x1 x2 y1 y2 trials]
 (* (monte-carlo trials #(p (random-in-range x1 (+ x2 1))
                          (random-in-range y1 (+ y2 1)))) (- y2 y1) (- x2 x1)))

(/ (double (monte-carlo-integration (fn [x y] (<= (+ (* x x) (* y y)) 1000000)) -1000 1000 -1000 1000 1000000)) 1000000)
```

### Exercise 3.6

It's simple yet hard to implement in Clojure, since I didn't find any information on how to initialize the seed of random, so I'll skip it.

### Exercise 3.7

```clojure
(defn make-account [initial-balance password]
  (let [balance (atom initial-balance)]
    (fn [pass operate]
      (cond
        (not= pass password)
          (constantly "Incorrect password")
        (= operate 'withdraw)
          (fn [x]
            (if (>= @balance x)
              (swap! balance #(- % x))
              "Insufficient funds"))
        (= operate 'deposit)
          (fn [x]
            (swap! balance (partial + x)))
        :else
          (throw (Exception. "Unknown request: MAKE-ACCOUNT"))))))

(defn make-joint [account pass another-pass]
  (if (= ((account pass 'deposit) 0) "Incorrect password")
    (constantly "Incorrect password for the original account")
    (fn [input-pass operate]
      (not= input-pass another-pass)
        (constantly "Incorrect password")
      :else
        (account pass operate))))
```

### Exercise 3.8
```clojure
(defn f-generator []
  (let [t (atom 0)]
    (fn [x]
      (swap! t inc)
      (if (= @t 1) x 0))))

(def f (f-generator))
```

### Exercise 3.9

Assume we call the factorial function from the global environment.

For the recursive version:

  1. Call (factorial 6), system creates a new frame E1 for the function, whose enclosing environment is the global environment.

  2. In (factorial 6), we evaluate (- n 1), where n is 6, got 5.

  3. Call (factorial 5), system creates a new frame E2 for the function, whose enclosing environment is E1.

  ...

  50. Call (factorial 1), system creates a new frame Ex for the function, enclosed by environment Ex-1.

  51. The function return 1.

  ...

  99. In (factorial 5), we evaluate (n * 24), where n is 5, return 120 to the caller function.

  100. In (factorial 6), we evaluate (n * 120), where n is 6, return 720 to the caller in the global environment.

For the iterative version:

  1. Call (factorial 6) from the global environment, the system creates a new frame E1 for the function, enclosed by the global environment.

  2. Call (fac-iter 1 1 6) from E1, system creates a new frame E2.

  3. Call (fac-iter 1 2 6) from E2, system creates a new frame E3.

  ...

  50. Call (fac-iter 720 7 6) from Ex, returns 720.

  51. Returns 720 from the Ex-1 frame.

  ...

  100. Return 720 from E1.

### Exercise 3.10

Difference, the let binding way have created a new frame of environment, and store the variables in the inner-most environment.

### Exercise 3.11

For each call on the make-account, the system creates a frame for the initial amount of money. So when different call on the make-account generate different frame for storing the state of that account.

### Exercise 3.12

Response 1: (b nil)

Response 2: (b (c (d nil)))

### Exercise 3.13

A loop. 'a -> 'b -> 'c -> 'a ...

Attempt to get the last element results in infinite loop.

### Exercise 3.14

This reverses a given list.

v: (list 'd 'c 'b 'a)
w: 'd

### Exercise 3.15

Skipped, it's easy.

### Exercise 3.16

```clojure
'(a (b c)) ;; 3

(def z '(a b))
(list z (list c z)) ;; 4

(def a '(x))
(def b (list a a))
(def c (list b b)) ;; 7

(def z '(a a))
(set-car! z z) ;; Infinite loop, I use set-car! just to demonstrate, actually clojure has no set-car!
```

### Exercise 3.17
```clojure
(defn count-lists[x]
  (defn iter [record input]
    (if (and (list? input) (not (some (partial identical? input) record)))
      (reduce iter (conj record input) input)
      record))
  (count (iter '() x)))
```
### Exercise 3.18
```clojure
(defn cycle?[x]
  (let [flag (atom false)
        chain (atom ()) ]
    (defn iter [record input]
      (cond (not (list? input))
              record
            (some (partial identical? input) @chain)
              (do (swap! flag (constantly true))
                  record)
            (some (partial identical? input) record)
              record
            :else
              (do
                (swap! chain #(conj % input))
                (reduce iter (conj record input) input)
                (swap! chain #(drop 1 %)))))
    (iter '() x)
    @flag))
```

This should work as expected, but I don't find a way to construct a self pointing list/pair.

### Exercise 3.19

Use the Floyd's "slow fast pointer" algorithm:

  1. Make 2 pointers A and B pointing to the head of the list.
  2. For each step, Move A one step forward and B two steps forward.
  3. If we reach the tail, without A and B meeting, then there's no loop.
  4. o.w. There is a loop. The algorithm is guaranteed to terminate.

Correctness:
  Obviously, if there's no loop. the algorithm while terminate without two Pointers meeting. What we should consider is the situation that there is a loop.

  If there's a loop, we must have a situation that both of the pointers trapped in the loop.

  Let's say the size of the loop is N, and the distance between A and B is t when they first entered the loop. Note that the distance t (Assume A is in the front, B is in the back. )

  So each move, A moves forward 1 step while B moves forward 2 step, there distance reduce by 1. After t moves, they meet each other.

This algorithm is different from the one implemented in 3.18, since 3.18 is actually judging cycles over a map rather than a linked list.

### Exercise 3.20

Skipped XP

### Exercise 3.21

The pair of the queue object actually stores a head and rear pointer, So whenever it prints, it prints a pair of the original queue and the last element.

```clojure
(def print-queue (comp prn first))
```

### Exercise 3.22

```clojure
(defn make-queue []
  (let [front-ptr (atom ())
        rear-ptr (atom ())]
     { :front-ptr (fn [] @front-ptr)
       :rear-ptr (fn [] @rear-ptr)
       :set-front-ptr! (fn [x] (swap! front-ptr (constantly x)))
       :set-rear-ptr! (fn [x] (swap! rear-ptr (constantly x)))}))

(defn front-ptr [q] ((:front-ptr q)))
(defn rear-ptr [q] ((:rear-ptr q)))
(defn set-front-ptr! [q x] ((:set-front-ptr! q) x))
(defn set-rear-ptr! [q x] ((:set-rear-ptr! q) x))
```

### Exercise 3.23
```clojure
(defn make-deque []
  (defn make-node [val] {:val val :last nil :next nil})
  (let [front-ptr (atom nil)
        rear-ptr (atom nil)]
    { :front-ptr (fn [] @front-ptr)
      :rear-ptr (fn [] @rear-ptr)
      :swap-front-ptr! (fn [f] (swap! front-ptr f))
      :swap-rear-ptr! (fn [f] (swap! rear-ptr f))}))

(defn front-ptr [q] ((:front-ptr q)))
(defn rear-ptr [q] ((:rear-ptr q)))
(defn set-front-ptr! [q x] ((:swap-front-ptr! q) (constantly x)))
(defn set-rear-ptr! [q x] ((:swap-rear-ptr! q) (constantly x)))
(defn swap-front-ptr! [q f] ((:swap-front-ptr! q) f))
(defn swap-rear-ptr! [q f] ((:swap-rear-ptr! q) f))

(defn empty-deque? [q] (nil? (front-ptr q)))
(defn front-deque[q]
  (if (empty-deque? q)
    (throw (Exception. "FRONT called with an empty queue"))
    (:val (front-ptr q))))
(defn front-deque [q]
  (if (empty-deque? q)
    (throw (Exception. "FRONT called with an empty queue"))
    (:val (front-ptr q))))

(defn front-insert-deque! [q x]
  (let [new-front (-> (make-node val)
                      (assoc :next (front-ptr q)))]
    (if (empty-deque? q)
      (set-rear-ptr! q new-front)
      (swap-front-ptr! q #(assoc % :last new-front)))
    (set-front-ptr! q new-front)))

(defn rear-insert-deque! [q x]
  (let [new-rear (-> (make-node val)
                     (assoc :last (rear-ptr q)))]
    (if (empty-deque? q)
      (set-front-ptr! q new-rear)
      (swap-rear-ptr! q #(assoc % :next new-rear)))
    (set-rear-ptr! q new-rear)))

(defn front-delete-deque! [q]
  (if (empty-deque? q)
    (throw (Exception. "DELETE called with an empty queue"))
    (if (= (front-ptr q) (rear-ptr q))
      (do (set-front-ptr! q nil)
          (set-rear-ptr! q nil))
      (do
        (swap-rear-ptr! q :last)
        (swap-rear-ptr! q #(assoc % :next nil))))))

(defn rear-delete-deque! [q]
  (if (empty-deque? q)
    (throw (Exception. "DELETE called with an empty queue"))
    (if (= (front-ptr q) (rear-ptr q))
      (do (set-front-ptr! q nil)
          (set-rear-ptr! q nil))
      (do
        (swap-front-ptr! q :next)
        (swap-front-ptr! q #(assoc % :last nil))))))
```

### Exercise 3.24

```clojure
(defn make-table [same-key?] ;; This is implemented as a n-dimension array
  (let [local-table (atom nil)]
    (defn lookup [keys table]
      (cond (or (nil? table) (empty? table))
              false
            (same-key? (first keys) (first (first table)))
              (if (empty? (rest keys))
                (second (first table))
                (recur (rest keys) (second (first table))))
            :else
              (recur key (rest table))))
    (defn insert [keys table value]
      (cond
        (empty? keys)
          value
        (or (nil? table) (empty? table))
          (list (list (first keys) (insert (rest keys) nil value)))
        (same-key? (first keys) (first (first table)))
          (conj (rest table) (list (first (first table))(insert (rest keys) (second (first table)) value)))
        :else
          (conj (insert keys (rest table) value) (first table))))
  (fn [m]
      (condp = m
       'lookup-proc
         (fn [keys]
           (lookup (if (list? keys) keys (list keys)) @local-table))
       'insert-proc!
         (fn [keys value]
           (swap! local-table (constantly
             (insert (if (list? keys) keys (list keys)) @local-table value))))
       :else
         (throw (Exception. (str "MAKE-TABLE: procedure not found for " m)))))))
```

### Exercise 3.25

Implemented in 3.24

### Exercise 3.26

A binary tree resides in another.

### Exercise 3.27

Environment diagram omitted.

The algorithm now turns to O(n+m), where n is the scale of input to the function and m is the time you query.

This is because for every x, f(x) will only be calculated once.

Scheme/Clojure won't work the same, if the recursion part won't call the memoized function.


