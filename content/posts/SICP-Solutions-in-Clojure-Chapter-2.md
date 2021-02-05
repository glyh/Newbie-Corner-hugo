---
title: "SICP Solutions in Clojure (Chapter 2)"
date: 2021-02-03T16:39:00+08:00
categories: ["IT", "science"]
tags: ["algorithms", "principles", "LISP"]
draft: false
---


### Exercise 2.1

```clojure
(defn make-rat [n d]
  (let [g (gcd n d) nf (/ n g) df (/ d g)]
    (if (< df 0) (list (- nf) (- df))
                      (list nf df) )))
```

### Exercise 2.2

```clojure
(defn make-point [x y] (list x y))
(def x-point first)
(def y-point second)

(defn make-segment [s t] (list s t))
(def start-segment first)
(def end-segment second)

(defn midpoint-segment [seg]
  (map #(/ (+ (% (start-segment seg)) (% (end-segment seg))) 2)
       [x-point y-point]))

(defn print-point [p] (prn (str "(" (x-point p) ", " (y-point p) ")")))
```

<!--more-->

### Exercise 2.3

```clojure

; Implementation 1
(defn make-rectangle [p1 p2] (list p1 p2))

(def abs #(if (< % 0) (- %) %))
(defn diff [f a b] (abs (- (f a) (f b))))
(def width #(diff x-point (start-segment %) (end-segment %))); segment refers to rectangle's main diagonal
(def height #(diff y-point (start-segment %) (end-segment %)))

; Implementation 2
(defn make-rectangle [p-topleft size] (list p-topleft size))

(defn size-rectangle [rect] (second rect))
(defn width [rect] (first (size-rectangle rect)))
(defn height [rect] (second (size-rectangle rect)))

(defn perimeter [rect] (* 2 (+ (width rect) (height rect))))
(defn area [rect] (* (width rect) (height rect)))


```

### Exercise 2.4

```clojure
(defn cons [x y] #(% x y))
(defn car [z] (z (fn [p q] p)))

(car (cons x y)); =>
(car #(% x y)); =>
(#(% x y) (fn [p q] p)); =>
((fn [p q] p) x y); =>
x

(defn cdr [z] (z (fn [p q] q)))
```

### Exercise 2.5

```clojure
(defn cons [x y] (int (* (Math/pow 2 x) (Math/pow 3 y))))
(defn cdr [z]
  (defn iter [z result] (if (= (rem z 3) 0) (recur (/ z 3) (+ result 1))result ))
  (iter z 0))
(defn car [z]
  (defn iter [z result] (if (= (rem z 2) 0) (recur (/ z 2) (+ result 1))result ))
  (iter z 0))
```

### Exercise 2.6

```clojure
(add-1 zero); =>
(fn [f] (fn [x] (f ((zero f) x)))); =>
(fn [f] (fn [x] (f ((fn [x] x) x)))); =>
(fn [f] (fn [x] (f x))); =>
(def one (fn [f] (fn[x] (f x))));

(add-1 one); =>
(fn [f] (fn [x] (f ((one f) x)))); =>
(fn [f] (fn [x] (f ((fn[x] (f x)) x)))); =>
(fn [f] (fn [x] (f (f x)))); =>
(def two (fn [f] (fn [x] (f (f x)))))

(def + [a b] (a b))
```

### Exercise 2.7

```clojure
(defn lower-bound first)
(defn upper-bound second)
```

### Exercise 2.8

```clojure
(defn sub-interval [I1 I2] (make-interval (- (lower-bound I1) (upper-bound I2)) (- (upper-bound I1) (lower-bound I2))))
```

### Exercise 2.9

For addition:

$$
(l_1, r_1) + (l_2, r_2) = (l_1 + l_2, r_1 + r_2)\newline
width_1 = r_1 - l_1\newline
width_2 = r_2 - l_2\newline
width_3 = (r_1+r_2)-(l_1+l_2)=width_1+width_2\newline
$$

For substraction:

$$
(l_1, r_1) - (l_2, r_2) = (l_1, r_1) + (-r_2, -l_2)\newline
$$

So this becomes addition.

For multiplication:

$$
(1, 2) \times (1, 2) = (1, 4)\newline
(1, 2) \times (3, 4) = (3, 8)
$$

All factors have width of 1, but their products' width are not the same.

For division:
$$
(1, 2) \div (1,2) = (\frac12, 2)\newline
(1, 2) \div (3, 4) = (\frac14, \frac23)
$$

All input intervals have width of 1, but their quotients' width are not the same.

### Exercise 2.10

```clojure
(defn div-interval [x y]
   (if (<= (lower-bound y) 0 (upper-bound y)) (throw (Throwable. "Divded by a interval that spans 0")))
   (mul-interval x (make-interval (/ 1.0 (upper-bound y)) (/ 1.0 (lower-bound y)))))
```

### Exercise 2.11

```clojure
(defn mul-interval [x y]
  (cond (and (>= (lower-bound x) 0) (>= (lower-bound y) 0))
          (make-interval (* (lower-bound x) (lower-bound y)) (* (upper-bound x) (upper-bound y)))
        (and (>= (lower-bound x) 0) (< (lower-bound y) 0 (upper-bound y)))
          (make-interval (* (upper-bound x) (lower-bound y)) (* (upper-bound x) (upper-bound y)))
        (and (>= (lower-bound x) 0) (<= (upper-bound y) 0))
          (make-interval (* (upper-bound x) (lower-bound y)) (* (lower-bound x) (upper-bound y)))
        (and (< (lower-bound x) 0 (upper-bound x)) (< (lower-bound y) 0 (upper-bound y)))
          (make-interval (max (* (upper-bound x) (lower-bound y)) (* (lower-bound x) (upper-bound y)))
                         (max (* (lower-bound x) (lower-bound y)) (* (upper-bound x) (upper-bound y))))
        (and (< (lower-bound x) 0 (upper-bound x)) (<= (upper-bound y) 0))
          (make-interval (* (upper-bound x) (lower-bound y)) (* (lower-bound x) (lower-bound y)))
        (and (<= (upper-bound x) 0) (<= (upper-bound y) 0))
          (make-interval (* (upper-bound x) (upper-bound y)) (* (lower-bound x) (lower-bound y)))
        :else
          (mul-interval y x)))
```

### Exercise 2.12

```clojure
(defn make-center-width [c w]
  (make-interval (- c w) (+ c w)))

(defn center [i]
  (/ (+ (lower-bound i)
        (upper-bound i))
     2))

(defn width [i]
  (/ (- (upper-bound i)
        (lower-bound i))
     2))

(defn make-center-percent [c p] (make-center-width c (* c p)))
(defn percent [I] (/ (width I)  (center I)))
```

### Exercise 2.13

$$
I_1:= make-center-percent(c_1, p_1) (c_1 > 0) \newline
I_2:= make-center-percent(c_2, p_2) (c_2 > 0) \newline
\begin{aligned}
&I_1 \times I_2 &=& (c_1(1 - p_1)c_2(1 - p_2), c_1 (1 + p_1) c_2 (1+p_2))& \\
&&=&(c_1c_2-(p_1 + p_2)c_1c_2+p_1p_2c_1c_2, c_1c_2+(p_1 + p_2)c_1c_2+p_1p_2c_1c_2)&
\end{aligned} \newline
center(I_1 \times I_2) = c_1c_2 + p_1p_2c_1c_2 \newline
percent(I_1 \times I_2) = \frac{(p_1 + p_2)c_1c_2}{c_1c_2 + p_1p_2c_1c_2} \newline
\begin {aligned}
& \because &p_1 << 1, p_2 << 1 \\
&\therefore &center(I_1 \times I_2) &\approx& c_1 c_2 & \\
&& percent(I_1 \times I_2) &\approx& p_1 + p_2 &
\end {aligned}
$$

### Exercise 2.14

```clojure
(defn par1 [r1 r2] (div-interval (mul-interval r1 r2) (add-interval r1 r2)))
(defn par2 [r1 r2] (let [one (make-interval 1 1)] (div-interval one (add-interval (div-interval one r1) (div-interval one r2)))))
```

The error occurs because $A \div A = (1, 1)$ is not guaranteed in interval calculation.

### Exercise 2.15

Yes, she is. Avoiding the same variable invloves into the calculation twice can help us avoid the occasion in Exercise 2.14.

### Exercise 2.16

My first thought is that, programming is mostly engineering rather than theory.

Engineering is always bothered with the complexity of the real world, you should consider the comsumption of resources but in theory you don't.

For example, computer can only approximate e, but in theory you just pick a sign representing it. (Space is limited, however, the information needed to represent e is infinite. )

I don't think "to design an interval-arithmetic package that does not have this shortcoming" is possible.

As long as you use one name mutiple times to refers to some variant, the problem in 2.14 will happen.

### Exercise 2.17

```clojure
(defn last-pair [L]
  (if (nil? (second L)) L (recur (rest L))))
```

### Exercise 2.18

```clojure
(defn reverse [L]
  (if (empty? L) L (concat (reverse (rest L)) (list (first L)))))
```

### Exercise 2.19

```clojure
(def no-more? empty?)
(def first-denomination first)
(def except-first-denomination rest)

(def us-coins '(50 25 10 5 1))
(def unordered-us-coins '(25 1 50 5 10))
(def uk-coins '(100 50 20 10 5 2 1 0.5))

(def cc (memoize (fn [amount coins-list]
  (cond (= amount 0) 1
        (or (< amount 0) (no-more? coins-list)) 0
        :else (+ (cc amount (except-first-denomination coins-list))
                 (cc (- amount (first-denomination coins-list)) coins-list))))))
(cc 100 us-coins)
(cc 100 unordered-us-coins)
```
The order of the list coins-list doesn't affect the answer produced by cc.

This is because the order of the coins are irrelevant to the plans to change the money.

### Exercise 2.20

```clojure
(defn same-parity [a & args]
  (if (empty? args) (list a)
    (let [b (first args)]
      (if (= (rem (- b a) 2) 0)
        (concat (list a) (apply same-parity b (rest args)))
        (apply same-parity a (rest args))))))
```

### Exercise 2.21

```clojure
(defn square-list [items]
  (if (empty? items) '() (concat (let [a (first items)] (list (* a a))) (square-list (rest items)))))
(defn square-list [items] (map #(* % %) items))
```

### Exercise 2.22

The function `cons` kept pushing elemnets to the front of the array.

```clojure
(def square #(* % %))
(defn square-list [items]
  (defn iter [things answer]
    (if (empty? things) answer
      (recur (rest things) (concat answer (list (square (first things)))))))
  (iter items '()))
```

This works for me... Maybe it's only because the call to iter in Scheme gives `nil` as the first element in the list.

### Exercise 2.23

```clojure
(def for-each [f col] (map f col) nil)

(def for-each [f col] (map f col))

(defn for-each [f col]
  (if (not (empty? col)) (do (f (first col)) (recur f (rest col)))))
```

### Exercise 2.24

Result by the interpreter : (1 (2 (3 4)))

Graphs are omited.

### Exercise 2.25

```clojure
(-> '(1 3 (5 7) 9) (rest) (rest) (first) (rest) (first))
(-> '((7)) (first) (first))
(-> '(1 (2 (3 (4 (5 (6 7)))))) (rest) (first) (rest) (first) (rest) (first) (rest) (first) (rest) (first) (rest) (first))
```

### Exercise 2.26

```clojure
(conj [1 2 3] [4 5 6])
(concat '(1 2 3) '(4 5 6))
(list '(1 2 3) '(4 5 6))
```

### Exercise 2.27

```clojure
(defn deep-reverse [L]
  (if (empty? L) L (concat (deep-reverse (rest L)) (list (let [a (first L)] (if (list? a) (deep-reverse a) a))))))
```

### Exercise 2.28

```clojure
(defn fringe [n]
  (if (empty? n)
    n
    (concat (let [a (first n)] (if (list? a) (fringe a) (list a)) )
            (fringe (rest n)))))
```

### Exercise 2.29

```clojure
(def left-branch first)
(def right-branch second)

(def length first)
(def structure second)

(defn total-weight [m]
  (if (list? m) (+ (total-weight (structure (left-branch m))) (total-weight (structure (right-branch m)))) m))
(defn balanced?
  ([m] (>= (balanced? m true)))
  ([m success]
    (if (list? m)
      (let [bl (balanced (structure (left-branch m))) br (balanced (structure (right-branch m)))]
        (if (and success (>= bl 0) (>= br 0) (= (* bl (length (left-branch m))) (* br (length (right-branch m)))))
          (+ bl br) -1))
      m)))
```

Only 4 functions, `left-branch`, `right-branch`, `length` and `structure`.

(Actually in the Clojure implementation there's nothing to change.

### Exercise 2.30

```clojure
(defn square-tree [n]
  (if (list? n) (list (square-tree (first n)) (square-tree (second n))) (* n n)))

(defn square-tree [n]
  (if (list? n) (map square-tree n) (* n n)))
```

The second implementation is better, since it can deal with non-binary trees.

### Exercise 2.31

```clojure
(defn tree-map [f n]
  (if (node? n) (f n) (map (partial tree-map f) n)))
```

### Exercise 2.32

```clojure
(defn subsets [s]
  (if (empty? s)
    '(())
    (let [s' (subsets (rest s)) a (first s)]
      (concat s' (map #(conj % a) s')))))
```

The application keeps reduce the size of a problem until it can be solve in constant time,

then merge the solutions of sub problems until we have the solution of the original problem.

### Exercise 2.33

```clojure
(defn map [p sequence] (reduce #(conj %1 (p %2)) [] sequence))

(defn append [seq1 seq2] (reduce #(conj %1 %2) (vec seq1) seq2))

(defn length [sequence] (reduce (fn [x y] (inc x)) 0 sequence))
```

### Exercise 2.34

```clojure
(defn horner-eval [x Cs]
  (reduce (fn [cur C_i] (+ (* cur x) C_i)) 0 (reverse Cs)))
(horner-eval 2 '(1 3 0 5 0 1))
```

### Exercise 2.35

```clojure
(defn count-leaves [n] (if (list? n) (reduce + 0 (map count-leaves n)) 1))
```

### Exercise 2.36

```clojure
(defn accumulate-n [op init seqs]
  (if (empty? (first seqs)) ()
    (conj (accumulate-n op init (map rest seqs)) (reduce op init (map first seqs)))))
```

### Exercise 2.37

```clojure
(defn dot-product [v w]
  (reduce + 0 (map * v w)))

(defn matrix-*-vector [m v]
  (map #(dot-product % v) m))

(defn transpose [m]
  (accumulate-n conj [] m))

(defn matrix*matrix [m n]
  (let [cols (transpose n)]
    (map #(matrix-*-vector cols %) m)))
```

### Exercise 2.38

Clojure only has fold-left, rather than fold-right.

```clojure
1/3
3/2
(1 (2 (3 nil)))
(((nil 1) 2) 3)
```

The result of `fold-left` and `fold-right` are the same if and only if the associative law works for the function f.

### Exercise 2.39

```clojure
(def fold-left reduce)
(defn fold-right [f init seq]
  (if (empty? seq) init (f (first seq) (fold-right f init (rest seq)))))

(defn reverse [seq] (fold-right #(conj %2 %1) [] seq))
(defn reverse [seq] (fold-left #(conj %1 %2) '() seq))
```

### Exercise 2.40

```clojure
(defn unique-pairs [n]
  (mapcat (fn [i] (map (fn [j] (list i j)) (range 1 (+ i 1)))) (range 1 (+ n 1))))

(defn prime? [x] (every? #(not= (mod x %) 0) (range 2 (+ 1 (int (Math/sqrt x))))))


(defn prime-sum-pairs [n] (filter #(prime? (+ (first %) (second %))) (unique-pairs n)))
```

### Exercise 2.41

```clojure
(defn triples-e [n]
  (->> (unique-pairs n)
       (filter #(let [a (second %) b (first %)] (< a b (- n a b))))
       (map #(let [a (second %) b (first %)] (list a b (- n a b))))))
(defn triples-le [n]
  (if (= n 3) () (concat (triples-le (- n 1)) (triples-e n))))
```

### Exercise 2.42

```clojure
(def empty-board ())

(defn safe? [k positions]
  (let [row-k (nth positions (- k 1)) diagonal-k-1 (+ k row-k) diagonal-k-2 (- k row-k)]
    (every? (fn [i] (let [row-i (nth positions (- i 1)) diagonal-i-1 (+ i row-i) diagonal-i-2 (- i row-i)]
      (and (not= row-i row-k) (not= diagonal-i-1 diagonal-k-1) (not= diagonal-i-2 diagonal-k-2)))) (range 1 k))))

(defn adjoin-position [new-row k rest-of-queens]
  (concat rest-of-queens (list new-row)))

(defn queens [board-size]
  (defn queen-cols [k]
    (if (= k 0) (list empty-board)
                (->> (queen-cols (- k 1))
                     (mapcat (fn [rest-of-queens] (map (fn [new-row] (adjoin-position new-row k rest-of-queens)) (range 1 (+ board-size 1)))))
                     (filter (partial safe? k)))))
  (queen-cols board-size))
```

Another version (the search algorithm), works in the positive order.

```clojure

(defn queens-optimized [board-size]
  (defn safe? [used-diagonal-1 used-diagonal-2 cur]
    (let [new-row (last cur) new-col (count cur)]
      (not (or (used-diagonal-1 (+ new-row new-col -2)) (used-diagonal-2 (+ new-row (- new-col) board-size -1))))))

  ; used-diagonal-1: [0, 2n-2],  used-diagonal-2: [0, 2n-2], unused: [1, n]
  (defn generate-state [used-diagonal-1 used-diagonal-2 unused cur]
    (let [new-row (last cur) new-col (count cur)]
      (list (assoc used-diagonal-1 (+ new-row new-col -2) true)
            (assoc used-diagonal-2 (+ new-row (- new-col) board-size -1) true)
            (disj unused new-row)
            cur)))
  (defn permutation [used-diagonal-1 used-diagonal-2 unused cur]
    (if (empty? unused) (list cur)
                        (->> unused
                             (map #(conj cur %))
                             (filter (partial safe? used-diagonal-1 used-diagonal-2))
                             (mapcat #(apply permutation (generate-state used-diagonal-1 used-diagonal-2 unused %)))
                        )))
  (let [initial-diagonal (vec (repeat (- (* 2 board-size) 1) false))]
    (permutation initial-diagonal initial-diagonal (set (range 1 (+ board-size 1))) [])))
```

It's slower because:

1. The search algorithm wants the state to be transfered between function calls.

2. The search algorithm forms a tree of call stacks, while the recursive algorithm only forms a chain of call stacks.

So here you mihght see that pure recursive algorithm works better for this particular problem.

### Exercise 2.43

Interchanging the order of maping cause the call stacks form a tree, i.e. every `queen-cols` functions calls itself at least once(In the beginning it's n times.

Estimates:
$$
\begin {aligned}
&\because& \sum_{i=4}^n \frac{i^2}{i(i-1)(i-2)(i-3)} \text{ converges.}\\
&\therefore& T(n)=O( \sum_{i=1}^n i^2 \frac {n!}{i!}) = O(n!\sum_{i=4}^n \frac{i^2}{i(i-1)(i-2)(i-3)}) = O(n!)\\
&&T'(n)=f(n)\text{, where }f(i) = O(n f(i-1)), f(0) = O(1) \\
&&T'(n)=O(n^n) \\
\end{aligned}
$$

Calculating the actual time difference its meaningless most of the time, since there is always a constant factor in [Big O notation](https://en.wikipedia.org/wiki/Big_O_notation).

(Also I'm lazy :p)

```clojure
(def empty-board ())

(defn safe? [k positions]
      (and (not= row-i row-k) (not= diagonal-i-1 diagonal-k-1) (not= diagonal-i-2 diagonal-k-2)))) (range 1 k))))

(defn adjoin-position [new-row k rest-of-queens]
  (concat rest-of-queens (list new-row)))

(defn queens [board-size]
  (defn queen-cols [k]
    (if (= k 0) (list empty-board)
                (->> (queen-cols (- k 1))
                     (mapcat (fn [rest-of-queens] (map (fn [new-row] (adjoin-position new-row k rest-of-queens)) (range 1 (+ board-size 1)))))
                     (filter (partial safe? k)))))
  (queen-cols board-size))

(defn bad-queens [board-size]
  (defn queen-cols [k]
    (if (= k 0) (list empty-board)
                (->> (range 1 (+ board-size 1))
                     (mapcat (fn [new-row] (map (fn [rest-of-queens] (adjoin-position new-row k rest-of-queens)) (queen-cols (- k 1)))))
                     (filter (partial safe? k)))))
  (queen-cols board-size))

(time (queens 8)); "Elapsed time: 18.970709 msecs"
(time (bad-queens 8)); "Elapsed time: 2977.498625 msecs"
```

### Exercise 2.44

```clojure
(defn up-split [painter n]
  (if (= n 0) painter
    (let [smaller (up-split painter (- n 1))]
      (below painter (beside smaller smaller)))))
```

### Exercise 2.45

```clojure
(defn split [painter n op1 op2]
  (if (= n 0) painter
    (let [smaller (split painter (- n 1) op1 op2)]
      (op1 painter (op2 smaller smaller)))))

(def right-split beside below)
(def up-split below beside)
```

### Exercise 2.46

```clojure
(def make-vect vector)
(def xcor-vect first)
(def ycor-vect second)

(defn add-vect [v1 v2] (make-vect (+ (xcor-vect v1) (xcor-vect v2)) (+ (ycor-vect v1) (ycor-vect v2))))
(defn sub-vect [v1 v2] (make-vect (- (xcor-vect v1) (xcor-vect v2)) (- (ycor-vect v1) (ycor-vect v2))))
(defn scale-vect [s v] (make-vect (* s (xcor-vect v)) (* s (ycor-vect v))))
```

### Exercise 2.47

Clojure doesn't have the same `cons` as Scheme does.

```clojure
(defn make-frame [origin edge1 edge2]
  (list origin edge1 edge2))

(def origin-frame first)
(def edge1-frame second)
(def edge2-frame last)
```

### Exercise 2.48

```clojure
(def make-segment list)
(def start-segment first)
(def end-segment second)
```

### Exercise 2.49

```clojure
(defn frame-coord-map [frame]
  (fn [v] (add-vect (origin-frame frame)
          (add-vect (scale-vect (xcor-vect v) (edge1-frame frame))
                    (scale-vect (ycor-vect v) (edge2-frame frame))))))

(defn segments->painter [segments]
  (fn [frame]
    (doseq [segment segments]
      (draw-line ((frame-coord-map frame) (start-segment segment)) ((frame-coord-map frame) (end-segment segment))))))

(defn shape [point-list]
  (let [cnt (count point-list)]
    (map #(make-segment (nth point-list %) (nth point-list (mod (+ % 1) cnt))) (range cnt))))

(defn comp-painter [painters]
  (fn [frame] (doseq [p painters] (p frame))))

(def outline (shape (list (make-vect 0 0) (make-vect 0 1) (make-vect 1 1) (make-vect 1 0))))
(def X (list (make-segment (make-vect 0 0) (make-vect 1 1)) (make-segment (make-vect 0 1) (make-vect 1 0))))
(def diamond (shape (list (make-vect 0 1/2) (make-vect 1/2 1) (make-vect 1 1/2) (make-vect 1/2 0))))
(def wave (shape (map #(apply make-vect %) '(
  (1/3 1) (2/3 1) (11/14 5/6) (2/3 2/3) (2/3 7/12) (11/14 7/12) (1 5/12) (1 1/3) (2/3 1/2) (2/3 1/3) (11/14 0) (2/3 0) (1/2 1/4) (1/3 0) (1/3 5/12) (3/28 1/3) (0 2/3) (0 5/6) (3/28 7/12) (1/3 2/3) (3/14 5/6)
))))
(def smile (shape (list (make-vect 5/12 5/6) (make-vect 1/2 3/4) (make-vect 7/12 5/6))))
(def figures {:outline outline, :X X, :diamond diamond :wave wave :smile smile})
(def painter-figures (into {} (map #(vector (first %) (segments->painter (second %))) figures)))
```

### Exercise 2.50

```clojure
(defn flip-horiz [painter]
  (transform-painter painter (make-vect 1 0) (make-vect 0 0) (make-vect 1 1)))

(defn rotate90 [painter]
  (transform-painter painter (make-vect 1 0) (make-vect 1 1) (make-vect 0 0)))

(defn rotate180 [painter]
  (transform-painter painter (make-vect 1 1) (make-vect 0 1) (make-vect 1 0)))
```

### Exercise 2.51

```clojure
(defn rotate90 [painter]
  (transform-painter painter (make-vect 1 0) (make-vect 1 1) (make-vect 0 0)))

(defn beside
  ([painter] (beside painter painter))
  ([painter1 painter2]
  (let [split-point (make-vect 1/2 0)
        paint-left (transform-painter painter1 (make-vect 0 0) split-point (make-vect 0 1))
        paint-right (transform-painter painter2 split-point (make-vect 1 0) (make-vect 1/2 1))]
    (fn [frame] (paint-left frame) (paint-right frame)))))

(defn below
  ([painter] (below painter painter))
  ([painter1 painter2]
  (let [split-point (make-vect 0 1/2)
        paint-up (transform-painter painter1 split-point (make-vect 1 1/2) (make-vect 0 1))
        paint-down (transform-painter painter2 (make-vect 0 0) (make-vect 1 0) split-point)]
    (fn [frame] (paint-up frame) (paint-down frame)))))

(defn below2 [painter1 painter2]
  (rotate270 (beside (rotate90 painter1) (rotate90 painter2))))
```

### Exercise 2.52

I use quil on clojure to implement everything of Chapter 2.2.4 on [Github](https://github.com/glyh/sicp-solutions-clojure/blob/main/src/sicp_solutions_clojure/chapter_2/picture_language.clj).

### Exercise 2.53

```clojure
(list 'a 'b 'c); => (a b c)
(list (list 'george)); => ((george))
(cdr '((x1 x2) (y1 y2))); => (y1 y2)
(cadr '((x1 x2) (y1 y2))); => y1
(pair? (car '(a short list))); => false
(memq 'red '((red shoes) (blue socks))); => false
(memq 'red '(red shoes blue socks)); => true
```

### Exercise 2.54

```clojure
(defn equal-list [a b]
  (cond (and (list? a) (list? b))
          (cond (and (empty? a) (empty? b)) true
                (not (or (empty? a) (empty? b))) (and (equal-list (first a) (first b)) (recur (rest a) (rest b)))
                :else false)
        (not (or (list? a) (list? b))) (= a b)
        :else false))
```

Actually a single `=` will do all the jobs for us.

### Exercise 2.55

`'` is but a macro. The reader of clojure will translate `''abracadabra` into `(quote (quote abracadabra))`.

As a result, you'll get `(quote abracadabra)`.

### Exercise 2.56

```clojure
(def variable? symbol?)
(def same-variable? =)

(defn make-sum [a1 a2]
  (cond (= a1 0) a2
        (= a2 0) a1
        (and (number? a1) (number? a2)) (+ a1 a2)
        :else (list '+ a1 a2)))

(defn make-product [a1 a2]
  (cond (or (= a1 0) (= a2 0)) 0
        (= a1 1) a2
        (= a2 1) a1
        :else (list '* a1 a2)))

(defn make-exponentiation [u n]
  (cond (or (= n 0) (= u 1)) 1
        (= n 1) u
        :else (list '** u n)))

(def addend second)
(def augend last)
(def multiplier second)
(def multiplicand last)
(def base second)
(def exponent last)


(defn sum? [x] (and (list? x) (= (first x) '+)))
(defn product? [x] (and (list? x) (= (first x) '*)))
(defn exponentiation? [x] (and (list? x) (= (first x) '**)))

(defn deriv [exp var]
  (cond (number? exp) 0
        (variable? exp) (if (= exp var) 1 0)
        (sum? exp) (make-sum (deriv (addend exp) var) (deriv (augend exp) var))
        (product? exp) (make-sum (make-product (deriv (multiplier exp) var) (multiplicand exp)) (make-product (deriv (multiplicand exp) var) (multiplier exp)))
        (exponentiation? exp) (make-product (make-product (exponent exp) (make-exponentiation (base exp) (make-sum (exponent exp) -1))) (deriv (base exp) var))
         :else (throw (Exception. (str "unknown expression type: DERIV" exp)))))
```

### Exercise 2.57

```clojure
(def variable? symbol?)
(def same-variable? =)

(defn make-sum [& args]
  (defn insert-into-sum [col i]
    (cond (number? i) (assoc col 0 (+ (first col) i))
          :else (conj col i)))
  (let [simplified (reduce insert-into-sum [0] args)]
    (cond (= (count simplified) 1) (first simplified)
          (and (= (count simplified) 2) (= (first simplified) 0)) (second simplified)
          :else (vec (concat '[+] (if (= (first simplified) 0) (rest simplified) simplified))))))

(defn make-product [& args]
  (defn insert-into-product [col i]
    (cond (number? i) (assoc col 0 (* (first col) i))
          :else (conj col i)))
  (if (some #(= % 0) args) 0
    (let [simplified (reduce insert-into-product [1] args)]
      (cond (= (count simplified) 1) (first simplified)
            (and (= (count simplified) 2) (= (first simplified) 1)) (second simplified)
            :else (vec (concat '[*] (if (= (first simplified) 1) (rest simplified) simplified)))))))

(defn make-exponentiation [u n]
  (cond (or (= n 0) (= u 1)) 1
        (= n 1) u
        :else (vector '** u n)))

(def base second)
(def exponent last)


(defn sum? [x] (and (list? x) (= (first x) '+)))
(defn product? [x] (and (list? x) (= (first x) '*)))
(defn exponentiation? [x] (and (list? x) (= (first x) '**)))

(defn deriv-nth-product [col var id]
  (apply make-product (map-indexed (fn [id' item] (if (= id' id) (deriv item var) item)) col)))

(defn deriv [exp var]
  (cond (number? exp) 0
        (variable? exp) (if (= exp var) 1 0)
        (sum? exp) (apply make-sum (map #(deriv % var) (rest exp)))
        (product? exp)
          (let [n (- (count exp) 1)]
            (apply make-sum (map (partial deriv-nth-product (rest exp) var) (range (- (count exp) 1)))))
        (exponentiation? exp) (make-product (make-product (exponent exp) (make-exponentiation (base exp) (make-sum (exponent exp) -1))) (deriv (base exp) var))
         :else (throw (Exception. (str "unknown expression type: DERIV" exp)))))

```

I've changed the definition of `deriv` here.

You can also do it without changing the definition of `deriv`, just change `augend` and `multiplicand` to these:

```clojure
(defn drop-nth [n coll]
   (keep-indexed #(if (not= %1 n) %2) coll))

(defn augend [exp]
  (drop-nth 1 exp))

(defn multiplicand [exp]
  (drop-nth 1 exp))
```

### Exercise 2.58

#### 1)
```clojure
(defn infix->prefix [exp]
  (if (or (number? exp) (variable? exp)) exp
    (vector (second exp) (infix->prefix (first exp)) (infix->prefix (last exp)))))
```

#### 2)

```clojure
(def operators-precedence {'+ 1, '* 2, '** 3})

(defn add-parentheses-to-prefix [exp] ; Only works for binary operators
  (if (or (number? exp) (variable? exp)) exp
    (let [sorted-ops (->> exp
         (map-indexed (fn [idx itm] (list idx (get operators-precedence itm))))
         (filter #(not= (second %) nil))
         (sort-by second)) split-at (first (first sorted-ops))]
      (if (nil? split-at) (recur (first exp)); the expression is a constant in some brackets
        (vector (nth exp split-at) (add-parentheses-to-prefix (take split-at exp)) (add-parentheses-to-prefix (drop (+ split-at 1) exp)))))))
```

### Exercise 2.59

```clojure
(defn element-of-set? [x set]
  (if (= x (first set)) true
      (and (not (empty? set)) (recur x (rest set)))))

(defn adjoin-set [x set]
  (if (element-of-set? x set) set (conj set x)))

(defn union-set [s1 s2]
  (cond (empty? s1) s2
        (empty? s2) s1
        :else (adjoin-set (first s1) (union-set (rest s1) s2))))
```

### Exercise 2.60

```clojure
(defn element-of-set? [x set]
  (if (= x (first set)) true
      (and (not (empty? set)) (recur x (rest set)))))

(def ajoin-set conj)

(def union-set concat)

(defn intersection-set [s1 s2]
  (cond (or (empty? s1) (empty? s2)) ()
        (element-of-set? (first s1) s2) (adjoin-set (intersection-set (rest s1) s2) (first s1))
        :else (recur (rest s1) s2)))
```

For no/n-duplicate implementation:

$$
\begin{aligned}
\text{element-of-set: }& \Theta(n)\\
\text{adjoin-set: }& \Theta(n)\\
\text{union-set: }& \Theta(n^2)\\
\text{intersection-set: }& \Theta(n^2)\\
\end{aligned}
$$

For duplicate implementation:

$$
\begin{aligned}
\text{element-of-set: }& \Theta(n)\\
\text{adjoin-set: }& \Theta(1)\\
\text{union-set: }& \Theta(n)\\
\text{intersection-set: }& \Theta(n)\\
\end{aligned}
$$

Actually, I won't use the duplicate implementation in application... Why not just use `list` or `vector`?

### Exercise 2.61

```clojure
(defn element-of-set? [x set]
  (cond (empty? set) false
        (= x (first set)) true
        (< x (first set)) false
        :else (recur x (rest set))))

(defn adjoin-set [x set]
  (cond (empty? set) (list x)
        (= x (first set)) set
        (< x (first set)) (conj set x)
        :else (conj (adjoin-set x (rest set)) (first set))))
```

This algorithm can be optimized to $O(\log n)$ with Dichotomic Search.

### Exercise 2.62

```clojure
(defn union-set [s1 s2]
  (cond (empty? s2) s1
        (empty? s1) s2
        (= (first s1) (first s2)) (conj (union-set (rest s1) (rest s2)) (first s1))
        (< (first s1) (first s2)) (conj (union-set (rest s1) s2) (first s1))
        :else (conj (union-set s1 (rest s2)) (first s2))))
```

### Exercise 2.63

#### 1)

Yes, they do.

#### 2)

`append` costs $O(n)$ in Scheme, while `cons` costs $O(1)$ in Scheme.

As a result, `tree->list-1` is $O(n^2)$, while `tree->list-2` is $O(n)$.

### Exercise 2.64

```clojure
(defn list->tree [elements]
  (defn partial-tree [elts n]
    (if (= n 0) (list nil elts)
      (let [left-size (quot (- n 1) 2)
            right-size (- n left-size 1)
            [left-tree non-left-elts] (partial-tree elts left-size)
            [cur & right-elts] non-left-elts
            [right-tree left-elts] (partial-tree right-elts right-size)]
        (list (list cur left-tree right-tree)
          left-elts))))
  (first (partial-tree elements (count elements))))

(list->tree '(1 3 5 7 9 11)); => (5 (1 nil (3 nil nil)) (9 (7 nil nil) (11 nil nil)))
```

`list->tree` is $O(n)$.

### Exercise 2.65

```clojure
(def val first)
(def L second)
(def R last)
(defn merge-seq [s1 s2]
  (cond (empty? s2) s1
        (empty? s1) s2
        (= (first s1) (first s2)) (conj (merge-seq (rest s1) (rest s2)) (first s1))
        (< (first s1) (first s2)) (conj (merge-seq (rest s1) s2) (first s1))
        :else (conj (merge-seq s1 (rest s2)) (first s2))))

(defn prefix->infix [t]
  (if (nil? t) nil
        (list (prefix->infix (L t)) (val t) (prefix->infix (R t)))))
(defn tree->list [t]
  (->> t
       (prefix->infix)
       (flatten)
       (filter #(not (nil? %)))))
(defn union-set [s1 s2] (list->tree (merge-seq (tree->list s1) (tree->list s2))))
```

### Exercise 2.66

```clojure
(defn lookup [given-key root]
  (cond (nil? root) false
        (= given-key (key root)) (val root)
        (< given-key (key root)) (recur given-key (L root))
        :else (recur given-key (R root))))
```

### Exercise 2.67

```clojure
(defn leaf [symbol weight]
  (list 'leaf symbol weight))
(defn leaf? [x] (= (first x) 'leaf))
(def symbol-leaf second)
(def weight last)

(def L first)
(def R second)
(defn symbols [x]
  (if (leaf? x) (list (symbol-leaf x)) (nth x 2)))

(defn code-tree [left right]
  (list left right (concat (symbols left) (symbols right)) (+ (weight left) (weight right))))

(defn choose-branch [bit branch]
  (cond (= bit 0) (L branch)
        (= bit 1) (R branch)
        :else (throw (Exception. (str "bad bit: CHOOSE-BRANCH `" bit "`")))))

(defn decode [bits tree]
  (defn decode-1 [bits cur]
    (if (empty? bits) ()
      (let [next (choose-branch (first bits) cur)]
        (if (leaf? next)
          (conj (decode-1 (rest bits) tree) (symbol-leaf next))
          (recur (rest bits) next)))))
  (decode-1 bits tree))

; The `make-leaf-set` implementation on the book is but a insertion sort.
; It's better to used the sort function implemented by Clojure, with a time complexity of O(nlogn)

(defn make-leaf-set [pairs]
  (->> pairs
       (sort-by weight)
       (map #(conj % 'leaf))))

(def sample-tree (code-tree (leaf 'A 4) (code-tree (leaf 'B 2) (code-tree (leaf 'D 1) (leaf 'C 1)))))

(def sample-message '(0 1 1 0 0 1 0 1 0 1 1 1 0))
```

### Exercise 2.68

```clojure
(def encode-symbol (memoize (fn [tree sym]
  (defn travel [rt cur]
    (if (leaf? rt)
        (if (= (symbol-leaf rt) sym) cur false)
      (or (travel (L rt) (conj cur 0))
           (travel (R rt) (conj cur 1)))))
  (apply list (travel tree [])))))

(defn encode [message tree]
  (if (empty? message) ()
    (concat (encode-symbol tree (first message)) (encode (rest message) tree))))
```

### Exercise 2.69

```clojure
; https://stackoverflow.com/questions/10942607/clojure-multi-maps
(ns #^{:doc "A multimap is a map that permits multiple values for each
  key.  In Clojure we can represent a multimap as a map with sets as
  values."}
  multimap
  (:use [clojure.set :only (union)]))

(defn first [mm]
  "Get the first key-value pair in the multimap. O(log(n))"
  (let [[k vs] (clojure.core/first mm)]
    [k (clojure.core/first vs)]))

(defn rest [mm]
  "Get the multimap after dropping the first key-value pair. O(log(n))"
   (let [[k v] (first mm)]
     (del mm k v)))

(defn second [mm]
  (first (rest mm)))

(defn add
  "Adds key-value pairs the multimap."
  ([mm k v]
     (assoc mm k (conj (get mm k #{}) v)))
  ([mm k v & kvs]
     (apply add (add mm k v) kvs)))

(defn del
  "Removes key-value pairs from the multimap."
  ([mm k v]
     (let [mmv (disj (get mm k) v)]
       (if (seq mmv)
         (assoc mm k mmv)
         (dissoc mm k))))
  ([mm k v & kvs]
     (apply del (del mm k v) kvs)))

(defn mm-merge
  "Merges the multimaps, taking the union of values."
  [& mms]
  (apply (partial merge-with union) mms))


(ns user)

(defn successive-merge [cnt pairs]
  (defn iter [pairs n]
    (if (= n 0) (second (multimap/first pairs))
      (let [new-node (code-tree (second (multimap/first pairs)) (second (multimap/second pairs)))
            rest-pairs (multimap/rest (multimap/rest pairs))]
        (recur (multimap/add rest-pairs (weight new-node) new-node) (- n 1)))))
  (iter pairs (- cnt 1)))

(defn huffman-tree [pairs]
  (let [cnt (count pairs)]
    (->> pairs
         (make-leaf-set)
         (reduce (fn [cur i] (multimap/add cur (weight i) i)) (sorted-map))
         (successive-merge cnt))))
```

### Exercise 2.70

```clojure
(def dictionary (huffman-tree '((A 2) (NA 16) (BOOM 1) (SHA 3) (GET 2) (YIP 9) (JOB 2) (WAH 1))))
(def message '(GET A JOB SHA NA NA NA NA NA NA NA NA GET A JOB SHA NA NA NA NA NA NA NA NA WAH YIP YIP YIP YIP YIP YIP YIP YIP YIP SHA BOOM))
(encode message dictionary); 84 bit in total
```

For a fixed-length code, it would take $36 \times 3 = 108 \text{(bits)}$.

### Exercise 2.71

I just draw it for n = 2, n = 5 and n = 10 are similar.

![A chain like Hoffman Tree for n = 2.](2-71-hoffman-tree-example.png)

It requires 1 bit to encode the most frequent symbol, while $2^n$ bit to encode the least frequent symbol.

### Exercise 2.72

It takes $O(1)$ to encode the most frequent symbol in Exercise 2.71, while $O(2^n)$ to encode the least frequent symbol in Exercise 2.71.

### Exercise 2.73

#### 1)

The code treat the exp as a general kind of data, tagged `sum` or `product`. Then it seperate the differentiation part of each implementation out of the general `deriv` function.

`number` and `variable` are special since they don't act like some operation, operating on operators and operands.

#### 2) & 3)

Clojure requires pure functional programming, so there's no way to "install" some modules.

```clojure
(defn drop-nth [n coll]
   (keep-indexed #(if (not= %1 n) %2) coll))

(def variable? symbol?)

(def operator first)
(def operands rest)

(def deriv)

(defn make-sum [a1 a2]
  (cond (= a1 0) a2
        (= a2 0) a1
        (and (number? a1) (number? a2)) (+ a1 a2)
        :else (list '+ a1 a2)))

(defn make-product [a1 a2]
  (cond (or (= a1 0) (= a2 0)) 0
        (= a1 1) a2
        (= a2 1) a1
        :else (list '* a1 a2)))

(defn make-exponentiation [u n]
  (cond (or (= n 0) (= u 1)) 1
        (= n 1) u
        :else (list '** u n)))

(def addend first)
(defn augend [exp]
  (if (= (count exp) 2) (second exp) (concat '(+) (rest exp))))

(defn deriv-+ [exp var]
  (make-sum (deriv (addend exp) var)
            (deriv (augend exp) var)))

(def multiplier first)
(defn multiplicand [exp]
  (if (= (count exp) 2) (second exp) (concat '(*) (rest exp))))

(defn deriv-* [exp var]
  (make-sum (make-product
              (multiplier exp)
              (deriv (multiplicand exp) var))
            (make-product
              (deriv (multiplier exp) var)
              (multiplicand exp))))

(def base first)
(def exponent second)
(defn deriv-** [exp var]
  (make-product (make-product
                  (exponent exp)
                  (make-exponentiation
                    (base exp)
                    (make-sum (exponent exp) -1)))
                (deriv (base exp) var)))


(def ops-map {
  ['deriv '+] deriv-+,
  ['deriv '*] deriv-*,
  ['deriv '**] deriv-**
})

(defn deriv [exp var]
  (cond (number? exp) 0
        (variable? exp)
          (if (= exp var) 1 0)
        :else
          ((get ops-map ['deriv (operator exp)]) (operands exp) var)))

```

#### 4)

In the example on the book, you should only change the implementation of `get`, `put`, and calls to them.

In my code you can just change the map `ops-map` and the calls to the function `get`.

### Exercise 2.74

```clojure
(defn get-record
  "the employee's id and the file should be supplied. "
  ([id file] ; O(n)
    (first
      (for [record file
            :let [cur-id (:id record)]
            :when (= cur-id id)] record))))

(defn find-employee-record
  "The set of all files should be supplied.
   It should be structured like this:
   '(({:id Tom :salary 10} {:id Jerry :salary 100})
     ({:id Alpha :salary 10} {:id Bravo :salary 100}))
   That is, a list of list of maps. "
  ([id files] ; O(n)
    (some #(get-record id %) files)))

(defn get-salary [id files]
  (:salary (find-employee-record id files)))
```

Only change the function `get-record`.

### Exercise 2.75

```clojure
(defn make-from-mag-ang [rho theta]
  (fn [op]
    (cond (= op 'real-part) (* rho (Math/cos theta))
          (= op 'imag-part) (* rho (Math/sin theta))
          (= op 'magnitude) rho
          (= op 'angle) theta
          :else (throw (Exception. (str "Unknown op: MAKE-FROM-MAG-ANG" op))))))
(defn apply-generic [op arg] (arg op))
```

### Exercise 2.76

For explicit dispatch:

  every operation should be implement as a conditional procudure, considering different inputs.

For data-directed style:

  operations on types forms a 2-dimension array, implementation of the operations are in the arrays.

For message-passing style:

  The operations on a specific types should always be implemented in the definition of that type.

For a system in which new types must be often added, message-passing style is more appropriate.

For a system in which new operations must often be added, explicit dispatch is more appropriate.

### Exercise 2.77

This adds a interface for the `complex` numbers, so it works.

For the second question, my implementation differs from the one on the book (I'm using clojure).

In my implementation, I straightly call the functions in the module `complex`, so no `apply-generic` is called.

The `magnitude` function calls  `complex/magnitude`, and then `base/val`.

### Exercise 2.78~2.81, 2.83 ~ 2.85

See: [sicp-solutions on my github.](https://github.com/glyh/sicp-solutions-clojure/tree/main/src/sicp_solutions_clojure/chapter_2/algebraic_system)

### Exercise 2.81

Stack overflows, since the function keeps calling itself.

### Exercise 2.82

The method mentioned in the question is not good, for example, we have type a, b and c.

Let's say a, b and c are all supertypes of some d, but there's no way to convert between them.

If so, trying to coerce between them won't lay out the result we want.

A proper way to solve this, might be treat the types relationships as a DAG. For each variable x to be applied by the operation,add a set on the node with the type in it, unioning the sets in the direction of the edges goes, and see whether there's some type have all types of inputed variables.

If there is some type fullfilled the requirements, then we can coerce to that type; If not we can't apply this method.

This is only a trivial solution. There might be better ways, but requires deeper knowledges on algorithms.

*[DAG]: Directed Acyclic Graph

*[DP]: Dynamic Programming

### Exercise 2.86

Nothing to change since ratio is treated as primitive in Clojure.

If you stick to this, we could insert some layers between `complex` and the under layers it relies on.


