---
title: "SICP Solutions in Clojure (Chapter 1)"
date: 2021-02-03T16:39:00+08:00
categories: ["IT", "science"]
tags: ["algorithms", "principles", "LISP"]
draft: false
---


I'm learning Clojure and SICP these days, and trying to finish the exercises on 
the SICP.

<!--more-->

### Exercise 1.1

```clojure 
(let [a 3 b (+ a 1)]
(doseq [x [10
           (+ 5 3 4)
           (- 9 1)
           (/ 6 2)
           (+ (* 2 4) (- 4 6))
           (+ a b (* a b))
           (= a b)
           (if (and (> b a) (< b (* a b))) b a)
           (cond (= a 4) 6 (= b 4) (+ 6 7 a) :else 25)
           (+ 2 (if (> b a) b a))
           (* (cond (> a b) a (< a b) b :else -1) (+ a 1))]]
 (println x)))
```

### Exercise 1.2

```clojure
(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 3))))) (* 3 (- 6 2) (- 2 7)))
```

### Exercise 1.3

```clojure
(defn sum-of-sqaures-of-two-biggest [a b c]

(let [s (vec (sort [a b c])) sec (second s) thi (last s)]
  (+ (* sec sec) (* thi thi))))
(println (sum-of-sqaures-of-two-biggest 1 3 2))
```

### Exercise 1.4

Just as the function's name, the function will return  $a + \lvert b \rvert$ .

### Exercise 1.5

The following form doesn't have a valid syntax in Clojure.

```clojure
(def (p) (p))
```

Let's suppose it is valid. 

If we're under applicative-order evaluation, the function will return 0, since \(p\) is not evaluated. 

If we're under normal-order evaluation, the function will fall in to a dead loop.

### Exercise 1.6

This would fall into a dead loop. 

Different from evaluation of the special form `cond`, the function call requires every parameter to be evaluated.

There is only one exit in the `sqrt-iter`, which calls `sqrt-iter` itself, result in a dead loop.

### Exercise 1.7

```clojure
(defn abs[x] 
  (if (< x 0) (- x) x))

(def eps 1e-8)

(defn sqrt
  ([x] (sqrt x 1 0))
  ([x guess last-guess]
    (if (< (abs (- guess last-guess)) eps) 
      guess 
      (recur x (double (/ (+ guess (/ x guess)) 2)) guess))))
      ; use `double` to convert ratio to float numbers, avoiding overflow. 

(println (sqrt 121))
```

### Exercise 1.8

```clojure
(defn abs
  [x] (if (< x 0) (- x) x))

(def eps 1e-8)

(defn cube-root
  ([x] (cube-root x 1 0))
  ([x guess last-guess]
    (if (< (abs (- guess last-guess)) eps) 
      guess 
      (recur x 
             (double (/ (+ (* 2 guess) (/ x (* guess guess))) 3)) 
             guess))))

(println (cube-root 0.00483))
```

### Exercise 1.9

The first one is recursive while the second one is iterative.

### Exercise 1.10

```clojure
(defn A [x y]
  (cond (= y 0) 0
    (= x 0) (* 2 y)
    (= y 1) 2
    :else (A (- x 1) (A x (- y 1)))))

(doseq [v [[1 10] [2 4] [3 3]]] 
  (println (apply A v)))

(defn f
  "Calculate 2 * n"
  [n] (A 0 n))

(defn g
  "Calculate 2 ^ n"
  [n] (A 1 n))

(defn h
  "Calculate 2 ^ 2 ^ 2 ^ 2 ^ 2 ... ^ 2 (there are n 2's in total)"
  [n] (A 2 n))

(println (f 3) (g 3) (h 3))
```

### Exercise 1.11

```clojure
(defn f
    ([n] (if (< n 3) n (f (- n 2) 2 1 0)))
    ([n a b c] (if (= n 0) a (recur (- n 1) (+ a (* 2 b) (* 3 c)) a b))))

(println (f 5))
```

### Exercise 1.12

```clojure
(defn pascal-triangle
  ([n] (pascal-triangle n [[1]]))
  ([n l] 
    (if (= 1 n) 
      l 
      (recur (- n 1) 
             (conj l (vec (map + 
             (conj (last l) 0) 
             (cons 0 (last l)))))))))

(prn (pascal-triangle 5))
```

### Exercise 1.13

$$
\lvert Fib(n) - \frac{\phi^n}{5} \rvert = \frac{\psi^n}{5} < \frac{\psi}{5} < \frac{1}{2},\square.
$$

\(To be continued ...\)

### Exerciese 1.14

#### Graph

{{<mermaid>}}
graph TD;
A{"f(11, 5)"} --> B("f(-39, 5)")
A --> C{"f(11, 4)"}
C --> D("f(-14, 4)")
C --> E{"f(11, 3)"}
E --> F{"f(1, 3)"}
E --> G{"f(11, 2)"}
F --> H("f(-9, 3)")
F --> I{"f(1, 2)"}
G --> J{"f(6, 2)"}
G --> K{"f{11,1}"}
I --> L("f(-4, 2)")
I --> M{"f(1, 1)"}
M --> N("f(0, 1)")
style N fill:#4caf50
M --> O("f(1, 0)")
J --> I 
K --> P{"f(10, 1)"}
K --> Q("f(11, 0)")
P --> R{"f(9, 1)"}
P --> S("f(10, 0)")
R --> T{"f(8, 1)"}
R --> U("f(9, 0)")
T --> V{"f(7, 1)"}
T --> W("f(8, 0)")
V --> X{"f(6, 1)"}
J --> X
V --> Y("f(7, 0)")
X --> Z{"f(5, 1)"}
X --> AA("f(6, 0)")
Z --> AB{"f(4, 1)"}
Z --> AC("f(5, 0)")
AB --> AD{"f(3, 1)"}
AB --> AE("f(4, 0)")
AD --> AF{"f(2, 1)"}
AD --> AG("f(3, 0)")
AF --> M
AF --> AH("f(2, 0)")
{{</mermaid>}}

#### Space complexity

It’s easy to observe the space complexity is $O(max\{m, n\})$. 

#### Time complexity 

Let's suppose n be the money to be changed, m be the count of type of coins, $V_m$ be the denomination of the coin of mth type.

The following is only a rough estimate. 

$$
\begin{aligned}
&T(n, m) &=& \sum_{i=0}^{\lceil\frac{n}{V_m}\rceil}T(n-iV_m, m-1)+O(1)& \\
&&=&O(\lceil\frac{n}{V_m}\rceil T(n, m-1))& \\
&&=&O(\prod_{i=1}^{m}\lceil\frac{n}{V_m}\rceil T(n, 0))& \\
&&=&O(n^m)&
\end{aligned}
$$

For m = 5, there  there is a closer estimate, implying that this algorithm has a time complexity of $\Theta(n^5)$ in [codology.net](https://codology.net/post/sicp-solution-exercise-1-14/).

#### Optimization on time complexity

If you examine the “tree” given before, you’ll realize that it’s actually not a tree. It’s a topological graph.

In the original tree, there is a lot of repeating tree nodes, calculating the same value of the recursive function.

If we save the value of every calculated function, the time complexity will be $O(nm)$ , since there are only $n \times m$ states in total.

For Clojure, using `memoize` will simply complete the job for you.

However, the space complexity will fall to $O(n \times m)$ , but usally the optimization as a whole is a great deal.

This kind of way of solving problems are actually DP. Notice: This kind of optimization only works for referentially transparent functions, that is, the function’s output only relates to its input.

*[DP]: Dynamic Programming

### Exercise 1.15

#### a)

Solve the inequality $\lvert\frac{\theta}{3^n}\rvert \leq 0.1(\theta = 12.15)$ yields $n_{min} = 5$ .

Therefore, the function p is called 5 times.

#### b) Time & space complexity

$$
\begin{aligned}
&T(p(x))&=&O(1)& \\
&T(sine(x))&=&\left\{\begin{aligned}
&T(sine(\frac{x}{3})) + T(p(x)),  &\forall \lvert x\rvert > 0.1& \\
&O(1), &\forall \lvert x\rvert \le 0.1&
\end{aligned}\right.& \\
&&=&O(log(n))&
\end{aligned}
$$

The space complexity is the same as time complexity.

### Exercise 1.16

```clojure 
(defn fast-expt
  ([b n] (fast-expt 1N b n))
  ([a b n]
    (cond (= n 0) a
          (even? n) (recur a (* b b) (/ n 2))
          :else (recur (* a b) b (- n 1)))))

(fast-expt 9321233N 112N)
```

### Exercise 1.17

```clojure
(def _double #(* % 2))

(def _half #(/ % 2))

(defn fast-mul
  [a b] (cond (= b 0) 0
              (even? b) (fast-mul (_double a) (_half b))
              :else (+ a (fast-mul a (- b 1))))

(fast-mul 12321411231231231N 12423112312312312321N)
```

### Exercise 1.18

```clojure
(def _double #(* % 2))

(def _half #(/ % 2))

(defn fast-mul
  ([a b] (fast-mul a b 0N))
  ; a * b + cur = constant
  ([a b cur] (cond (= b 0) cur
                   (even? b) (recur (_double a) (_half b) cur)
                   :else (recur a (- b 1) (+ cur a)))))

(fast-mul 12321411231231231N 12423112312312312321N)
```

### Exercise 1.19

This is an application of Exponentiation by [squaring](https://en.wikipedia.org/wiki/Exponentiation_by_squaring).

$$
\begin{aligned}
\text{Let A be a } 2 \times 2 \text{ matrix, s.t.} \\
A \times \begin{bmatrix} b \\ a \end{bmatrix} = \begin{bmatrix} bp+aq \\bq+aq+ap \end{bmatrix} \\
\text{We have } A = \begin{bmatrix} p & q \\ q & p+q \end{bmatrix} \\
A^2 = \begin{bmatrix} p^2+q^2 & 2pq+q^2 \\ 2pq+q^2 & p^2 + 2pq + 2q^2 \end{bmatrix} \\
p'=p^2+q^2, q'=2pq+q^2
\end{aligned}
$$

```clojure
(defn fib
  ([n] (fib 1N 0N 0N 1N n))
  ([a b p q cnt] 
    (cond (= cnt 0) b
          (even? cnt) (recur a b 
                             (+ (* p p) (* q q)) 
                             (+ (* q q) (* 2 p q))
                             (/ cnt 2))
          :else (recur (+ (* b q) (* a q) (* a p)) 
                       (+ (* b p) (* a q))
                       p
                       q
                       (- cnt 1)))))

(fib 10000)
```

### Exercise 1.20

Applicative order evaluation, applying the mod operation for 4 times.

```clojure
(gcd 206 40); => (Call once)

(if (= 40 0) 206 (gcd 40 (rem 206 40))); =>

(gcd 40 ( 206 40)); =>

(gcd 40 6); => (Call twice)

(if (= 6 0) 40 (gcd 6 (rem 40 6))); =>

(gcd 6 (rem 40 6)); =>

(gcd 6 4); => (Call 3 times)

(if (= 4 0) 6 (gcd 4 (rem 6 4))); =>

(gcd 4 (rem 6 4)); =>

(gcd 4 2); => (Call 4 times)

(if (= 2 0) 4 (gcd 2 (rem 4 2))); =>

(gcd 2 (rem 4 2)); =>

(gcd 2 0); => (Call 5 times)

(if (= 0 0) 2 (gcd 2 (rem 2 0))); =>

2
```

Normal order evaluation:

```clojure
(if (= 40 0) 206 (gcd 40 (rem 206 40))); =>

(if (= 40 0) 
  206 
  (if (= (rem 206 40) 0) 
    40 
    (gcd (rem 206 40) (rem 40 (rem 206 40))))); =>

(if (= 40 0) 
  206 
  (if (= (rem 206 40) 0) 
    40 
    (if (= (rem 40 (rem 206 40)) 0) 
      (rem 206 40)
      (gcd (rem 40 (rem 206 40)) (rem (rem (206 40)) (rem 40 (rem 206 40))))))); =>

......
```

Suppose after expanding the ith `gcd`, we call `rem` f(i) times, then:

$$
\begin{aligned}
&f(0)&=&0& \\
&f(i+1)&=&3f(i)+1&
\end{aligned}

$$

In the applicative order, gcd is called 5 times, so the answer is:

$$

f(5) = 3^5(f(0)+\frac{1}{2})-\frac{1}{2}=121

$$

### Exercise 1.21

```clojure
(defn smallest-divisor
  ([n] (smallest-divisor n 2))
  ([n test-divisor] (cond (> (* test-divisor test-divisor) n) n
                          (= (rem n test-divisor) 0) test-divisor
                          :else (recur n (+ test-divisor 1)))))

(map smallest-divisor [199 1999 19999])
```

### Exercise 1.22

```clojure
(defn prime? [x] (every? #(not= (mod x %) 0) (range 2 (+ 1 (int (Math/sqrt x))))))

(defn range-to-inf [low-bound] (iterate inc low-bound))

(defn prime-seq [low-bound] (filter prime? (range-to-inf low-bound)))

(doseq [x [1000 10000 100000 1000000]]
    (time (prn (take 3 (prime-seq x)))))
```

Output:

> (1009 1013 1019)
> 
> “Elapsed time: 0.676343 msecs”
> 
> (10007 10009 10037)
> 
> “Elapsed time: 1.799251 msecs”
> 
> (100003 100019 100043)
> 
> “Elapsed time: 2.813975 msecs”
> 
> (1000003 1000033 1000037)
> 
> “Elapsed time: 2.98355 msecs”
> 
> nil

![A line with a sqaure-root-function look.](/images/sicp-solutions-in-clojure-chapter-1/1-22-time-input-scale-line-plot.svg)

This verrified the assumption of the order of growth of the `prime?` function. 

### Exercise 1.23

```clojure 
(defn smallest-divisor
  ([n] (smallest-divisor n 2))
  ([n test-divisor] (cond (> (* test-divisor test-divisor) n) n
                          (= (rem n test-divisor) 0) test-divisor
                          :else (recur n (+ test-divisor 1)))))

(defn smallest-divisor-improved
  ([n] (smallest-divisor-improved n 2))
  ([n test-divisor] (cond (> (* test-divisor test-divisor) n) n
                          (= (rem n test-divisor) 0) test-divisor
                          :else (recur n (if (= test-divisor 2) 3 (+ test-divisor 2))))))

(doseq [x [1009 1013 1019 10007 10009 10037 100003 100019 100043 1000003 1000033 1000037]
       y [smallest-divisor smallest-divisor-improved]]
  (println (str "Testing " x " on " y))
  (println (time (y x))))
```

![Two lines having a portion less than 2](/images/sicp-solutions-in-clojure-chapter-1/1-23-time-input-scale-line-plot.svg)

A guess: Executing the if statements cost time. 

### Exercise 1.24

```clojure
(defn expmod 
  "Calculate a^b%p"
  [a b p] 
  (cond (= 0 b) 1
        (even? b)
          (let [h (expmod a (/ b 2) p)]
            (rem (* h h) p))
        :else
          (rem (* a (expmod a (- b 1) p)) p))) 

(defn fermat-test [n]
  (let [rnd (bigint (+ 1 (rand (- n 1))))]
    (= (expmod rnd n n) rnd)))

(defn fast-prime? [x times]
  (cond (= 0 times) true
        (fermat-test x) (recur x (- times 1))
        :else false))
(fast-prime? 1000000007 1000)
(doseq [x [1009 1013 1019 10007 10009 10037 100003 100019 100043 1000003 1000033 1000037]]
  (time (fast-prime? x 1000)))
```

![A line with an log-function look, however a point is strange](/images/sicp-solutions-in-clojure-chapter-1/1-24-time-input-scale-line-plot.svg)

This nearly consistents with my guess that the time consumed is proportional to the order of the magnitude of the input. 

However a strange point does not consist with my guess. 

### Exercise 1.25

She is wrong. The memory is limited, so there's no point to store a huge number. 

If we compute exponentials then take remainders, it may overflow in many cases. 

On the contrary, taking remainders after every time we do a multiplication will reduce the probability of math overflow. 

### Exercise 1.26

$$
\begin{aligned}
&T(n) &=& \left\{ \begin{aligned} 
& 2T(\frac{n}{2}) + O(1) &, &n \equiv 0 \pmod 2& \\
& T(n-1) + O(1) &, & n \equiv 1 \pmod 2&
\end{aligned}\right. &\\
&&=&\Theta(n+\log n)&\\
&&=&O(n)&
\end{aligned}
$$

### Exercise 1.27

```clojure
(defn expmod 
  "Calculate a^b%p"
  [a b p] 
  (cond (= 0 b) 1
        (even? b)
          (let [h (expmod a (/ b 2) p)]
            (rem (* h h) p))
        :else
          (rem (* a (expmod a (- b 1) p)) p))) 

(defn carmichael? [n] (every? #(= (expmod % n n) %) (range 2 n)))

(every? carmichael? [561 1105 1729 2465 2821 6601])
```

### Exercise 1.28

```clojure
(defn expmod 
  "Calculate a^b%p"
  [a b p] 
  (cond (= 0 b) 1
        (even? b)
          (let [h (expmod a (/ b 2) p) sq (rem (* h h) p)]
            (if (and (= sq 1) (not= h 1) (not= h (- p 1))) 0 sq))
        :else
          (rem (* a (expmod a (- b 1) p)) p))) 

(defn miller-rabin [n]
  (let [rnd (bigint (+ 1 (rand (- n 1))))]
    (not= (expmod rnd n n) 0)))

(defn fast-prime? [x times]
  (cond (= 0 times) true
        (miller-rabin x) (recur x (- times 1))
        :else false))

(some #(fast-prime? % 1000) [561 1105 1729 2465 2821 6601])
```

### Exercise 1.29

```clojure
(def cube #(* % % %))

(def sum #(reduce + %))

(defn integral [f a b dx]
  (* dx (sum (map f (range a (+ b dx) dx)))))

(defn simpson [f a b n]
  (let [h (/ (- b a) n) h2 (+ h h)]
    (* (/ h 3) 
      (+ (f a) (f b)
         (* 2 (sum (map f (range (+ a h2) (- b h) h2))))
         (* 4 (sum (map f (range (+ a h) b h2))))))))

(println (str "dx=0.01: " (integral cube 0 1 (/ 100)) " " (simpson cube 0 1 100)))
(println (str "dx=0.001: " (integral cube 0 1 (/ 1000)) " " (simpson cube 0 1 1000)))
```

### Exercise 1.30

```clojure
(defn sum [term a next b] ; avoid using 0 since the function might work not only for numbers
  (defn iter [x result]
    (if (= x b) 
        (term b)
        (recur (next x) (+ (term x) result))))
  (iter (next a) (term a)))
```

### Exercise 1.31

#### a)

```clojure
(defn product [term a next b]
  (if (= a b)
    (term a)
    (* (term a)
       (product term (next a) next b))))

(defn factorial [x] (product identity 1 #(+ % 1) x))

(defn approximate-pi-quarter [n] (product #(double (/ (- (* % %) 1) (* % %))) 3 #(+ % 2) (+ n n 1)))
```

#### b)

```clojure
(defn product 
  ([term a next b] 
    (product term (next a) next b (term a)))
  ([term a next b result]
    (if (> a b) result (recur term (next a) next b (* (term a) result)))))
```

### Exercise 1.32

Actually, `accumulate` is the function `reduce` implemented in Clojure.

There is a difference, that is accumulate is right-fold while reduce is left-fold. 

See [more about fold on wikipedia](https://en.wikipedia.org/wiki/Fold_(higher-order_function). 

#### a)

```clojure
(defn accumulate [combiner null-value term a next b]
  (if (= a b) (combiner null-value (term a))
              (recur combiner (combiner null-value (term a)) term (next a) next b)))

(defn sum [term a next b] (accumulate + 0 term a next b))

(defn product [term a next b] (accumulate * 1 term a next b))
```

#### b)

```clojure
(defn accumulate [combiner null-value term a next b]
  (if (= a b) (combiner null-value (term a))
              (combiner a (accumulate combiner null-value term (next a) next b))))
```

### Exercise 1.33

```clojure
(defn filtered-accumulate [combiner null-value term a next b predicate]
  (if (= a b) (if (predicate a) (combiner null-value a) null-value)
              (if (predicate a) (recur combiner (combiner null-value (term a)) term (next a) next b predicate)
                                (recur combiner null-value term (next a) next b predicate))))

(defn prime? [x] (every? #(not= (mod x %) 0) (range 2 (+ 1 (int (Math/sqrt x))))))

(defn func-a [a b] (filtered-accumulate + 0 #(* % %) a #(+ % 1) b prime?))

(defn gcd [a b] (if (= b 0) a (recur b (rem a b))))

(defn func-b [n] (filtered-accumulate * 1 identity 2 #(+ % 1) (- n 1) #(= (gcd % n) 1)))
```

### Exercise 1.34

```clojure
(defn f [g] (g 2))

(f f); =>

(f 2); => 

; Execution error (ClassCastException) at user/f (REPL:1).
; class java.lang.Long cannot be cast to class clojure.lang.IFn.

```

### Exercise 1.35

$$
\phi = \frac{\sqrt5+1}2, \frac1\phi+1 = \frac{\sqrt5+1}2 = \phi
$$

```clojure
(def tolerance 1e-5)

(def abs #(if (< % 0) (- %) %))

(defn fixed-point [f initial]
  (def close? #(< (abs (- %1 %2)) tolerance))
  (defn _try [guess] ; `try` is a special form in Clojure. 
    (let [next (f guess)]
      (if (close? guess next) next (recur next))))
  (_try initial))

(fixed-point #(+ 1 (/ %)) 1)
```

### Exercise 1.36

```clojure
(def tolerance 1e-5)

(def abs #(if (< % 0) (- %) %))

(defn fixed-point [f initial]
  (def close? #(< (abs (- %1 %2)) tolerance))
  (defn _try [guess] ; `try` is a special form in Clojure. 
    (println guess)
    (let [next (f guess)]
      (if (close? guess next) next (recur next))))
  (_try initial))

(defn average-damp [f] #(/ (+ (identity %) (f %)) 2))

(def f #(/ (Math/log 1000) (Math/log %)))

(fixed-point f 2)
(println)
(fixed-point (average-damp f) 2)
```

Output:

> 9.965784284662087
>
> 3.004472209841214
>
> 6.279195757507157
>
> 3.759850702401539
>
> 5.215843784925895
>
> 4.182207192401397
>
> 4.8277650983445906
>
> 4.387593384662677
>
> 4.671250085763899
>
> 4.481403616895052
>
> 4.6053657460929
>
> 4.5230849678718865
>
> 4.577114682047341
>
> 4.541382480151454
>
> 4.564903245230833
>
> 4.549372679303342
>
> 4.559606491913287
>
> 4.552853875788271
>
> 4.557305529748263
>
> 4.554369064436181
>
> 4.556305311532999
>
> 4.555028263573554
>
> 4.555870396702851
>
> 4.555315001192079
>
> 4.5556812635433275
>
> 4.555439715736846
>
> 4.555599009998291
>
> 4.555493957531389
>
> 4.555563237292884
>
> 4.555517548417651
>
> 4.555547679306398
>
> 4.555527808516254
>
> 4.555540912917957
>
> 4.555532270803653
>
> ~
>
> 5.9828921423310435
>
> 4.922168721308343
>
> 4.628224318195455
>
> 4.568346513136242
>
> 4.5577305909237005
>
> 4.555909809045131
>
> 4.555599411610624
>
> 4.5555465521473675
>
> 4.555537551999825
>

Without average-damping, the fixed-point function took 34 steps; 

With average-damping, the fixed-point function took 9 steps. 

Notice: average-damping won't always improve the performance of your program. you can try this:

```clojure
(def f #(/ % 2))
(fixed-point f 1/2)
(println)
(fixed-point (average-damp x) 1/2)
```

Average-damping improve the performance of the fixed-point function, if the applying multiple times f on some x results in the output keeping taking turns. 

That property doesn't hold for every function. 

### Exercise 1.37

```clojure
(defn cont-frac 
  ([n d k] (cont-frac n d k 0)) 
  ([n d k result] 
    (if (= k 0) result
                (recur n d (- k 1) (/ (n k) (+ result (d k)))))))

(def c1 (constantly 1))

(double (cont-frac c1 c1 10)) ;=> 0.6179775280898876
(double (cont-frac c1 c1 11)) ;=> 0.6180555555555556
```

### Exercise 1.38

```clojure
(def d #(if (= (rem % 3) 2) (* (+ % 1) 2/3) 1))
(+ 2 (cont-frac (constantly 1) d 100 0.0)) ; Use double initial to avoid ratio (ratio is slow)
```

### Exercise 1.39

```clojure
(defn tan-cf [x k] (/ (cont-frac (constantly (- (* x x))) #(- (+ % %) 1) k 0.0) (- x)))
```

### Exercise 1.40

```clojure
(def dx 1e-5)

(defn deriv [g] #(/ (- (g (+ % dx)) (g %)) dx)) 

(defn newton-transform [g] #(- % (/ (g %) ((deriv g) %)))) 

(defn newtons-method [f initial] (fixed-point (newton-transform f) initial))

(defn cubic [a b c] (+ (* x x x) (* a x x) (* b x) c))
```

### Exercise 1.41

```clojure
(defn _double [f] #(f (f %)))

(((_double (_double _double)) #(+ % 1)) 5); => 21

```

### Exercise 1.42

`compose` is built-in in Clojure as `comp`.

```clojure
(defn compose [f g] #(f (g %)))
```

### Exercise 1.43

```clojure
(defn repeated [f n]
  (if (= n 0) identity #(f ((repeated f (- n 1)) %)))) 
```

### Exercise 1.44

```clojure
(def dx 1e-5)

(defn smooth 
  ([f] (smooth f 1))
  ([f n] 
    (if (= n 0) f
      (let [g (smooth f (- n 1))]
        #(/ (+ (g %) (g (- % dx)) (g (+ % dx))) 3)))))
```
### Exercise 1.45

```clojure
(defn iterative-improve 
  [good? improve]
  (fn [initial]
    (defn _try [guess]
      (let [next (improve guess)]
        (if (good? guess) next (recur next))))
    (_try initial)))

(def tolerance 1e-5)
(def abs #(if (< % 0) (- %) %))
(def close? #(< (abs (- %1 %2)) tolerance))

(defn fixed-point [f initial] ((iterative-improve #(close? % (f %)) f) initial))

(defn sqrt [x] 
  (defn improve [guess] (double (/ (+ guess (/ x guess)) 2)))
  ((iterative-improve #(close? % (improve %)) improve) 1)) 
```
