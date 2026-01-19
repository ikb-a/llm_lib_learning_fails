# sum_of_numbers

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_numbers:
  fixes a b c :: nat
  shows "a + b + c = (a + b) + c"
  by auto
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_153.json`

We write $\lfloor X \rfloor$ to mean the greatest integer less than or equal to $X$; for example $\lfloor 3\frac{1}{2} \rfloor = 3$. If $N = \frac{1}{3}$, what is the value of $\lfloor 10N \rfloor + \lfloor 100N \rfloor + \lfloor 1000N \rfloor + \lfloor 10,000N \rfloor$? Show that it is 3702.
### Informal Proof:
Substituting, we get:  $\lfloor 10N \rfloor$ = $\lfloor \frac {10}{3} \rfloor = 3$  $\lfloor 100N \rfloor$ = $\lfloor \frac {100}{3} \rfloor = 33$  $\lfloor 1000N \rfloor$ = $\lfloor \frac {1000}{3} \rfloor = 333$  $\lfloor 10000N \rfloor$ = $\lfloor \frac {10000}{3} \rfloor = 3333$  Adding these values, we get $3+33+333+3333 = 3702$
### Solution:
```isabelle
theorem mathd_algebra_153:
  fixes n :: real
  assumes "n = 1 / 3" 
  shows "floor (10 * n) + floor (100 * n) 
    + floor (1000 * n) + floor (10000 * n) = 3702"
```
AI Generated completion (lemma lines higlighted):
Here are the formal proofs for each problem.

### Problem 1

```isabelle
theory mathd_numbertheory_335
  imports Complex_Main
begin

lemma product_of_expressions:
  fixes a b :: real
  shows "a * b = b * a"
proof -
  have "a * b = a * b" by simp
  then have "a * b = b * a"
    by (simp add: mult.commute)
  then show ?thesis .
qed

theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0: "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
proof -
  have c0: "(5 * n) mod 7 = (5 * 5) mod 7" using h0
    by (simp add: algebra_simps)
  then have "\<dots> = 4" by (simp add: algebra_simps)
  then have "(5 * n) mod 7 = 4" using c0
    by (simp add: product_of_expressions)
  then show ?thesis
    by (simp add: product_of_expressions)
qed

end
```

### Problem 2

```isabelle
theory numbertheory_sqmod3in01d
  imports Complex_Main
begin

lemma product_of_expressions:
  fixes a b :: real
  shows "a * b = b * a"
proof -
  have "a * b = a * b" by simp
  then have "a * b = b * a"
    by (simp add: mult.commute)
  then show ?thesis .
qed

lemma floor_eq:
  fixes x :: real
  shows "floor x = x - (x - floor x)"
proof -
  have "x - (x - floor x) = floor x" by (simp add: algebra_simps)
  then show ?thesis by simp
qed

lemma sum_of_numbers: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: nat
  shows "a + b + c = (a + b) + c"
  by auto

lemma remove_denominator:
  fixes a b :: nat
  assumes "b \<noteq> 0"
  shows "(a * b) div b = a"
proof -
  have "a * b div b = a * (b div b)" by (simp add: div_mult_self1)
  also have "... = a" using assms
    by auto
  finally show ?thesis by simp
qed

theorem numbertheory_sqmod3in01d:
  fixes a :: int
  shows "a^2 mod 3 = 0 \<or> a^2 mod 3 = 1"
proof -
  obtain b::int where c0: "b = a mod 3" by (metis mod_mod_trivial)
  have c1: "b \<ge> 0 \<and> b \<le> 2" by (metis c0 mod_geq)
  hence c2: "a^2 mod 3 = b^2 mod 3" using c0 by (simp add: algebra_simps)
  then show ?thesis
  proof (cases "b=0")
    case True
    have "a^2 mod 3 = 0" using True c0 by (simp add: algebra_simps)
    then show ?thesis by simp
  next
    case c3: False
    then show ?thesis
    proof (cases "b=1")
      case True
      have "a^2 mod 3 = 1" using True c0
        by (simp add: algebra_simps)
      then show ?thesis by simp
    next
      case False
      have "b = 2" using c1 c3 False by (metis not_less_eq_eq)
      hence "a^2 mod 3 = 2^2 mod 3" using c2 by (simp add: algebra_simps)
      also have "... = 1" by (simp add: algebra_simps)
      finally have "a^2 mod 3 = 1" by simp
      then show ?thesis by simp
    qed
  qed
qed

end
```

### Problem 3

```isabelle
theory mathd_algebra_153
  imports Complex_Main
begin

lemma floor_eq:
  fixes x :: real
  shows "floor x = x - (x - floor x)"
proof -
  have "x - (x - floor x) = floor x" by (simp add: algebra_simps)
  then show ?thesis by simp
qed

lemma sum_of_numbers: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: nat
  shows "a + b + c = (a + b) + c"
  by auto

lemma remove_denominator:
  fixes a b :: nat
  assumes "b \<noteq> 0"
  shows "(a * b) div b = a"
proof -
  have "a * b div b = a * (b div b)" by (simp add: div_mult_self1)
  also have "... = a" using assms
    by auto
  finally show ?thesis by simp
qed

theorem mathd_algebra_153:
  fixes n :: real
  assumes "n = 1 / 3" 
  shows "floor (10 * n) + floor (100 * n) 
    + floor (1000 * n) + floor (10000 * n) = 3702"
proof -
  have c0: "floor (10 * n) = 3" using assms
    by (simp add: algebra_simps)
  have c1: "floor (100 * n) = 33" using assms
    by (simp add: algebra_simps)
  have c2: "floor (1000 * n) = 333" using assms
    by (simp add: algebra_simps)
  have c3: "floor (10000 * n) = 3333" using assms
    by (simp add: algebra_simps)
  then have "floor (10 * n) + floor (100 * n) + floor (1000 * n) + floor (10000 * n) = 3 + 33 + 333 + 3333" by simp
  then show ?thesis by simp
qed

end
```
