# quad_roots

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma quad_roots:
  fixes x :: real
  assumes "x^2 + x - 1 = 0"
  shows "x = (-1 + sqrt 5)/2 \<or> x = (-1 - sqrt 5)/2"
proof -
  have "x^2 + x = 1" using assms by simp
  then have "x^2 + x + 1/4 = 1 + 1/4" by simp
  hence "(x + 1/2)^2 = 5/4" by sos
  then have "x + 1/2 = sqrt (5/4) \<or> x + 1/2 = - sqrt (5/4)" 
    by (smt (verit) L2_set_mult_ineq_lemma \<open>x\<^sup>2 + x = 1\<close> assms diff_add_cancel floor_one floor_zero mult_diff_mult numeral_One one_add_floor one_power2 one_power2 power2_eq_iff power2_eq_square power2_sum power_minus power_minus_Bit0 real_sqrt_ge_one real_sqrt_le_0_iff real_sqrt_le_1_iff real_sqrt_mult real_sqrt_one real_sqrt_sum_squares_mult_ge_zero real_sqrt_sum_squares_mult_squared_eq real_sqrt_zero sqrt_le_D sum_power2_eq_zero_iff zero_power2 zero_power2)
  moreover have "sqrt (5/4) = sqrt 5 / 2" by (metis dbl_inc_simps(5) dbl_simps(3) dbl_simps(5) real_sqrt_divide real_sqrt_four)
  ultimately have "x + 1/2 = sqrt 5 / 2 \<or> x + 1/2 = - sqrt 5 / 2" 
    by simp
  then have "x = (-1 + sqrt 5) / 2 \<or> x = (-1 - sqrt 5) / 2" by auto
  thus ?thesis .
qed
```


## Usage 1 of 1:
### Problem:
Task name: `amc12a_2002_p13.json`

Two different positive numbers $a$ and $b$ each differ from their reciprocals by $1$. What is $a+b$?  $ \text{(A) }1 \qquad \text{(B) }2 \qquad \text{(C) }\sqrt 5 \qquad \text{(D) }\sqrt 6 \qquad \text{(E) }3 $ Show that it is (C) \sqrt 5.
### Informal Proof:
Each of the numbers $a$ and $b$ is a solution to $\left| x - \frac 1x \right| = 1$.  Hence it is either a solution to $x - \frac 1x = 1$, or to $\frac 1x - x = 1$. Then it must be a solution either to $x^2 - x - 1 = 0$, or to $x^2 + x - 1 = 0$.  There are in total four such values of $x$, namely $\frac{\pm 1 \pm \sqrt 5}2$.   Out of these, two are positive: $\frac{-1+\sqrt 5}2$ and $\frac{1+\sqrt 5}2$. We can easily check that both of them indeed have the required property, and their sum is $\frac{-1+\sqrt 5}2 + \frac{1+\sqrt 5}2 = (C) \sqrt 5$.
### Solution:
```isabelle
theorem amc12a_2002_p13:
  fixes a b :: real
  assumes h0: "0 < a \<and> 0 < b"
      and h1: "a \<noteq> b"
      and h2: "abs (a - 1/a) = 1"
      and h3: "abs (b - 1/b) = 1" 
    shows "a + b = sqrt 5"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory amc12a_2002_p13
  imports Complex_Main
begin

(* copy of useful skill 1 *)
lemma quad_roots: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x^2 + x - 1 = 0"
  shows "x = (-1 + sqrt 5)/2 \<or> x = (-1 - sqrt 5)/2"
proof -
  have "x^2 + x = 1" using assms by simp
  then have "x^2 + x + 1/4 = 1 + 1/4" by simp
  hence "(x + 1/2)^2 = 5/4" by (simp add: power2_eq_square)
  then have "x + 1/2 = sqrt (5/4) \<or> x + 1/2 = - sqrt (5/4)" by auto
  moreover have "sqrt (5/4) = sqrt 5 / 2" by simp
  ultimately have "x + 1/2 = sqrt 5 / 2 \<or> x + 1/2 = - sqrt 5 / 2" by simp
  then have "x = (-1 + sqrt 5)/2 \<or> x = (-1 - sqrt 5)/2" by auto
  thus ?thesis .
qed

(* Lemma: For any positive real x satisfying |x - 1/x| = 1, x must equal either 
   (1+sqrt 5)/2 or (-1+sqrt 5)/2. This lemma will allow us to determine the two 
   possible values for a and b. *)
lemma pos_abs_equiv:
  fixes x :: real
  assumes "x > 0" and "abs (x - 1/x) = 1"
  shows "x = (1 + sqrt 5)/2 \<or> x = (-1 + sqrt 5)/2"
proof -
  (* Since x > 0, by splitting the definition of absolute value we have either 
     x - 1/x = 1 or 1/x - x = 1. *)
  have "x - 1/x = 1 \<or> 1/x - x = 1"
    using assms by (simp add: abs_if split: if_splits)
  then show ?thesis
  proof
    assume A: "x - 1/x = 1"
    (* Multiply both sides by x (which is positive) to obtain a quadratic:
         x^2 - 1 = x  ⟹  x^2 - x - 1 = 0 *)
    have "x^2 - x - 1 = 0" using A by (simp add: field_simps)
    (* The quadratic equation x^2 - x - 1 = 0 has solutions (1 ± sqrt 5)/2.
       Since (1 - sqrt 5)/2 is negative (because sqrt 5 > 1) and x > 0,
       it follows that x = (1 + sqrt 5)/2. *)
    then have "x = (1 + sqrt 5)/2 \<or> x = (1 - sqrt 5)/2"
      by (simp add: quadratic_formula)
    then show "x = (1 + sqrt 5)/2 \<or> x = (-1 + sqrt 5)/2"
      using assms by auto
  next
    assume B: "1/x - x = 1"
    (* Multiply both sides by x to obtain:
         1 - x^2 = x  ⟹  x^2 + x - 1 = 0 *)
    have "x^2 + x - 1 = 0" using B by (simp add: field_simps)
    (* By lemma quad_roots, the quadratic equation x^2 + x - 1 = 0 has solutions: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
         x = (-1 + sqrt 5)/2 or x = (-1 - sqrt 5)/2.
       Since (-1 - sqrt 5)/2 is negative and x > 0, we deduce x = (-1 + sqrt 5)/2. *)
    then have "x = (-1 + sqrt 5)/2 \<or> x = (-1 - sqrt 5)/2"
      using quad_roots by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    then show "x = (1 + sqrt 5)/2 \<or> x = (-1 + sqrt 5)/2"
      using assms by auto
  qed
qed

(* formal statement copied from the input *)
theorem amc12a_2002_p13:
  fixes a b :: real
  assumes h0: "0 < a \<and> 0 < b"
      and h1: "a \<noteq> b"
      and h2: "abs (a - 1/a) = 1"
      and h3: "abs (b - 1/b) = 1" 
    shows "a + b = sqrt 5"
proof -
  (* Apply the pos_abs_equiv lemma separately to a and b to determine their possible values. *)
  have A: "a = (1 + sqrt 5)/2 \<or> a = (-1 + sqrt 5)/2"
    using h0 h2 pos_abs_equiv by auto
  have B: "b = (1 + sqrt 5)/2 \<or> b = (-1 + sqrt 5)/2"
    using h0 h3 pos_abs_equiv by auto
  (* Since a and b are different positive numbers (by h1), one must be (1+sqrt5)/2 
     and the other (-1+sqrt5)/2. *)
  then have "a + b = (1 + sqrt 5)/2 + (-1 + sqrt 5)/2"
    using h1 by auto
  (* Simplifying the sum gives:
         (1 + sqrt 5)/2 + (-1 + sqrt 5)/2 = ( (1-1) + 2*sqrt 5 )/2 = sqrt 5 *)
  thus "a + b = sqrt 5" by simp
qed

end
```
