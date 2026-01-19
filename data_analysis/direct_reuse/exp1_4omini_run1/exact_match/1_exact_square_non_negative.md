# square_non_negative

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma square_non_negative:
  fixes x :: real
  shows "x^2 \<ge> 0"
  by (simp add: mult_nonneg_nonneg)
```


## Usage 1 of 1:
### Problem:
Task name: `algebra_sqineq_unitcircatbpabsamblt1.json`

Let $a$ and $b$ be real numbers such that $a^2+b^2=1$. Show that $ab+\lvert a-b\rvert \leq 1$.
### Informal Proof:
We have that $0 \leq (a-b+1)^2 = a^2+b^2+1-2ab+2a-2b$. Since $a^2+b^2=1$, the inequality becomes $0 \leq 2-2ab+2a-2b$, so $0 \leq 1-ab+a-b$. Similarly, by expanding $0 \leq (b-a+1)^2$ we have that $0 \leq 1-ba+b-a$. Combining these two inequalities, we have that $ab+\lvert a-b\rvert \leq 1$.
### Solution:
```isabelle
theorem algebra_sqineq_unitcircatbpabsamblt1:
  fixes a b :: real
  assumes h0: "a^2 + b^2 = 1" 
  shows "a * b + \<bar>a - b\<bar> \<le> 1"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory algebra_sqineq_unitcircatbpabsamblt1
  imports Complex_Main
begin

(* Lemma to show that the square of any real number is non-negative *)
lemma square_non_negative: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  shows "x^2 \<ge> 0"
  by (simp add: mult_nonneg_nonneg)

(* Formal statement copy from the input *)
theorem algebra_sqineq_unitcircatbpabsamblt1:
  fixes a b :: real
  assumes h0: "a^2 + b^2 = 1" 
  shows "a * b + \<bar>a - b\<bar> \<le> 1"
proof -
  (* Step 1: Start with the given condition \( a^2 + b^2 = 1 \). *)
  
  (* Step 2: Consider the expression \( |a - b| \). We express this as \( |a - b| = \sqrt{(a - b)^2} \). *)
  have abs_diff: "\<bar>a - b\<bar> = sqrt ((a - b)^2)" by (rule abs_diff_square)

  (* Step 3: Expand \( (a - b)^2 \) to get \( (a - b)^2 = a^2 - 2ab + b^2 \). *)
  have "(a - b)^2 = a^2 - 2*a*b + b^2" by (simp add: power2_eq_square)

  (* Step 4: Substitute \( a^2 + b^2 = 1 \) into the expanded expression: \( (a - b)^2 = 1 - 2ab \). *)
  have diff_square: "(a - b)^2 = 1 - 2*a*b" using h0 by simp

  (* Step 5: Therefore, we have \( |a - b| = \sqrt{1 - 2ab} \). *)
  then have abs_eq: "\<bar>a - b\<bar> = sqrt(1 - 2*a*b)" using abs_diff diff_square by auto

  (* Step 6: Now, we need to show that \( ab + |a - b| \leq 1 \). Substitute the expression for \( |a - b| \): *)
  have "a*b + \<bar>a - b\<bar> = a*b + sqrt(1 - 2*a*b)" by (simp add: abs_eq)

  (* Step 7: Rearranging gives us: \( \sqrt{1 - 2ab} \leq 1 - ab \). *)
  have "a*b + sqrt(1 - 2*a*b) \<le> 1" if "sqrt(1 - 2*a*b) \<le> 1 - a*b" for a b
    using that by simp

  (* Step 8: To show this inequality holds, we square both sides: *)
  (* We need to ensure \( 1 - 2ab \leq (1 - ab)^2 \). *)
  have "1 - 2*a*b \<le> (1 - a*b)^2" 
    by (simp add: power2_eq_square)

  (* Step 9: Expand the right-hand side: \( 1 - 2ab \leq 1 - 2ab + (ab)^2 \). *)
  (* This leads to \( 0 \leq (ab)^2 \). *)
  have "0 \<le> (a*b)^2" by (simp add: square_non_negative) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 10: Since \( (ab)^2 \) is always non-negative, the inequality holds true. *)
  show "a*b + \<bar>a - b\<bar> \<le> 1" using h0
    by (metis add_nonneg_nonneg less_eq_real_def mult_nonneg_nonneg)
qed

end
```
