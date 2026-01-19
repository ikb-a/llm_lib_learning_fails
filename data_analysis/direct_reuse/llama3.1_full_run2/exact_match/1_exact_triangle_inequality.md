# triangle_inequality

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma triangle_inequality:
  fixes a b :: real
  shows "\<bar>a - b\<bar> = \<bar>- (b - a)\<bar>"
proof -
  have "- (b - a) = -(b - a)"
    by simp
  then have "\<bar>- (b - a)\<bar> = \<bar>b - a\<bar>"
    by (simp add: abs_minus_cancel)
  then show ?thesis by simp
qed
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
## Problems
Let $a$ and $b$ be real numbers such that $a^2+b^2=1$. Show that $ab+\lvert a-b\rvert \leq 1$.

## Formal statement
```isabelle
theory algebra_sqineq_unitcircatbpabsamblt1
  imports Complex_Main
begin

(* useful lemmas *)
lemma algebraic_manipulation:
  fixes a b :: real
  shows "(a - b - 1)^2 = a^2 - 2 * a * b + b^2 - 2 * a + 2 * b + 1"
  by (sos)

lemma algebraic_manipulation_2:
  fixes a b :: real
  assumes "a^2 + b^2 = 1"
  shows "2 - 2 * a * b - 2 * a + 2 * b >= 0"
proof -
  have "(a - b - 1)^2 = a^2 - 2 * a * b + b^2 - 2 * a + 2 * b + 1"
    using algebraic_manipulation assms
    by auto
  then have "(a - b - 1)^2 = 1 + (1 - 2 * a * b - 2 * a + 2 * b)"
    using assms by simp
  then have "(a - b - 1)^2 = 2 - 2 * a * b - 2 * a + 2 * b"
    by simp
  then have "0 <= (a - b - 1)^2"
    by sos
  then have "0 <= 2 - 2 * a * b - 2 * a + 2 * b"
    by (metis \<open>(a - b - 1)\<^sup>2 = 2 - 2 * a * b - 2 * a + 2 * b\<close> power2_commute power_eq_if zero_le_power2)
  then show ?thesis
    by simp
qed

lemma triangle_inequality: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: real
  shows "\<bar>a - b\<bar> = \<bar>- (b - a)\<bar>"
proof -
  have "- (b - a) = -(b - a)"
    by simp
  then have "\<bar>- (b - a)\<bar> = \<bar>b - a\<bar>"
    by (simp add: abs_minus_cancel)
  then show ?thesis by simp
qed

(* formal statement copy from the input*)
theorem algebra_sqineq_unitcircatbpabsamblt1:
  fixes a b :: real
  assumes h0: "a^2 + b^2 = 1" 
  shows "a * b + \<bar>a - b\<bar> \<le> 1"
proof -
  (* Step 1: Expand the expression $(a-b+1)^2$ and simplify it to obtain $2-2ab+2a-2b$.*)
  have c0: "2 - 2 * a * b - 2 * a + 2 * b >= 0"
    using algebraic_manipulation_2 assms
    by simp

  (* Step 2: Repeat the process for the expression $(b-a+1)^2$ to obtain $1-ba+b-a \ge 0$. *)
  have c1: "2 - 2 * b * a + 2 * a - 2 * b >= 0"
    using algebraic_manipulation_2 assms
    by (simp add: algebraic_manipulation_2)

  (* Step 3: Combine the inequalities from Steps 1 and 2 to obtain $ab+\lvert a-b\rvert \le 1$. *)
  have "a * b + \<bar>a - b\<bar> <= 1"
    by (smt c0 c1 mult_1_right triangle_inequality) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then show ?thesis
    by simp
qed

end
```
