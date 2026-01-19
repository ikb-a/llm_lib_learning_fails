# abs_cases

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma abs_cases:
  fixes x y :: real
  shows "\<bar>x-y\<bar> = (if x \<ge> y then x-y else y-x)"
proof -
  have "\<bar>x - y\<bar> = (if x - y \<ge> 0 then x - y else -(x - y))"
    by (simp add: abs_if)
  also have "... = (if x - y \<ge> 0 then x - y else y - x)"
    by simp
  also have "... = (if x \<ge> y then x - y else y - x)"
    by auto
  finally show ?thesis .
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
```isabelle
theory algebra_sqineq_unitcircatbpabsamblt1
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

(* no helper lemmas required *)

(* formal statement copy from the input *)
theorem algebra_sqineq_unitcircatbpabsamblt1:
  fixes a b :: real
  assumes h0: "a^2 + b^2 = 1" 
  shows "a * b + \<bar>a - b\<bar> \<le> 1"
proof -
  (* Step 1: Start with the given condition \( a^2 + b^2 = 1 \). *)
  have eq1: "a^2 + b^2 = 1" 
    using h0 by simp
  
  (* Step 2: Consider the expression \( (a - b + 1)^2 \). Expanding this. *)
  have "(a - b + 1)^2 = a^2 - 2*a*b + b^2 + 2*a - 2*b + 1"
    by (simp add: power2_eq_square algebra_simps)
  (* Substitute \( a^2 + b^2 = 1 \) into the expression. *)
  hence "(a - b + 1)^2 = 1 - 2*a*b + 2*a - 2*b + 1"
    using eq1 by simp
  (* Since squares are non-negative, \( (a - b + 1)^2 \geq 0 \). *)
  hence "0 \<le> (a - b + 1)^2"
    by simp
  (* This implies: \( 2 - 2*a*b + 2*a - 2*b \<ge> 0 \). *)
  hence "2 - 2*a*b + 2*a - 2*b \<ge> 0"
    by simp
  (* Which simplifies to: \( 1 - a*b + a - b \<ge> 0 \). *)
  hence ineq1: "1 - a*b + a - b \<ge> 0"
    by simp
    
  (* Step 3: Similarly, consider the expression \( (b - a + 1)^2 \). *)
  have "(b - a + 1)^2 = b^2 - 2*b*a + a^2 + 2*b - 2*a + 1"
    by (simp add: power2_eq_square algebra_simps)
  (* Substitute \( a^2 + b^2 = 1 \) into the expression. *)
  hence "(b - a + 1)^2 = 1 - 2*a*b + 2*b - 2*a + 1"
    using eq1 by simp
  (* Since squares are non-negative, \( (b - a + 1)^2 \geq 0 \). *)
  hence "0 \<le> (b - a + 1)^2"
    by simp
  (* This implies: \( 2 - 2*a*b + 2*b - 2*a \<ge> 0 \). *)
  hence "2 - 2*a*b + 2*b - 2*a \<ge> 0"
    by simp
  (* Which simplifies to: \( 1 - a*b + b - a \<ge> 0 \). *)
  hence ineq2: "1 - a*b + b - a \<ge> 0"
    by simp

  (* Step 4: Combine the inequalities obtained from steps 2 and 3. *)
  (* Use abs_cases lemma to handle the absolute value and derive the final inequality. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "a * b + \<bar>a - b\<bar> = (if a \<ge> b then a*b + (a - b) else a*b + (b - a))"
    by (simp add: abs_cases) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  hence "a * b + \<bar>a - b\<bar> \<le> 1"
  proof (cases "a \<ge> b")
    case True
    (* Case 1: \( a \ge b \), use ineq1. *)
    then show ?thesis
      using ineq1 by simp
  next
    case False
    (* Case 2: \( a < b \), use ineq2. *)
    then show ?thesis
      using ineq2 by simp
  qed
  (* Step 5: Conclude that the inequality \( ab + |a - b| \leq 1 \) holds. *)
  thus ?thesis .
qed

end
```
