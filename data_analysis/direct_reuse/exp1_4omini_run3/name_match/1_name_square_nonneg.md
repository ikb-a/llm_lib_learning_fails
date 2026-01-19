# square_nonneg

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma square_nonneg:
  fixes x :: real
  shows "x^2 >= 0"
  by auto
```


## Usage 1 of 1:
### Problem:
Task name: `algebra_sqineq_unitcircatbpamblt1.json`

Let $a$ and $b$ be two real numbers such that $a^2+b^2=1$. Show that $ab+(a-b)\leq 1$.
### Informal Proof:
We have that $(a - b - 1)^2 \geq 0$. By expanding, we have: $0 \leq a^2 - ab - a - ab + b^2 + b - a + b + 1$. Since $a^2+b^2=1$, we get $0 \leq 2 - 2ab - 2a + 2b$. As a result, $ab+(a-b) \leq 1$.
### Solution:
```isabelle
theorem algebra_sqineq_unitcircatbpamblt1:
  fixes a b:: real
  assumes h0: "a^2 + b^2 = 1"
  shows "a * b + (a - b) \<le> 1"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory algebra_sqineq_unitcircatbpamblt1
  imports Complex_Main
begin

(* lemma 1: a lemma stating that the square of any real number is non-negative *)
lemma square_nonneg: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  shows "x^2 >= 0"
  by auto

(* formal statement copy from the input *)
theorem algebra_sqineq_unitcircatbpamblt1:
  fixes a b:: real
  assumes h0: "a^2 + b^2 = 1"
  shows "a * b + (a - b) \<le> 1"
proof -
  (* Step 1: Start with the assumption that \( a^2 + b^2 = 1 \). *)
  have ab_leq: "a^2 + b^2 = 1" by (rule h0)

  (* Step 2: Rewrite the expression we want to prove: \( ab + (a - b) \leq 1 \). *)
  (* Step 3: Rearrange the inequality: \( ab + a - b \leq 1 \) can be rewritten as \( ab + a - b - 1 \leq 0 \). *)
  have c0: "a * b + (a - b) - 1 = a * b + a - b - 1" by simp

  (* Step 4: Consider the expression \( (a - b - 1)^2 \geq 0 \). This is always true since the square of any real number is non-negative. *)
  have c1: "(a - b - 1)^2 >= 0" by (rule square_nonneg) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 5: Expand the squared term: *)
  have expansion: "(a - b - 1)^2 = (a - b)^2 - 2*(a - b) + 1"
    by (simp add: expand_square)

  (* Step 6: Substitute \( a^2 + b^2 = 1 \) into the expanded expression. *)
  have expanded_expr: "(a - b)^2 - 2*a + 2*b + 1 = a^2 - 2*a*b + b^2 - 2*a + 2*b + 1"
    by (simp add: power2_diff)

  (* Substituting \( a^2 + b^2 = 1 \) into the inequality gives us: *)
  have inequality: "0 <= (1 - 2*a*b - 2*a + 2*b) + 1"
    using ab_leq by (simp add: expanded_expr)

  (* Step 7: Simplify the inequality: *)
  have simplified: "0 <= 2 - 2*a*b - 2*a + 2*b"
    by (simp add: inequality)

  (* Step 8: Divide the entire inequality by 2: *)
  have final_step: "0 <= 1 - a*b - a + b"
    by (simp add: simplified divide_simps)

  (* Step 9: Rearranging gives us: *)
  have rearranged: "a*b + (a - b) <= 1"
    by (simp add: final_step)

  (* Step 10: Conclude that the inequality holds for any real numbers \( a \) and \( b \) such that \( a^2 + b^2 = 1 \). *)
  thus ?thesis using rearranged by simp
qed

end
```
