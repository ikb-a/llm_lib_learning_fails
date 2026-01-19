# square_nonneg

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma square_nonneg:
  fixes x :: real
  shows "x^2 >= 0"
  by (simp add: power2_eq_square)
```


## Usage 1 of 1:
### Problem:
Task name: `algebra_sqineq_at2malt1.json`

Show that for any real number $a$, $a(2-a)\leq 1$.
### Informal Proof:
We have that for any real number $a$, $(a - 1)^2 \geq 0$. So, $a^2 - 2a + 1 \geq 0$. As a result, $a(2-a) = 2a - a^2 \leq 1$.
### Solution:
```isabelle
theorem algebra_sqineq_at2malt1:
  fixes a::real 
  shows "a * (2 - a) \<le> 1"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory algebra_sqineq_at2malt1
  imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem algebra_sqineq_at2malt1:
  fixes a::real 
  shows "a * (2 - a) \<le> 1"
proof -
  (* Step 1: Rewrite the expression \( a(2-a) \) as \( 2a - a^2 \). *)
  have "a * (2 - a) = 2 * a - a^2" by simp

  (* Step 2: Rearranging gives us \( -a^2 + 2a - 1 \leq 0 \). *)
  then have "2 * a - a^2 - 1 \<le> 0" by simp

  (* Step 3: Rewrite as \( -(a^2 - 2a + 1) \leq 0 \). *)
  have "-(a^2 - 2 * a + 1) \<le> 0" by (simp add: algebra_simps)

  (* Step 4: Recognize that \( a^2 - 2a + 1 = (a - 1)^2 \). *)
  have "(a - 1)^2 = a^2 - 2 * a + 1" by (simp add: power2_eq_square)

  (* Step 5: Since \( (a - 1)^2 \) is always non-negative, we have \( -(a - 1)^2 \leq 0 \). *)
  have "(a - 1)^2 \<ge> 0" by (simp add: square_nonneg) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 6: Therefore, we conclude that \( a(2-a) \leq 1 \) holds for all real numbers \( a \). *)
  thus ?thesis using `-(a^2 - 2 * a + 1) \<le> 0` by simp
qed

end
```
