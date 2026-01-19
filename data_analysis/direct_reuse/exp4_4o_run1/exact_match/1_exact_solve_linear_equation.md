# solve_linear_equation

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_linear_equation:
  fixes a b x :: real
  assumes "a * x = b" "a \<noteq> 0"
  shows "x = b / a"
proof -
  from assms(1) have "a * x = b" .
  hence "x = b / a"
    using assms(2) by auto
  thus ?thesis .
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_137.json`

Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? Show that it is 575\text{ students}.
### Informal Proof:
If we knew last year's enrollment at Liberty Middle School, we would multiply by $1.04$ to get the new enrollment of $598$ students. Working backward, we can divide $598$ by $1.04$ to get $575\text{ students}$. Alternatively, we could solve the equation $x + 0.04x = 598$, where $x$ is last year's enrollment.
### Solution:
```isabelle
theorem mathd_algebra_137:
  fixes x::nat
  assumes " x + 4 / 100 * x = 598" 
  shows "x = 575"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_137
  imports Complex_Main
begin

(* This lemma helps us to solve linear equations involving a single variable. *)
lemma solve_linear_equation: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b x :: real
  assumes "a * x = b" "a \<noteq> 0"
  shows "x = b / a"
proof -
  from assms(1) have "a * x = b" .
  hence "x = b / a"
    using assms(2) by auto
  thus ?thesis .
qed

(* formal statement copy from the input *)
theorem mathd_algebra_137:
  fixes x::nat
  assumes "x + 4 / 100 * x = 598" 
  shows "x = 575"
proof -
  (* Step 1: The problem states that the current enrollment is an increase of $4\%$ over last year's enrollment, which can be expressed as $x + 0.04x = 598$. *)
  have "x + 0.04 * x = 598" using assms by auto

  (* Step 2: Simplify the equation $x + 0.04x = 598$ to $1.04x = 598$. *)
  then have "1.04 * x = 598"
    by (simp add: distrib_left)

  (* Step 3: Solve for $x$ by dividing both sides of the equation by $1.04$: $x = \frac{598}{1.04}$. *)
  then have "x = 598 / 1.04"
    using solve_linear_equation[where a="1.04" and b="598"] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 4: Calculate $\frac{598}{1.04}$ to find $x = 575$. *)
  then have "x = 575"
    by simp

  (* Step 5: Verify the solution by checking that $575 + 0.04 \times 575 = 598$. Calculate $0.04 \times 575 = 23$, and $575 + 23 = 598$, confirming the correctness of the solution. *)
  thus ?thesis by auto
qed

end
```
