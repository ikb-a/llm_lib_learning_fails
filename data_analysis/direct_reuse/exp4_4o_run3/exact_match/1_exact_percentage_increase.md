# percentage_increase

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma percentage_increase:
  fixes x p :: real
  assumes "p > 0"
  shows "x + p / 100 * x = x * (1 + p / 100)"
proof -
  have "x + p / 100 * x = x * (1 + p / 100)"
    by (auto simp: field_simps)
  thus ?thesis by simp
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

(* lemma for percentage increase *)
lemma percentage_increase: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x p :: real
  assumes "p > 0"
  shows "x + p / 100 * x = x * (1 + p / 100)"
proof -
  have "x + p / 100 * x = x * (1 + p / 100)"
    by (auto simp: field_simps)
  thus ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_137:
  fixes x::nat
  assumes " x + 4 / 100 * x = 598" 
  shows "x = 575"
proof -
  (* Step 2: Set up the equation based on the problem statement. Use the percentage_increase lemma to simplify the expression. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "x + 4 / 100 * x = x * (1 + 4 / 100)"
    using percentage_increase[of x 4] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "x * 1.04 = 598"
    using assms by simp

  (* Step 4: Solve for \( x \). Divide both sides of the equation by 1.04 to isolate \( x \). *)
  then have "x = 598 / 1.04"
    by simp

  (* Step 5: Calculate the value of \( x \). Perform the division to find \( x = 575 \). *)
  then have "x = 575"
    by simp

  (* Step 6: Verify the solution. Multiply 575 by 1.04 to ensure it equals 598. *)
  thus ?thesis
    by simp
qed

end
```
