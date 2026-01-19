# divide_by_nonzero

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma divide_by_nonzero:
  fixes a b :: real
  assumes "b > 0"
  shows "a / b = a * (1 / b)"
  by (simp add: assms)
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

(* formal statement copied from the input *)
theorem mathd_algebra_137:
  fixes x::nat
  assumes "x + 4 / 100 * x = 598" 
  shows "x = 575"
proof -
  (* Step 1: We can rewrite the equation from the assumption. *)
  have "1.04 * x = 598" using assms by simp
  
  (* Step 2: Isolate x by dividing both sides by 1.04. *)
  have "x = 598 / 1.04" using `1.04 * x = 598` by (simp add: field_simps)
  
  (* Step 3: Calculate the value of x. *)
  also have "... = 575" by (simp add: divide_by_nonzero[of 598 1.04]) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
  (* Step 4: Conclude the proof. *)
  finally show ?thesis by simp
qed

lemma divide_by_nonzero: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: real
  assumes "b > 0"
  shows "a / b = a * (1 / b)"
  by (simp add: assms)

end
```
