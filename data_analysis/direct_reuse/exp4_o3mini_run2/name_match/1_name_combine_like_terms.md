# combine_like_terms

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma combine_like_terms:
  fixes x :: real
  shows "x + (4/100 * x) = (104/100) * x"
proof -
  have "x + (4/100 * x) = (100/100 * x) + (4/100 * x)" by (simp add: field_simps)
  also have "... = ((100/100) + (4/100)) * x" by (simp add: algebra_simps)
  also have "... = (104/100) * x" by simp
  finally show ?thesis .
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
  imports Main
begin

(* A lemma combining like terms useful when dealing with percentage increases. *)
lemma combine_like_terms: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  shows "x + (4/100 * x) = (104/100) * x"
proof -
  (* Express x as 1 * x *)
  have "x + (4/100 * x) = 1 * x + (4/100 * x)" by simp
  (* Factor x out from the sum *)
  also have "... = (1 + 4/100) * x" by (simp add: algebra_simps)
  (* Express 1 as 100/100 to combine with 4/100 *)
  also have "... = (100/100 + 4/100) * x" by simp
  (* Sum the fractions *)
  also have "... = (104/100) * x" by simp
  finally show ?thesis .
qed

theorem mathd_algebra_137:
  fixes x::nat
  assumes " x + 4 / 100 * x = 598" 
  shows "x = 575"
proof -
  (* Since x is of type nat, it is automatically coerced to a real number in numeric expressions.
     Apply the combine_like_terms lemma to express the LHS in a simplified form. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have eq: "real x + (4/100) * real x = (104/100) * real x" 
    using combine_like_terms[of "real x"] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* By the assumption and coercion, we have that: *)
  have A: "(104/100) * real x = 598"
    using assms eq by simp
  (* Multiply both sides of the equation A by 100 (which is allowed because 100 ≠ 0) to eliminate the denominator: *)
  have "104 * real x = 598 * 100"
    using A by (simp add: field_simps)
  (* Simplify the right-hand side: *)
  have "104 * real x = 59800" by simp
  (* Notice that 104 * 575 = 59800, hence we deduce that real x = 575.
     Since x is a natural number and 575 is natural, we obtain x = 575. *)
  have "real x = 575" using \<open>104 * real x = 59800\<close> by simp
  then have "x = 575" by simp
  thus "x = 575" .
qed

end
```
