# multi_distrib_complex

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma multi_distrib_complex:
  fixes a b c d :: complex
  shows "(a + b) * (c + d) = a * c + a * d + b * c + b * d"
  by (simp add: distrib_left distrib_right)
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_432.json`

Expand $(x+3)(2x-6)$. Show that it is 2x^2-18.
### Informal Proof:
Factoring a $2$ out of the second term gives $2(x+3)(x-3)=2(x^2-3^2)=2x^2-18$.
### Solution:
```isabelle
theorem mathd_algebra_432:
  fixes x ::real 
  shows "(x + 3) * (2 * x - 6) = 2 * x^2 - 18"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_432
  imports Complex_Main
begin

(* The lemma multi_distrib_complex can be applied here since it helps in expanding expressions of the form (a + b) * (c + d) *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
(* We use the lemma to expand the expression: (x + 3) * (2 * x - 6) *)

theorem mathd_algebra_432:
  fixes x ::real 
  shows "(x + 3) * (2 * x - 6) = 2 * x^2 - 18"
proof -
  (* Step 1: Expand the expression using the distributive property *)
  have "(x + 3) * (2 * x - 6) = x * 2 * x + x * (-6) + 3 * 2 * x + 3 * (-6)"
    by (simp add: multi_distrib_complex) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 2: Simplify each term *)
  then have "... = 2 * x^2 + (-6) * x + 6 * x + (-18)"
    by simp

  (* Step 3: Combine like terms *)
  then have "... = 2 * x^2 + (6 - 6) * x + (-18)"
    by simp

  (* Step 4: Conclude the proof by showing the simplified expression *)
  then show ?thesis
    by simp
qed

end
```
