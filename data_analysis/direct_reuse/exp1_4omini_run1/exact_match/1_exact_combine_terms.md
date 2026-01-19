# combine_terms

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma combine_terms:
  fixes a b c d :: real
  shows "a * (b - c) + d = (a * b) - (a * c) + d"
  by (simp add: algebra_simps)
```


## Usage 1 of 1:
### Problem:
Task name: `amc12b_2002_p2.json`

What is the value of  $(3x - 2)(4x + 1) - (3x - 2)4x + 1$ when $x=4$?  $\mathrm{(A)}\ 0 \qquad\mathrm{(B)}\ 1 \qquad\mathrm{(C)}\ 10 \qquad\mathrm{(D)}\ 11 \qquad\mathrm{(E)}\ 12$ Show that it is \mathrm{(D)}\ 11.
### Informal Proof:
By the distributive property,   $(3x-2)[(4x+1)-4x] + 1 = 3x-2 + 1 = 3x-1 = 3(4) - 1 = \mathrm{(D)}\ 11$.
### Solution:
```isabelle
theorem amc12b_2002_p2:
  fixes x ::int
  assumes h0: "x = 4" 
  shows "(3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory amc12b_2002_p2
  imports Complex_Main
begin

(* lemma 1. This lemma simplifies the expression by combining like terms. *)
lemma combine_terms: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c d :: real
  shows "a * (b - c) + d = (a * b) - (a * c) + d"
  by (simp add: algebra_simps)

(* formal statement copy from the input *)
theorem amc12b_2002_p2:
  fixes x :: int
  assumes h0: "x = 4" 
  shows "(3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11"
proof -
  (* Step 1: Start with the expression \((3x - 2)(4x + 1) - (3x - 2)(4x) + 1\). *)
  let ?expr = "(3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1"

  (* Step 2: Factor out the common term \((3x - 2)\) from the first two terms. *)
  have " ?expr = (3 * x - 2) * ((4 * x + 1) - (4 * x)) + 1" 
    by (simp add: distribute)

  (* Step 3: Simplify the expression inside the parentheses. *)
  have "... = (3 * x - 2) * 1 + 1"
    by (simp add: algebra_simps)

  (* Thus, the expression simplifies to: *)
  have "... = (3 * x - 2) + 1"
    by simp

  (* Step 4: Combine like terms. *)
  have "... = 3 * x - 1"
    by (simp add: algebra_simps)

  (* Step 5: Substitute \(x = 4\) into the simplified expression. *)
  have "3 * x - 1 = 3 * 4 - 1"
    using h0 by simp

  (* Step 6: Calculate the final result. *)
  have "... = 12 - 1"
    by simp
  then show ?thesis
    by simp
qed

end
```
