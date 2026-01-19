# abs_cases

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma abs_cases:
  fixes x :: real
  shows "abs (2 - x) = 3 \<longleftrightarrow> (2 - x = 3) \<or> (2 - x = -3)"
  by auto
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_196.json`

Find the sum of all solutions of the equation $|2-x|= 3$. Show that it is 4.
### Informal Proof:
In order to have $|2-x| = 3$, we must have $2-x = 3$ or $2-x = -3$.  If $2-x = 3$, then $x=-1$, and if $2-x = -3$, then $x = 5$.  The sum of these solutions is $(-1) + 5 = 4$.
### Solution:
```isabelle
theorem mathd_algebra_196:
  "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = 4"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_196
  imports Complex_Main
begin

(* Lemma: This lemma expresses the cases for the absolute value equation. *)
lemma abs_cases: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  shows "abs (2 - x) = 3 \<longleftrightarrow> (2 - x = 3) \<or> (2 - x = -3)"
  by auto

(* formal statement copy from the input *)
theorem mathd_algebra_196:
  "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = 4"
proof -
  (* Step 1: Start with the absolute value equation \( |2 - x| = 3 \). *)
  let ?S = "{x :: real. abs (2 - x) = 3}"

  (* Step 2: Rewrite the absolute value equation into two separate cases using the lemma. *)
  have "x \<in> ?S \<longleftrightarrow> (2 - x = 3) \<or> (2 - x = -3)" 
    using abs_cases by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 3: Solve Case 1: \( 2 - x = 3 \). *)
  have case1: "(2 - x = 3) \<longrightarrow> (x = -1)" 
    by (simp add: algebra_simps)

  (* Step 4: Solve Case 2: \( 2 - x = -3 \). *)
  have case2: "(2 - x = -3) \<longrightarrow> (x = 5)" 
    by (simp add: algebra_simps)

  (* Collecting the solutions from both cases: \( x = -1 \) and \( x = 5 \). *)
  have solutions: "?S = {-1, 5}" 
    using case1 case2 by auto

  (* Step 6: Calculate the sum of the solutions: \( (-1) + 5 = 4 \). *)
  have "(\<Sum> k \<in> ?S. k) = (-1) + 5" 
    by (simp add: solutions)

  (* Conclude that the sum of all solutions is \( 4 \). *)
  thus ?thesis 
    by simp
qed

end
```
