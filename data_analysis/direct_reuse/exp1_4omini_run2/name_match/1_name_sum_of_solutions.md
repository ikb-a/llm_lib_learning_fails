# sum_of_solutions

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_solutions:
  fixes a b :: real
  shows "(-a) + b = b - a"
proof -
  have "(-a) + b = b + (-a)" by (simp add: algebra_simps)
  also have "... = b - a" by auto
  finally show ?thesis .
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_80.json`

Solve  \[\frac{x-9}{x+1}=2\]for $x$. Show that it is -11.
### Informal Proof:
Cross-multiplication gives  \[x-9=2x+2.\]Simplifying this expression tells us  \[x=-11.\]
### Solution:
```isabelle
theorem mathd_algebra_80:
  fixes x :: real
  assumes "x \<noteq> -1"
      and "(x - 9) / (x + 1) = 2"
    shows "x = -11"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_80
  imports Complex_Main
begin

(* lemma for cross-multiplication, useful for manipulating equations *)
lemma cross_multiply:
  fixes x y z :: real
  assumes "z \<noteq> 0"
  shows "(x / z) = y \<longleftrightarrow> (x = y * z)"
proof -
  have "((x / z) = y) \<longleftrightarrow> (x = y * z)" 
    using assms by (auto simp add: field_simps)
  thus ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_80:
  fixes x :: real
  assumes "x \<noteq> -1"
      and "(x - 9) / (x + 1) = 2"
    shows "x = -11"
proof -
  (* Step 1: Start with the equation \(\frac{x-9}{x+1} = 2\). *)
  
  (* Step 2: Cross-multiply to eliminate the fraction. *)
  have "x - 9 = 2 * (x + 1)" using assms(2) 
    using cross_multiply[of "x - 9" "2" "x + 1"] assms(1) by auto
  
  (* Step 3: Distribute the \(2\) on the right side. *)
  have "x - 9 = 2 * x + 2" by (simp add: algebra_simps)
  
  (* Step 4: Rearrange the equation to isolate \(x\) on one side. *)
  (* Subtract \(2x\) from both sides: \(x - 2x - 9 = 2\). *)
  have "-x - 9 = 2" by (simp add: algebra_simps)

  (* Step 5: Add \(9\) to both sides to isolate \(-x\): \(-x = 2 + 9\). *)
  have "-x = 11" by (simp add: sum_of_solutions) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 6: Multiply both sides by \(-1\) to solve for \(x\). *)
  have "x = -11" by (simp add: multiply_by_negative)

  (* Step 7: Conclude that the solution to the equation is \(x = -11\). *)
  thus ?thesis by simp
qed

end
```
