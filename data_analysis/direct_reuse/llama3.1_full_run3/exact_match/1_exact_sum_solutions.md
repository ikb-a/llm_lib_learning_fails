# sum_solutions, mathd_algebra_196

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_solutions:
  shows "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = 4"
proof -
  have "{x ::real. abs (2 - x) = 3} = {-1, 5}"
    by (auto simp add: abs_if)
  then have "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = -1 + 5"
    by auto
  also have "... = 4" by auto
  finally show ?thesis by auto
qed

theorem mathd_algebra_196:
  "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = 4"
proof -
  show ?thesis using sum_solutions by auto
qed
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
## Problems
Find the sum of all solutions of the equation $|2-x|= 3$. Show that it is 4.

## Formal statement
```isabelle
theory mathd_algebra_196 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

lemma sum_solutions: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  shows "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = 4"
proof -
  have "{x ::real. abs (2 - x) = 3} = {-1, 5}"
    by (auto simp add: abs_if)
  then have "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = -1 + 5"
    by auto
  also have "... = 4" by auto
  finally show ?thesis by auto
qed

theorem mathd_algebra_196: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  "(\<Sum> k \<in> {x ::real. abs (2 - x) = 3}. k) = 4"
proof -
  show ?thesis using sum_solutions by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
qed

end
```

This proof uses a lemma, `sum_solutions`, which is a general statement about the sum of solutions to the equation $|2-x|= 3$. The theorem then uses this lemma to show that the sum of all solutions to the equation is 4. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
