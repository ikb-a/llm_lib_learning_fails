# mathd_algebra_80

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_80:
  fixes x :: real
  assumes "x \<noteq> -1"
      and "(x - 9) / (x + 1) = 2"
    shows "x = -11"
proof -
  have "x - 9 = 2 * (x + 1)" using assms by (auto simp: field_simps)
  then have "x - 9 = 2 * x + 2" by (simp add: algebra_simps)
  then have "x - 2 * x = 9 + 2" by (simp add: algebra_simps)
  then have "-x = 11" by (simp add: algebra_simps)
  then have "x = -11" by simp
  then show ?thesis by simp
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
Here's the formal proof for the problem:

```isabelle
theory mathd_algebra_80 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_algebra_80: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x \<noteq> -1"
      and "(x - 9) / (x + 1) = 2"
    shows "x = -11"
proof -
  (* Cross-multiplication gives  x-9=2x+2. *)
  have cross_multiplication: "(x - 9) = 2 * (x + 1)" using assms by (auto simp: field_simps)
  then have "x - 9 = 2 * x + 2" by (simp add: algebra_simps)
  then have "x - 2 * x = 9 + 2" by (simp add: algebra_simps)
  then have "-x = 11" by (simp add: algebra_simps)
  then have "x = -11" by simp
  then show ?thesis by simp
qed

end
```

This proof uses the cross-multiplication property of fractions and the algebraic properties of real numbers to simplify the equation and arrive at the solution x = -11.
