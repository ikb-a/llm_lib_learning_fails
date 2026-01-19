# mathd_algebra_419

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_419:
  fixes a b :: real
  assumes "a = -1"
    and "b = 5"
  shows "-a - b^2 + 3 * (a * b) = -39"
proof -
  have "b^2 = 25" using assms(2) by simp
  have "a * b = -5" using assms by simp
  then have "3 * (a * b) = -15" by simp
  then show ?thesis 
    using assms(1) by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_419.json`

What is the value of $-a-b^2+3ab$ if $a=-1$ and $b=5$? Show that it is -39.
### Informal Proof:
Plugging in the given values yields $-a-b^2+3ab=-(-1)-5^2+3(-1)(5)=1-25-15=-39$.
### Solution:
```isabelle
theorem mathd_algebra_419:
  fixes a b :: real
  assumes "a = -1"
    and "b = 5"
  shows "-a - b^2 + 3 * (a * b) = -39"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_419 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main 
begin

(* formal statement copy from the input *)
theorem mathd_algebra_419: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: real
  assumes "a = -1"
    and "b = 5"
  shows "-a - b^2 + 3 * (a * b) = -39"
proof -
  (* Step 1: Calculate b^2 *)
  have b_squared: "b^2 = 25" using assms(2) by simp

  (* Step 2: Calculate a * b *)
  have a_times_b: "a * b = -5" using assms by simp

  (* Step 3: Calculate 3 * (a * b) *)
  have three_a_times_b: "3 * (a * b) = -15" using a_times_b by simp

  (* Step 4: Calculate -a *)
  have neg_a: "-a = 1" using assms(1) by simp

  (* Step 5: Combine all results to show the final equation *)
  show ?thesis 
    using neg_a b_squared three_a_times_b 
    by (simp add: algebra_simps)
qed

end
```
