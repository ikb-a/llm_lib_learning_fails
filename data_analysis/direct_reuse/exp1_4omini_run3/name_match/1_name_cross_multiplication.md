# cross_multiplication

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem cross_multiplication:
  fixes a b c d :: real
  assumes "c \<noteq> 0" and "d \<noteq> 0"
  shows "a / b = c / d \<Longrightarrow> a * d = b * c"
proof -
  assume "a / b = c / d"
  then have "a * d = c * (b / d * d)" by (smt (verit) assms(1) assms(2) divide_eq_0_iff divide_eq_eq frac_eq_eq)
  then show "a * d = b * c" using assms by (metis field_simps)
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

(* Step 1: Start with the equation \(\frac{x-9}{x+1} = 2\). *)
(* We already have this equation in the assumptions. *)

(* Step 2: Perform cross-multiplication to eliminate the fraction, yielding \(x - 9 = 2(x + 1)\). *)
lemma cross_multiplication: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x \<noteq> -1" 
      and "(x - 9) / (x + 1) = 2"
  shows "x - 9 = 2 * (x + 1)"
proof -
  have "((x - 9) / (x + 1) = 2) \<longleftrightarrow> (x - 9) = 2 * (x + 1)"
    using assms by (simp add: field_simps)
  then show ?thesis by (metis ab_semigroup_add_class.add_ac(1) add.commute assms(2) group_cancel.add2 mult_2 uminus_add_conv_diff)
qed

(* Step 3: Expand the right-hand side: \(x - 9 = 2x + 2\). *)
lemma expand_right_hand_side:
  fixes x :: real
  assumes "x - 9 = 2 * (x + 1)"
  shows "x - 9 = 2 * x + 2"
proof -
  have "2 * (x + 1) = 2 * x + 2" by simp
  then show ?thesis using assms by simp
qed

(* Step 4: Rearrange the equation to isolate \(x\): \(x - 2x = 2 + 9\). *)
lemma rearrange_equation:
  fixes x :: real
  assumes "x - 9 = 2 * x + 2"
  shows "x - 2 * x = 2 + 9"
proof -
  have "x - 2 * x = -x" by simp
  have "x - 9 = 2 * x + 2" using assms by simp
  then have "x - 2 * x = 2 + 9" by (smt (verit) \<open>x - 9 = 2 * x + 2\<close>)
  show ?thesis by (simp add: field_simps)
qed

(* Step 5: Simplify the left-hand side: \(-x = 11\). *)
lemma simplify_left_hand_side:
  fixes x :: real
  assumes "x - 2 * x = 2 + 9"
  shows "-x = 11"
proof -
  have "-x = 11" by (smt (verit) assms)
  show ?thesis using `-x = 11` by simp
qed

(* Step 6: Multiply both sides by -1 to solve for \(x\): \(x = -11\). *)
theorem mathd_algebra_80:
  fixes x :: real
  assumes "x \<noteq> -1"
      and "(x - 9) / (x + 1) = 2"
  shows "x = -11"
proof -
  (* Apply the lemmas to solve for x *)
  have step1: "x - 9 = 2 * (x + 1)" using cross_multiplication[of x] assms by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have step2: "x - 9 = 2 * x + 2" using expand_right_hand_side[of x] step1 by simp
  have step3: "x - 2 * x = 11" using rearrange_equation[of x] step2 by simp
  have step4: "-x = 11" using simplify_left_hand_side[of x] step3 by simp
  then show ?thesis by (simp add: field_simps)
qed

end
```
