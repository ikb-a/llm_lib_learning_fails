# am_gm_sqrt

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma am_gm_sqrt:
  fixes x y :: real
  assumes "x \<ge> 0" and "y \<ge> 0"
  shows "(x + y) / 2 \<ge> sqrt (x * y)"
proof -
  have sq_ineq: "(x + y)^2 \<ge> 4 * x * y"
  proof -
    have "(x - y)^2 \<ge> 0" by simp
    then have "x^2 - 2 * x * y + y^2 \<ge> 0" by sos
    hence "x^2 + 2 * x * y + y^2 \<ge> 4 * x * y" by simp
    then show ?thesis by (simp add: power2_sum)
  qed
  note sq_ineq
  moreover have "sqrt ((x + y)^2) = x + y"
  proof -
    from assms have "x + y \<ge> 0" by simp
    then show ?thesis by auto
  qed
  moreover have "sqrt 4 = 2" by simp
  ultimately have "x + y \<ge> 2 * sqrt (x * y)"
    by (metis mult.commute mult.left_commute real_sqrt_le_iff real_sqrt_mult)
  then show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `amc12b_2020_p22.json`

What is the maximum value of $\frac{(2^t-3t)t}{4^t}$ for real values of $t?$  $\textbf{(A)}\ \frac{1}{16} \qquad\textbf{(B)}\ \frac{1}{15} \qquad\textbf{(C)}\ \frac{1}{12} \qquad\textbf{(D)}\ \frac{1}{10} \qquad\textbf{(E)}\ \frac{1}{9}$ Show that it is \textbf{(C)} \frac{1}{12}.
### Informal Proof:
We proceed by using AM-GM. We get $\frac{(2^t-3t) + 3t}{2}$ $\ge \sqrt{(2^t-3t)(3t)}$. Thus, squaring gives us that $4^{t-1} \ge (2^t-3t)(3t)$. Rembering what we want to find, we divide both sides of the inequality by the positive amount of $\frac{1}{3\cdot4^t}$. We get the maximal values as $\frac{1}{12}$, and we are done.
### Solution:
```isabelle
theorem amc12b_2020_p22:
  fixes t :: real
  shows "((2 powr t - 3 * t) * t) / (4 powr t) \<le> 1 / 12"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory amc12b_2020_p22
  imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem amc12b_2020_p22:
  fixes t :: real
  shows "((2 powr t - 3 * t) * t) / (4 powr t) \<le> 1 / 12"
proof -
  (* We consider two cases. In the case where t > 0 and 2 powr t - 3 * t > 0, 
     we can apply the AM-GM inequality to positive numbers. Otherwise, the left‐side
     is nonpositive and the inequality holds trivially as 1/12 > 0. *)
  have pos_case: "t > 0 \<and> 2 powr t - 3 * t > 0 \<or> \<not>(t > 0 \<and> 2 powr t - 3 * t > 0)"
    by auto
  then show ?thesis
  proof
    assume H: "t > 0 \<and> 2 powr t - 3 * t > 0"
    (* Define A = 2^t - 3t and B = 3t. Both are positive because t > 0 and by H *)
    let ?A = "2 powr t - 3 * t"
    let ?B = "3 * t"
    (* By our assumption H we have that ?A > 0 and, since t > 0, also ?B > 0. *)
    have A_pos: "?A > 0" using H by simp
    have B_pos: "?B > 0" using H by simp
    (* Apply the AM-GM inequality for nonnegative numbers.
       We use a standard lemma (am_gm_sqrt) stating that for any x, y ≥ 0,  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
       (x + y)/2 ≥ sqrt(x*y). *)
    have "((?A) + (?B)) / 2 \<ge> sqrt (?A * ?B)"
      using A_pos B_pos by (simp add: am_gm_sqrt[of ?A ?B]) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    (* Note that ?A + ?B = (2 powr t - 3*t) + 3*t = 2 powr t *)
    then have "2 powr t / 2 \<ge> sqrt ((2 powr t - 3 * t) * 3 * t)" by simp
    (* Since both sides are nonnegative, we can square them safely. *)
    then have "(2 powr t / 2)\<^sup>2 \<ge> (sqrt ((2 powr t - 3 * t) * 3 * t))\<^sup>2"
      by (simp add: power2_eq_square)
    (* Simplify the left-hand side: (2 powr t / 2)^2 = ( (2 powr t)^2 )/4 = 4 powr t / 4,
       because (2 powr t)^2 = 4 powr t. *)
    have lhs: "(2 powr t / 2)\<^sup>2 = 4 powr t / 4" 
      by (simp add: powr_exponentiation)
    (* Also, (sqrt ((2 powr t - 3*t) * 3*t))^2 = (2 powr t - 3*t) * 3*t *)
    have rhs: "(sqrt ((2 powr t - 3*t) * 3*t))\<^sup>2 = (2 powr t - 3*t) * 3*t"
      by simp
    (* Combining the above, we have: 4 powr t/4 ≥ (2 powr t - 3*t)*3*t *)
    hence "4 powr t / 4 \<ge> (2 powr t - 3*t) * 3*t" using lhs rhs by simp
    (* Divide both sides by 3 (which is positive) to obtain: 
       (2 powr t - 3*t)*t ≤ 4 powr t/12 *)
    then have "(2 powr t - 3*t)*t \<le> 4 powr t / 12"
      by (simp add: field_split_simps)
    (* Finally, dividing both sides by 4 powr t (which is positive for all t) yields the claim. *)
    then show ?thesis by (simp add: field_split_simps)
  next
    assume H: "\<not>(t > 0 \<and> 2 powr t - 3*t > 0)"
    (* In this case, either t ≤ 0 or 2 powr t - 3*t ≤ 0. *)
    have "((2 powr t - 3*t) * t) / (4 powr t) \<le> 0"
    proof -
      (* 4 powr t is always positive. *)
      have pos_denom: "4 powr t > 0" by simp
      (* If t ≤ 0 then (2 powr t - 3*t)*t ≤ 0 since t is nonpositive, 
         or if t > 0 but 2 powr t - 3*t ≤ 0 then their product is nonpositive. *)
      have "(2 powr t - 3*t) * t \<le> 0"
      proof (cases "t > 0")
        case True
        then have "2 powr t - 3*t \<le> 0" using H by auto
        then show ?thesis by simp
      next
        case False
        then show ?thesis by simp
      qed
      with pos_denom show ?thesis by (simp add: divide_nonneg_pos)
    qed
    (* Since 0 ≤ 1/12, the inequality holds in this case. *)
    then show ?thesis by simp
  qed
qed

end
```
