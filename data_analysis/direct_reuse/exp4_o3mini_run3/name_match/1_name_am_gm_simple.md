# am_gm_simple

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma am_gm_simple:
  fixes a b :: real
  assumes "a \<ge> 0" and "b \<ge> 0"
  shows "(a + b) / 2 \<ge> sqrt (a * b)"
proof -
  have "(a - b)^2 \<ge> 0" by simp
  then have "a^2 - 2 * a * b + b^2 \<ge> 0" by sos
  hence "a^2 + 2 * a * b + b^2 \<ge> 4 * a * b" by simp
  then have "(a + b)^2 \<ge> 4 * a * b" by sos
  then have "sqrt ((a + b)^2) \<ge> sqrt (4 * a * b)"
    using assms by (metis mult.commute mult.left_commute power2_eq_square real_sqrt_le_iff)
  hence "a + b \<ge> 2 * sqrt (a * b)"
    using assms by (metis add_increasing2 mult.commute mult.left_commute real_sqrt_four real_sqrt_mult real_sqrt_pow2_iff real_sqrt_power)
  thus ?thesis by simp
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
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

(* formal statement copy from the input*)
theorem amc12b_2020_p22:
  fixes t :: real
  shows "((2 powr t - 3 * t) * t) / (4 powr t) \<le> 1 / 12"
proof (cases "t > 0")
  (* Case 1: t is not positive *)
  case False
  (* If t ≤ 0 then t is nonpositive.
     In this case, note that ((2 powr t - 3 * t)*t) is also ≤ 0,
     while (4 powr t) is always > 0.
     Thus the whole fraction is ≤ 0 which is certainly ≤ 1/12. *)
  then have "t \<le> 0" by simp
  moreover have "4 powr t > 0" 
    using powr_gt_zero[of 4 t] by simp
  ultimately have "((2 powr t - 3 * t) * t) / (4 powr t) \<le> 0" 
    by (simp add: divide_nonpos_pos)
  then show ?thesis by simp
next
  (* Case 2: t > 0 *)
  case True
  then have t_pos: "t > 0" by simp
  (* We split into two subcases according to the sign of (2 powr t - 3*t). *)
  {
    (* Subcase 2a: 2 powr t - 3 * t < 0 *)
    assume A: "2 powr t - 3 * t < 0"
    then have "((2 powr t - 3 * t) * t) < 0" using t_pos by simp
    moreover have "4 powr t > 0" 
      using powr_gt_zero[of 4 t] by simp
    ultimately have "((2 powr t - 3 * t) * t) / (4 powr t) < 0" 
      by simp
    then have "((2 powr t - 3 * t) * t) / (4 powr t) \<le> 1/12" by simp
  }
  {
    (* Subcase 2b: 2 powr t - 3 * t \<ge> 0 *)
    assume B: "2 powr t - 3 * t \<ge> 0"
    (* In this subcase both numbers
       A = 2 powr t - 3*t and B = 3*t are nonnegative.
       We apply the arithmetic mean–geometric mean inequality.
       Note that (A + B) = (2 powr t - 3*t + 3*t) = 2 powr t. *)
    have am: "((2 powr t - 3*t) + 3*t) / 2 = 2 powr t / 2" by simp
    (* We invoke the AM–GM inequality (useful skill 1) on the nonnegative numbers
       A = 2 powr t - 3*t and B = 3*t.
       Since t > 0 and by assumption B we have 2 powr t - 3*t \<ge> 0 and 3*t > 0. *)
    have gm: "2 powr t / 2 \<ge> sqrt ((2 powr t - 3*t) * (3*t))"
      using B t_pos
      by (rule am_gm_simple) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    (* Square both sides; note that both sides are nonnegative. *)
    then have "(2 powr t)^2 / 4 \<ge> (2 powr t - 3*t) * (3*t)"
      by (simp add: power2_ge_iff)
    (* Observe that (2 powr t)^2 = 4 powr t; this is because 4 = (2)^2. *)
    then have "4 powr t / 4 \<ge> (2 powr t - 3*t) * (3*t)" 
      by (simp add: powr_mult)
    then have "4 powr t \<ge> 12 * t * (2 powr t - 3*t)" by simp
    (* Dividing both sides by the positive number 12 * (4 powr t), we deduce *)
    then have "((2 powr t - 3*t) * t) \<le> (4 powr t) / 12" 
      by simp
    then have "((2 powr t - 3*t) * t) / (4 powr t) \<le> 1/12" 
      using powr_gt_zero[of 4 t] by simp
  }
  thus ?thesis by blast
qed

end
```
