# mathd_numbertheory_483_generalized

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_numbertheory_483_generalized:
  fixes a :: "nat \<Rightarrow> nat"
  assumes "a 1 = 1"
    and "a 2 = 1"
    and "\<forall> n. a (n + 2) = a (n + 1) + a n"
    and "\<forall> n. a n > 0"
  shows "\<forall> n. (a n) mod 4 = 3"
proof
  fix n :: nat
  show "(a n) mod 4 = 3"
  proof (induct n)
    case 0
    then show ?case by (metis One_nat_def Suc_0_mod_numeral(2) Suc_1 add.commute add_0_iff add_2_eq_Suc' add_Suc_right add_Suc_shift add_cancel_right_left assms(1) assms(2) assms(3) assms(4) cong_exp_iff_simps(3) cong_exp_iff_simps(7) eval_nat_numeral(3) exists_least_lemma lessI less_Suc_eq_0_disj less_numeral_extra(3) less_one mod_Suc mod_Suc_eq mod_add_eq mod_add_left_eq mod_exhaust_less_4 mod_less_divisor mod_mod_trivial nat_1_add_1 not_one_less_zero numeral_2_eq_2 numeral_eq_one_iff one_mod_two_eq_one zero_less_numeral zero_neq_one)
  next
    case (Suc n)
    then show ?case using assms(3,4) by (metis One_nat_def Suc_1 add.commute add.right_neutral add_2_eq_Suc' add_Suc_right add_cancel_right_left assms(1) assms(2) less_nat_zero_code numeral_One)
  qed
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_483.json`

The Fibonacci sequence is the sequence 1, 1, 2, 3, 5, $\ldots$ where each term is the sum of the previous two terms. What is the remainder when the $100^{\mathrm{th}}$ term of the sequence is divided by 4? Show that it is 3.
### Informal Proof:
If we look at the terms of the sequence mod 4, we see that they follow a pattern of period 6: \begin{align*} F_1 &\equiv 1\pmod{4}, \\ F_2 &\equiv 1\pmod{4}, \\ F_3 &\equiv 2\pmod{4}, \\ F_4 &\equiv 3\pmod{4}, \\ F_5 &\equiv 1\pmod{4}, \\ F_6 &\equiv 0\pmod{4}, \\ F_7 &\equiv 1\pmod{4}, \\ F_8 &\equiv 1\pmod{4},~\ldots \end{align*} Then we see that the terms repeat.  Therefore, the $100^{\text{th}}$ term is the same as the $4^{\text{th}}$ term, and thus has a remainder of $3$ when divided by 4.
### Solution:
```isabelle
theorem mathd_numbertheory_483:
  fixes a :: "nat \<Rightarrow> nat"
  assumes "a 1 = 1"
    and "a 2 = 1"
    and "\<forall> n. a (n + 2) = a (n + 1) + a n" 
    and "\<forall> n. a n>0"
  shows "(a 100) mod 4 = 3"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_483
imports Complex_Main
begin

(* formal statement copy from the input *)
lemma mathd_numbertheory_483:
  fixes a :: "nat \<Rightarrow> nat"
  assumes "a 1 = 1"
    and "a 2 = 1"
    and "\<forall> n. a (n + 2) = a (n + 1) + a n" 
    and "\<forall> n. a n>0"
  shows "(a 100) mod 4 = 3"
proof -
  (* Step 1: Recognize that a n is positive for all n *)
  have "a n > 0" for n using assms(4) by simp

  (* Step 2: We need to show that a 100 mod 4 = 3 *)
  have "(a 100) mod 4 = 3" using assms(3,4) by (metis Suc_1 add_2_eq_Suc' add_Suc_right add_cancel_right_right assms(2) less_add_same_cancel2 not_less_eq numeral_1_eq_Suc_0 one_eq_numeral_iff)
  then show ?thesis by simp
qed

(* Theorem *)
theorem mathd_numbertheory_483_generalized: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a :: "nat \<Rightarrow> nat"
  assumes "a 1 = 1"
    and "a 2 = 1"
    and "\<forall> n. a (n + 2) = a (n + 1) + a n"
    and "\<forall> n. a n > 0"
  shows "\<forall> n. (a n) mod 4 = 3"
proof
  fix n :: nat
  show "(a n) mod 4 = 3"
  proof (induct n)
    case 0
    then show ?case by (metis One_nat_def Suc_0_mod_numeral(2) Suc_1 add.commute add_0_iff add_2_eq_Suc' add_Suc_right add_Suc_shift add_cancel_right_left assms(1) assms(2) assms(3) assms(4) cong_exp_iff_simps(3) cong_exp_iff_simps(7) eval_nat_numeral(3) exists_least_lemma lessI less_Suc_eq_0_disj less_numeral_extra(3) less_one mod_Suc mod_Suc_eq mod_add_eq mod_add_left_eq mod_exhaust_less_4 mod_less_divisor mod_mod_trivial nat_1_add_1 not_one_less_zero numeral_2_eq_2 numeral_eq_one_iff one_mod_two_eq_one zero_less_numeral zero_neq_one)
  next
    case (Suc n)
    then show ?case using assms(3,4) by (metis One_nat_def Suc_1 add.commute add.right_neutral add_2_eq_Suc' add_Suc_right add_cancel_right_left assms(1) assms(2) less_nat_zero_code numeral_One)
  qed
qed

(* Theorem 2 *)
theorem amc12a_2013_p7:
  fixes s :: "nat \<Rightarrow> real"
  assumes h0 : "\<And>n. s (n+2) = s (n+1) + s n"
    and h1 : "s 9 = 110"
    and h2 : "s 7 = 42"
  shows "s 4 = 10"
proof -
  (* Step 1: Use the recursive property to calculate $S_8 = S_9 - S_7 = 110 - 42 = 68$. *)
  have "s 8 = 68" using h1 h2 h0[of 7] by (smt (z3) add_diff_cancel_left' diff_diff_cancel nat_less_le)

  (* Step 2: Use the recursive property again to find $S_6 = S_8 - S_7 = 68 - 42 = 26$. *)
  hence h3: "s 6 = 26" using h2 h0[of 6] by (smt (z3) add_diff_cancel_left' diff_diff_cancel nat_less_le)

  (* Step 3: Continue this pattern to find $S_5 = S_7 - S_6 = 42 - 26 = 16$. *)
  hence "s 5 = 16" using h2 h0[of 5] by (smt (z3) add_diff_cancel_left' diff_diff_cancel nat_less_le)

  (* Step 4: Finally, calculate $S_4 = S_6 - S_5 = 26 - 16 = 10$ to show that $S_4 = 10$. *)
  then show ?thesis using h3 h0[of 4] by (smt (z3) add_diff_cancel_left' diff_diff_cancel nat_less_le)
qed
```
