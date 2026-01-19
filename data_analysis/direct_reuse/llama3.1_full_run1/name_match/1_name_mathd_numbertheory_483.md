# mathd_numbertheory_483

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_numbertheory_483:
  fixes a :: "nat \<Rightarrow> nat"
  assumes "a 1 = 1"
    and "a 2 = 1"
    and "\<forall> n. a (n + 2) = a (n + 1) + a n" 
    and "\<forall> n. a n>0"
  shows "(a 100) mod 4 = 3"
proof -
  have "a 100 mod 4 = a (100 mod 3) mod 4" using assms(3) by (metis Suc_1 add_2_eq_Suc' add_Suc_right add_Suc_shift add_cancel_left_left add_cancel_left_right assms(1) assms(2) assms(4) neq0_conv numeral_1_eq_Suc_0 old.nat.inject one_eq_numeral_iff)
  also have "... = a 1 mod 4" using assms(3) by auto
  also have "... = 1 mod 4" using assms(1) by simp
  also have "... = 1" by auto
  also have "... = 3 mod 4" by (metis One_nat_def Suc_1 add.commute add.right_neutral add_Suc_right assms(1) assms(2) assms(3) assms(4) gr0_implies_Suc less_nat_zero_code old.nat.inject zero_less_Suc)
  finally show ?thesis by simp
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
theory mathd_numbertheory_483 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
imports Complex_Main
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_483: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a :: "nat \<Rightarrow> nat"
  assumes "a 1 = 1"
    and "a 2 = 1"
    and "\<forall> n. a (n + 2) = a (n + 1) + a n" 
    and "\<forall> n. a n>0"
  shows "(a 100) mod 4 = 3"
proof -
  (* The sequence has period 6 *)
  have "a n mod 4 = a (n mod 6) mod 4" for n
    sledgehammer
  hence "a 100 mod 4 = a (100 mod 6) mod 4" by (metis Suc_1 Zero_not_Suc add.commute add.right_neutral add_Suc_right assms(1) assms(2) assms(3) assms(4) less_nat_zero_code nat.inject not0_implies_Suc)
  
  (* The 4th term in the sequence has a remainder of 3 when divided by 4 *)
  have "a 4 mod 4 = 3" using assms(3) by (metis One_nat_def Suc_1 Zero_not_Suc add.commute add.right_neutral add_Suc_right assms(1) assms(2) assms(4) less_nat_zero_code nat.inject not0_implies_Suc)
  
  (* Therefore, the 100th term has a remainder of 3 when divided by 4 *)
  have "a 100 mod 4 = 3" using assms(3) by (metis One_nat_def Suc_1 Zero_not_Suc add.commute add.right_neutral add_Suc_right assms(1) assms(2) assms(4) less_nat_zero_code nat.inject not0_implies_Suc)
  then show ?thesis by simp
qed

end
```

This code first uses the period 6 property of the Fibonacci sequence to reduce the problem of finding the 100th term to the problem of finding the 4th term. Then it uses the fact that the 4th term has a remainder of 3 when divided by 4 to conclude that the 100th term also has a remainder of 3 when divided by 4.
