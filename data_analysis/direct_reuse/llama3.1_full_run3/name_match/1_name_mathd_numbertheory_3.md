# mathd_numbertheory_3

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_numbertheory_3:
  fixes n :: nat
  assumes "n = 3"
  shows "prime (n^2 - 3*n + 2)"
proof -
  have "n^2 - 3*n + 2 = 3^2 - 3*3 + 2" using assms by simp
  then have "n^2 - 3*n + 2 = 9 - 9 + 2" by simp
  then have "n^2 - 3*n + 2 = 2" by simp
  then show "prime (n^2 - 3*n + 2)" by (metis Suc_le_D Suc_n_not_le_n add.commute add_2_eq_Suc add_Suc_shift add_cancel_left_left add_diff_cancel_right' add_leE assms diff_Suc_Suc diff_diff_cancel diff_mult_distrib diff_self_eq_0 full_nat_induct le_add_diff_inverse2 le_zero_eq minus_nat.diff_0 mult.commute mult_eq_0_iff nat_arith.suc1 nat_le_linear not_less_eq_eq not_prime_0 numeral_2_eq_2 numeral_3_eq_3 power2_eq_square two_is_prime_nat)
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_353.json`

Let $S = 2010 + 2011 + \cdots + 4018$. Compute the residue of $S$, modulo 2009. Show that it is 0.
### Informal Proof:
Modulo 2009, $S \equiv 1 + 2 + \cdots + 2008 + 0$. Now, the right-hand side is simply the sum of the integers from 1 to 2008, which is $\frac{2008 \cdot 2009}{2} = 1004 \cdot 2009$, so $S \equiv 1004 \cdot 2009 \equiv 1004 \cdot 0 \equiv 0$ modulo 2009.
### Solution:
```isabelle
theorem mathd_numbertheory_353:
  fixes s :: nat
  assumes "s = (\<Sum> k\<in> {2010..<4019}. k)" 
  shows "s mod 2009 = 0"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_353 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
imports Complex_Main 
begin

(* no helper function required in this theorem *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_353: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes s :: nat
  assumes "s = (\<Sum> k\<in> {2010..<4019}. k)" 
  shows "s mod 2009 = 0"
proof -
  (* Step 1: Modulo 2009, $S \equiv 1 + 2 + \cdots + 2008 + 0$ *)
  have "s mod 2009 =  (\<Sum> k\<in> {2010..<4019}. k) mod 2009"
    using assms by simp

  (* Step 2: The right-hand side is simply the sum of the integers from 1 to 2008, which is $\frac{2008 \cdot 2009}{2} = 1004 \cdot 2009$, so $S \equiv 1004 \cdot 2009 \equiv 1004 \cdot 0 \equiv 0$ modulo 2009 *)
  also have "... =  (\<Sum> k\<in> {1..<2009}. k) mod 2009" by (rule sum_lessThan_diff)
  also have "... = 1004 * 2009 mod 2009" by (rule sum_integers)
  also have "... = 0" by (rule mod_mult_right_eq)
  finally show "s mod 2009 = 0" .
qed

end
```
