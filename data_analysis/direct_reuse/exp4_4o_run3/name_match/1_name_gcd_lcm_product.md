# gcd_lcm_product

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma gcd_lcm_product:
  fixes a b :: nat
  shows "gcd a b * lcm a b = a * b"
proof -
  have "gcd a b * (a * b) = a * b * gcd a b"
    by (simp add: mult.commute)
  moreover have "lcm a b = (a * b) div gcd a b"
    by (metis lcm_nat_def)
  ultimately have "gcd a b * lcm a b = gcd a b * ((a * b) div gcd a b)"
    by simp
  also have "... = (gcd a b * (a * b)) div gcd a b"
    by (simp add: mult.commute)
  also have "... = a * b"
    by (simp add: div_mult_self1)
  finally show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_222.json`

The least common multiple of two numbers is 3720, and their greatest common divisor is 8. Given that one of the numbers is 120, what is the other number? Show that it is 248.
### Informal Proof:
We know that $\gcd(a,b) \cdot \mathop{\text{lcm}}[a,b] = ab$ for all positive integers $a$ and $b$.  Hence, in this case, the other number is $8 \cdot 3720/120 = 248$.
### Solution:
```isabelle
theorem mathd_numbertheory_222:
  fixes b :: nat
  assumes "lcm 120 b = 3720"
    and "gcd 120 b = 8" 
  shows "b = 248"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_222
  imports Complex_Main
begin

(* We will use a known relationship between gcd and lcm of two numbers to solve this problem. *)

lemma gcd_lcm_product: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: nat
  shows "gcd a b * lcm a b = a * b"
proof -
  (* Start with the definition of lcm in terms of gcd *)
  have "lcm a b = (a * b) div gcd a b"
    by (metis lcm_nat_def)
  (* Multiply both sides of the definition by gcd a b *)
  then have "gcd a b * lcm a b = gcd a b * ((a * b) div gcd a b)"
    by simp
  (* Simplify the equation using division properties *)
  also have "... = (gcd a b * (a * b)) div gcd a b"
    by simp
  (* Final simplification to arrive at the product of the numbers *)
  also have "... = a * b"
    using gcd_mult_distrib_nat by simp
  finally show ?thesis .
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_222:
  fixes b :: nat
  assumes "lcm 120 b = 3720"
    and "gcd 120 b = 8" 
  shows "b = 248"
proof -
  (* Use the relationship between gcd, lcm, and the product of two numbers *)
  have relation: "gcd 120 b * lcm 120 b = 120 * b"
    using gcd_lcm_product[of 120 b] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Substitute the given values into the equation *)
  then have "8 * 3720 = 120 * b"
    using assms by simp
  (* Solve for b by dividing both sides by 120 *)
  then have "b = (8 * 3720) div 120"
    by simp
  (* Perform the arithmetic calculation *)
  then have "b = 248"
    by eval
  (* Conclude that the other number is indeed 248 *)
  show ?thesis
    using `b = 248` by simp
qed

end
```
