# lcm_gcd_product

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma lcm_gcd_product:
  fixes a b :: nat
  shows "lcm a b * gcd a b = a * b"
proof -
  have "gcd a b * lcm a b = a * b"
    using prod_gcd_lcm_nat by auto
  hence "lcm a b * gcd a b = a * b"
    by (simp add: mult.commute)
  thus ?thesis .
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

(* formal statement copy from the input *)
theorem mathd_numbertheory_222:
  fixes b :: nat
  assumes "lcm 120 b = 3720"
    and "gcd 120 b = 8" 
  shows "b = 248"
proof -
  (* Step 1. Use the well-known fact that lcm * gcd = product *)
  have prod_equiv: "lcm 120 b * gcd 120 b = 120 * b" 
    by (simp add: lcm_gcd_product) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 2. Substitute the given values from the assumptions. *)
  have "120 * b = 3720 * 8"
    using prod_equiv assms by simp
  (* Step 3. Simplify the right-hand side arithmetic: 3720 * 8 = 29760 *)
  then have "120 * b = 29760" by simp
  (* Step 4. Since 120 divides 120 * b, we can divide both sides by 120.
           We use the lemma Nat.div_mult_self which holds because 120 dvd (120 * b). *)
  then have "b = 29760 div 120" 
    by (simp add: Nat.div_mult_self)
  (* Step 5. Finally, simplify the arithmetic to obtain 29760 div 120 = 248. *)
  then have "b = 248" by simp 
  thus ?thesis .
qed

end
```
