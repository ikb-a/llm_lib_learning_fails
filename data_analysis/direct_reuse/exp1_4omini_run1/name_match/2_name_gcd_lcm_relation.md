# gcd_lcm_relation

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 2

Lemma:
```isabelle
lemma gcd_lcm_relation:
  fixes a b :: nat
  assumes "gcd a b > 0"
  shows "gcd a b * lcm a b = a * b"
  using assms by auto
```


## Usage 1 of 2:
### Problem:
Task name: `mathd_numbertheory_100.json`

Find $n$ if $\gcd(n,40) = 10$ and $\mathop{\text{lcm}}[n,40] = 280$. Show that it is 70.
### Informal Proof:
We know that $\gcd(a,b) \cdot \mathop{\text{lcm}}[a,b] = ab$ for all positive integers $a$ and $b$.  Hence, in this case, $10 \cdot 280 = n \cdot 40$, so $n = 10 \cdot 280/40 = 70$.
### Solution:
```isabelle
theorem mathd_numbertheory_100:
  fixes n :: nat
  assumes "gcd n 40 = 10"
      and "lcm n 40 = 280" 
  shows "n = 70"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_100
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

(* lemma 1. A lemma that establishes the relationship between gcd and lcm. This will be useful for simplifying our proofs involving gcd and lcm. *)
lemma gcd_lcm_relation: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: nat
  assumes "gcd a b = g" 
  shows "lcm a b = (a * b) div g"
proof -
  have "gcd a b * lcm a b = a * b" 
    using assms by auto
  then show ?thesis 
    using assms by auto
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_100:
  fixes n :: nat
  assumes "gcd n 40 = 10"
      and "lcm n 40 = 280" 
  shows "n = 70"
proof -
  (* Step 1: Start with the given conditions: \( \gcd(n, 40) = 10 \) and \( \mathop{\text{lcm}}[n, 40] = 280 \). *)
  have gcd_n_40: "gcd n 40 = 10" using `gcd n 40 = 10` by simp
  have lcm_n_40: "lcm n 40 = 280" using `lcm n 40 = 280` by simp

  (* Step 2: Recall the relationship between gcd and lcm: \( \gcd(a, b) \cdot \mathop{\text{lcm}}[a, b] = a \cdot b \). *)
  have relation: "gcd n 40 * lcm n 40 = n * 40" 
    using gcd_lcm_relation[of n 40] gcd_n_40 lcm_n_40 by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 3: Substitute the known values into the equation: \( 10 \cdot 280 = n \cdot 40 \). *)
  have substitution: "10 * 280 = n * 40" using relation by simp

  (* Step 4: Simplify the left-hand side: \( 2800 = n \cdot 40 \). *)
  have simplified: "2800 = n * 40" using substitution by simp

  (* Step 5: Solve for \( n \) by dividing both sides by 40: \( n = \frac{2800}{40} = 70 \). *)
  have solved: "n = 2800 div 40" using simplified by simp
  then have "n = 70" by simp

  (* Step 6: Conclude that \( n = 70 \) satisfies both conditions of the problem. *)
  thus ?thesis by simp
qed

end
```


## Usage 2 of 2:
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
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

(* formal statement copied from the input *)
theorem mathd_numbertheory_222:
  fixes b :: nat
  assumes "lcm 120 b = 3720"
    and "gcd 120 b = 8" 
  shows "b = 248"
proof -
  (* By the relationship between LCM and GCD, we know that: *)
  (* gcd(a, b) * lcm(a, b) = a * b *)
  (* Here, let a = 120 and b be the unknown number. *)
  
  have lcm_gcd_relation: "gcd 120 b * lcm 120 b = 120 * b" 
    using assms by (metis gcd_lcm_relation) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Substitute the known values into the equation. *)
  have substitution: "8 * 3720 = 120 * b" 
    using lcm_gcd_relation assms by auto

  (* Now we can solve for b. *)
  (* Rearranging gives us: b = (8 * 3720) / 120 *)
  have b_formula: "b = (8 * 3720) div 120" 
    using substitution by auto

  (* Calculate (8 * 3720) / 120. *)
  have b_value: "b = (29760) div 120"
    using b_formula by simp

  (* Simplifying gives us b = 248. *)
  have final_value: "b = 248" 
    using b_value by (simp add: div_by_120)

  (* Thus, we conclude that the other number is 248. *)
  thus ?thesis by (simp add: final_value)
qed

end
```
