# gcd_lcm_relation

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma gcd_lcm_relation:
  fixes a b :: nat
  assumes "0 < a" "0 < b"
  shows "gcd a b * lcm a b = a * b"
proof -
  have "gcd a b > 0" using assms by auto
  hence "lcm a b = (a * b) div (gcd a b)" by (metis lcm_nat_def)
  then have "gcd a b * lcm a b = gcd a b * ((a * b) div (gcd a b))" by simp
  also have "... = a * b" by auto
  finally show ?thesis by simp
qed
```


## Usage 1 of 1:
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
  imports Complex_Main
begin

(* Step 1: Recall the relationship between gcd and lcm *)
lemma gcd_lcm_relation: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: nat
  assumes "0 < a" "0 < b"
  shows "gcd a b * lcm a b = a * b"
proof -
  have "gcd a b > 0" using assms by auto
  hence "lcm a b = (a * b) div (gcd a b)" by (metis lcm_nat_def)
  then have "gcd a b * lcm a b = gcd a b * ((a * b) div (gcd a b))" by simp
  also have "... = a * b" by auto
  finally show ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_100:
  fixes n :: nat
  assumes "gcd n 40 = 10"
      and "lcm n 40 = 280" 
  shows "n = 70"
proof -
  (* Step 2: Use the gcd-lcm relation *)
  have "gcd n 40 * lcm n 40 = n * 40"
    using gcd_lcm_relation[of n 40] assms by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 3: Substitute known values into the relation *)
  then have "10 * 280 = n * 40"
    using assms by simp

  (* Step 4: Simplify the equation *)
  then have "n * 40 = 2800"
    by simp

  (* Step 5: Solve for n *)
  then have "n = 2800 div 40"
    by auto

  (* Step 6: Calculate the value of n *)
  thus "n = 70"
    by simp
qed

end
```
