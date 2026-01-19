# mathd_algebra_398

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_398:
  fixes a b c ::real
  assumes "0 < a \<and> 0 < b \<and> 0 < c"
    and "9 * b = 20 * c"
    and "7 * a = 4 * b"
  shows "63 * a = 80 * c"
proof -  
  have "7 * a = 4 * b" and "9 * b = 20 * c" using assms by auto
  then have "63 * a = 4 * (9 * b)" by (simp add: algebra_simps)
  also have "... = 4 * (20 * c)" using assms by (simp add: algebra_simps)
  also have "... = 80 * c" by (simp add: algebra_simps)
  finally show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_398.json`

On planet Larky, 7 ligs = 4 lags, and 9 lags = 20 lugs. How many ligs are equivalent to 80 lugs? Show that it is 63.
### Informal Proof:
Multiply the second equation by 4 to find that 36 lags are equivalent to 80 lugs.  Then multiply the first equation by 9 to find that 36 lags are equivalent to 63 ligs.  Since each is equivalent to 36 lags, 80 lugs and $63$ ligs are equivalent.
### Solution:
```isabelle
theorem mathd_algebra_398:
  fixes a b c ::real
  assumes "0 < a \<and> 0 < b \<and> 0 < c"
    and "9 * b = 20 * c"
    and "7 * a = 4 * b"
  shows "63 * a = 80 * c"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_398 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* lemma 1. According to the step 2 in the informal proof, we derived a special form of the second equation by multiplying 4 to the right hand side. *)
lemma helper1:
  fixes b c :: real
  assumes "0 < b" and "0 < c" and "9 * b = 20 * c"
  shows "36 * b = 80 * c"
proof -
  from assms(3) have "36 * b = 80 * c" by (simp add: algebra_simps)
  thus ?thesis by simp
qed

(* lemma 2. According to the step 3 in the informal proof, we derived a special form of the first equation by multiplying 9 to the left hand side. *)
lemma helper2:
  fixes a b :: real
  assumes "0 < a" and "0 < b" and "7 * a = 4 * b"
  shows "63 * a = 36 * b"
proof -
  from assms(3) have "63 * a = 36 * b" by (simp add: algebra_simps)
  thus ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_398: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c ::real
  assumes "0 < a \<and> 0 < b \<and> 0 < c"
    and "9 * b = 20 * c"
    and "7 * a = 4 * b"
  shows "63 * a = 80 * c"
proof -
  (* Step 1: Multiply the second equation by 4 to find that 36 lags are equivalent to 80 lugs. *)
  have "36 * b = 80 * c" using helper1 assms by simp

  (* Step 2: Multiply the first equation by 9 to find that 36 lags are equivalent to 63 ligs. *)
  have "63 * a = 36 * b" using helper2 assms by simp

  (* Step 3: Since each is equivalent to 36 lags, 80 lugs and $63$ ligs are equivalent. *)
  from this and ‹36 * b = 80 * c› have "63 * a = 80 * c" by simp
  thus ?thesis by simp
qed

end
```
