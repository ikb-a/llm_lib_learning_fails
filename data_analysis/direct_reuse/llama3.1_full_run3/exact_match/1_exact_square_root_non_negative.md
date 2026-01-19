# square_root_non_negative

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma square_root_non_negative:
  fixes x :: real
  assumes "x \<ge> 0"
  shows "sqrt x * sqrt x = x"
proof -
  have "sqrt x * sqrt x = (sqrt x)^2" by (metis power2_eq_square)
  then have "sqrt x * sqrt x = x" by (simp add: assms)
  then show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_263.json`

Find $y$: $\sqrt{19+3y} = 7$. Show that it is 10.
### Informal Proof:
Squaring both sides of this equation, we have that $19+3y=49$. Now, we subtract $19$ from both sides of the equation and then divide by $3$ to get that $3y = 30 \Rightarrow y = 10$.
### Solution:
```isabelle
theorem mathd_algebra_263:
  fixes y :: real
  assumes "0 \<le> 19 + 3 * y"
    and "sqrt (19 + 3 * y) = 7" 
  shows "y = 10"
```
AI Generated completion (lemma lines higlighted):
Here is a formal proof for the problem:

```isabelle
theory mathd_algebra_263
imports Complex_Main
begin

(* useful skill 3: square_root_non_negative *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
lemma square_root_non_negative: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x \<ge> 0"
  shows "sqrt x * sqrt x = x"
proof -
  have "sqrt x * sqrt x = (sqrt x)^2" by (metis power2_eq_square)
  then have "sqrt x * sqrt x = x" by (simp add: assms)
  then show ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_263:
  fixes y :: real
  assumes "0 \<le> 19 + 3 * y"
    and "sqrt (19 + 3 * y) = 7" 
  shows "y = 10"
proof -
  (* Step 1: Square both sides of the equation *)
  have "(sqrt (19 + 3 * y))^2 = 7^2" using assms(2) by (smt (verit) assms(1) real_sqrt_pow2_iff)
  then have "19 + 3 * y = 49" by simp
  
  (* Step 2: Subtract 19 from both sides of the equation *)
  then have "3 * y = 30" by auto
  
  (* Step 3: Divide both sides of the equation by 3 *)
  then have "y = 10" by (simp add: field_simps)
  
  (* Step 4: Conclude that the value of y is 10 *)
  then show ?thesis by simp
qed

end
```

This proof uses the `square_root_non_negative` lemma to show that the square of the square root of a non-negative number is equal to the number itself. This is used in Step 1 to square both sides of the equation. The rest of the proof follows the informal proof steps. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
