# verify_enrollment

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma verify_enrollment:
  fixes x :: nat
  assumes "x = 598 / 1.04"
  shows "x = 575"
proof -
  from assms have "x = 598 / (26 / 25)" by auto
  also have "... = 598 * 25 / 26" by (simp add: divide_divide_eq_left)
  also have "... = (598 / 26) * 25" by (simp add: field_simps)
  also have "... = 23 * 25" by auto
  also have "... = 575" by simp
  finally show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_137.json`

Because of redistricting, Liberty Middle School's enrollment increased to 598 students. This is an increase of $4\%$ over last year's enrollment. What was last year's enrollment? Show that it is 575\text{ students}.
### Informal Proof:
If we knew last year's enrollment at Liberty Middle School, we would multiply by $1.04$ to get the new enrollment of $598$ students. Working backward, we can divide $598$ by $1.04$ to get $575\text{ students}$. Alternatively, we could solve the equation $x + 0.04x = 598$, where $x$ is last year's enrollment.
### Solution:
```isabelle
theorem mathd_algebra_137:
  fixes x::nat
  assumes " x + 4 / 100 * x = 598" 
  shows "x = 575"
```
AI Generated completion (lemma lines higlighted):
<think>
Okay, let's tackle this problem. The user wants to prove that last year's enrollment was 575 students given that this year's enrollment is 598, which is a 4% increase. The formal statement is given as a theorem in Isabelle.

First, I need to understand the informal proof steps. Step 1 says that x is last year's enrollment, and this year's is 1.04x. The equation is set up as 1.04x = 598. Then solving for x gives 598 / 1.04 = 575. 

Looking at the formal statement, the assumption is "x + 4/100 * x = 598". That simplifies to 1.04x = 598. The goal is to show x = 575. 

In the previous examples, there was a lemma called equation_simplification that converted the equation x + 0.04x = 598 into 1.04x = 598. Maybe I can use that here. The user's proof used that lemma, so perhaps I should replicate that approach.

Wait, the user's formal statement has "x + 4 / 100 * x = 598". The 4/100 is 0.04, so the equation is indeed 1.04x = 598. Then solving for x would involve dividing both sides by 1.04. But in Isabelle, dealing with division in real numbers might require some lemmas. 

Looking at the previous example (verify_enrollment), they converted 598 / 1.04 into 598 * 25 / 26 by rewriting 1.04 as 26/25. That seems like a useful approach here. Let me check that.  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So 1.04 is equal to 26/25, because 26 divided by 25 is 1.04. Therefore, dividing by 1.04 is the same as multiplying by 25/26. So x = 598 * (25/26). Then, 598 divided by 26 is 23, and 23 * 25 is 575. 

So the steps would be: 

1. Use the equation_simplification lemma to rewrite x + 0.04x = 598 as 1.04x = 598.
2. Then express 1.04 as 26/25, so x = 598 * 25 / 26.
3. Compute 598 / 26 = 23, then multiply by 25 to get 575.

In the previous examples, the verify_enrollment lemma used these steps. So perhaps I can use that lemma here. However, the user's problem is different because the equation is already given as x + 0.04x = 598, so maybe the equation_simplification lemma is directly applicable.  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Wait, in the given formal statement, the assumption is "x + 4 / 100 * x = 598". So the first step is to simplify that to 1.04x = 598. The equation_simplification lemma does exactly that. So I can use that lemma here.

Then, solving 1.04x = 598 for x would involve dividing both sides by 1.04. However, in Isabelle, division in real numbers can be tricky. The verify_enrollment lemma used the fact that dividing by 1.04 is equivalent to multiplying by 25/26. So perhaps I need to create a lemma that allows me to rewrite 598 / 1.04 as 598 * 25 / 26.  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, since 1.04 is 26/25, then 598 divided by (26/25) is 598 * 25 / 26. Then compute that value. 

So the steps in the proof would be:

- Use equation_simplification to get 1.04x = 598.
- Then, solve for x by dividing both sides by 1.04.
- Show that 598 divided by 1.04 is 575.

But how to do that in Isabelle? The previous example used the lemma verify_enrollment, which showed that 598 / 1.04 equals 575 by rewriting the division as multiplication by 25/26. So I can use that lemma here.  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Wait, the user's problem is to show that x = 575 given x + 0.04x = 598. So the steps would be:

1. Use equation_simplification to get 1.04x = 598.
2. Then, solve for x: x = 598 / 1.04.
3. Use the lemma verify_enrollment (from the previous example) to show that 598 / 1.04 = 575. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

But in the current problem, the formal statement is different. The assumption is "x + 4 / 100 * x = 598", which is the same as 1.04x = 598. Then, the lemma equation_simplification would convert that to 1.04x = 598. Then, solving for x gives x = 598 / 1.04. Then, using the verify_enrollment lemma to show that 598 / 1.04 is 575. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

But in the previous example, the lemma verify_enrollment was for 598 / 1.04 = 575. So if I can use that lemma here, then the proof would be straightforward. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Wait, but the current problem's formal statement is "x + 4 / 100 * x = 598" and the conclusion is "x = 575". So the steps would be:

- Use equation_simplification to get 1.04x = 598.
- Then, divide both sides by 1.04, leading to x = 598 / 1.04.
- Then, using the lemma verify_enrollment (or a similar one) to show that 598 / 1.04 = 575. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So the key is to have a lemma that proves 598 / 1.04 = 575. The previous example had such a lemma, so I can use that here.

Alternatively, create a new lemma similar to verify_enrollment for this specific case. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Wait, but the user's problem is to show that x = 575 given x + 0.04x = 598. The previous example's lemma verify_enrollment was for the case where x = 598 / 1.04 and showed that equals 575. So in this case, the same lemma can be used. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Therefore, the proof would be:

- Apply equation_simplification to get 1.04x = 598.
- Then, solve for x: x = 598 / 1.04.
- Use the verify_enrollment lemma to show that 598 / 1.04 = 575. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
- Therefore, x = 575.

But I need to make sure that the lemma verify_enrollment is available. However, in the current problem, the user hasn't provided that lemma. So I need to create it or use the steps from the previous example. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, create a lemma that directly computes 598 / 1.04 as 575. Let's think about how to do that in Isabelle.

The previous example used the following steps:

lemma verify_enrollment: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: nat
  assumes "x = 598 / 1.04"
  shows "x = 575"
proof -
  from assms have "x = 598 / (26 / 25)" by auto
  also have "... = 598 * 25 / 26" by (simp add: divide_divide_eq_left)
  also have "... = (598 / 26) * 25" by (simp add: field_simps)
  also have "... = 23 * 25" by auto
  also have "... = 575" by simp
  finally show ?thesis by simp
qed

So the key steps are rewriting 1.04 as 26/25, then using division and multiplication properties.

Therefore, in the current problem, after getting to x = 598 / 1.04, we can apply the same steps to show that equals 575.

So the proof in Isabelle would be:

- Use equation_simplification to get 1.04x = 598.
- Then, x = 598 / 1.04.
- Then, apply the same steps as in the verify_enrollment lemma to show that equals 575. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Therefore, the Isabelle proof would involve these steps. But since the user's problem may not have the verify_enrollment lemma, I need to create it within the proof or use the steps directly. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Wait, the user's problem has the formal statement as a theorem, and the proof is to be written. So the user's code example includes the verify_enrollment lemma, but in the current problem, the user is asking to create the proof for mathd_algebra_137. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So in this case, the user's proof should include the necessary lemmas. However, the user's previous example used the verify_enrollment lemma. But in the current problem, the user hasn't provided that lemma, so I need to either include it or derive the steps directly. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

But the user's instructions say to create the proof with lemmas as needed. So perhaps I should include the lemma verify_enrollment in the current proof, or create a similar one. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, use the same steps as in the previous example.

Putting it all together, the proof would be:

First, apply equation_simplification to get 1.04x = 598.

Then, solve for x: x = 598 / 1.04.

Then, show that 598 / 1.04 equals 575 by the same steps as in the verify_enrollment lemma. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So in the code, the steps would be:

proof -
  from assms have "1.04 * x = 598" by (rule equation_simplification)
  then have "x = 598 / 1.04" by (simp add: field_simps)
  also have "... = 598 * 25 / 26" by (simp add: divide_divide_eq_left)
  also have "... = (598 / 26) * 25" by (simp add: field_simps)
  also have "... = 23 * 25" by auto
  also have "... = 575" by simp
  finally show ?thesis by simp
qed

But I need to make sure that the division and multiplication steps are valid in Isabelle. The previous example used divide_divide_eq_left and field_simps. So the same steps should apply here.

Therefore, the lemma verify_enrollment can be used here, but since the user's problem may not have it, I need to either include it or derive the steps. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, create a lemma within the proof to handle the division.

But the user's previous example included the lemma verify_enrollment, so perhaps in this problem, the same approach is used. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So the final proof would involve:

- Applying equation_simplification to get 1.04x = 598.
- Then, solving for x by division.
- Then, showing that division results in 575 using the steps from verify_enrollment. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Thus, the Isabelle code would be structured with these steps, using the necessary lemmas and simplifications.
</think>

```isabelle
theory mathd_algebra_137
imports Complex_Main
begin

(* Lemma: Simplify the equation x + 0.04 * x = 598 to 1.04 * x = 598 *)
lemma equation_simplification:
  fixes x :: real
  assumes "x + 0.04 * x = 598"
  shows "1.04 * x = 598"
proof -
  from assms have "1.04 * x = x + 0.04 * x" by (simp add: field_simps)
  also have "... = 598" by (rule assms)
  finally show ?thesis by simp
qed

(* Lemma: Show that 598 / 1.04 equals 575 by rewriting division as multiplication *)
lemma division_verification:
  fixes x :: real
  assumes "x = 598 / 1.04"
  shows "x = 575"
proof -
  from assms have "x = 598 / (26 / 25)" by auto
  also have "... = 598 * 25 / 26" by (simp add: divide_divide_eq_left)
  also have "... = (598 / 26) * 25" by (simp add: field_simps)
  also have "... = 23 * 25" by auto
  also have "... = 575" by simp
  finally show ?thesis by simp
qed

(* Formal statement copy from the input *)
theorem mathd_algebra_137:
  fixes x::nat
  assumes "x + 4 / 100 * x = 598" 
  shows "x = 575"
proof -
  (* Step 1: Simplify the equation to 1.04 * x = 598 *)
  have "1.04 * x = 598" 
    using equation_simplification[where x = "real x"] 
    by (simp add: assms of_nat_real_def)
  
  (* Step 2: Solve for x by dividing both sides by 1.04 *)
  then have "x = 598 / 1.04" 
    by (simp add: field_simps)
  
  (* Step 3: Show that 598 / 1.04 = 575 using the division_verification lemma *)
  also have "... = 575" 
    by (rule division_verification)
  
  (* Step 4: Conclude that x = 575 *)
  finally show ?thesis 
    by simp
qed

end
```
