# solve_linear_equation

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_linear_equation:
  fixes a b x :: real
  assumes "a * x = b" "a \<noteq> 0"
  shows "x = b / a"
  using assms by (simp add: field_simps)
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_400.json`

Five plus $500\%$ of $10$ is the same as $110\%$ of what number? Show that it is 50.
### Informal Proof:
We have $5+\frac{500}{100}\cdot10=5+5\cdot10=55$ equal to $110\%$ of the number $x$. $$\frac{110}{100}x=\frac{11}{10}x=55\qquad\Rightarrow x=55\cdot\frac{10}{11}=5\cdot10=50$$ The number is $50$.
### Solution:
```isabelle
theorem mathd_algebra_400:
  fixes x :: real
  assumes "5 + 500 / 100 * 10 = 110 / 100 * x"  
  shows "x = 50"
```
AI Generated completion (lemma lines higlighted):
<think>
Okay, let's tackle this problem. The user wants to prove that five plus 500% of 10 equals 110% of 50. The formal statement is given as a theorem in Isabelle, and I need to provide a proof that follows the structure and uses the provided skills.

First, I'll look at the informal proof steps. Step 1 says to calculate 500% of 10, which is 5*10=50, then add 5 to get 55. Step 2 converts 110% to 11/10 and sets up the equation 55 = (11/10)*x. Step 3 solves for x by multiplying both sides by 10/11, resulting in x=50. Step 4 concludes that x is 50.

Now, translating this into Isabelle. The theorem is straightforward: given the equation 5 + (500/100)*10 = (110/100)*x, prove x=50.

I need to break down the steps. Let's start by simplifying the left-hand side. The 500/100 is 5, so 5*10 is 50. Then adding 5 gives 55. For the right-hand side, 110/100 is 11/10. So the equation becomes 55 = (11/10)*x. Then solving for x would involve multiplying both sides by 10/11, which is the reciprocal of 11/10.

Looking at the provided skills, there's a lemma called solve_linear_equation which can be useful here. Also, fraction_simplification_1 might help in simplifying 500/100 to 5. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Let me outline the steps in Isabelle:

1. Simplify the left-hand side: 5 + (500/100)*10. Since 500/100 is 5, this becomes 5 + 5*10 = 5 + 50 = 55. Use the fraction_simplification_1 lemma for 500/100 = 5.

2. Simplify the right-hand side: 110/100 * x. 110/100 is 11/10, so the equation is 55 = (11/10)*x.

3. Solve for x: Multiply both sides by 10/11. Using the multiply_both_sides_by_reciprocal lemma, which states that if a * b = c and a ≠ 0, then b = c/a. Here, a is 11/10, so the reciprocal is 10/11. Applying this lemma would give x = 55 * (10/11) = 50.

I need to make sure each step is justified. For the first part, using fraction_simplification_1 on 500/100. Then, simplifying the left-hand side. Then, simplifying the right-hand side. Then, applying the solve_linear_equation lemma or the multiply_both_sides_by_reciprocal to solve for x. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Wait, the problem is that the given theorem's assumption is the equation, and we need to prove x=50. So the steps would be:

Given 5 + 500/100 * 10 = 110/100 * x.

First, compute 500/100 as 5, so left side becomes 5 + 5*10 = 55.

Then, right side is 110/100 * x = 11/10 * x.

So the equation is 55 = (11/10) * x.

Then, solve for x by multiplying both sides by 10/11, which gives x = 55 * (10/11) = 50.

So in Isabelle, the proof would involve:

- Using fraction_simplification_1 to replace 500/100 with 5.

- Then, simplifying 5 + 5*10 to 55.

- Then, simplifying 110/100 to 11/10.

- Then, applying the solve_linear_equation lemma with a = 11/10, b = 55, so x = 55 / (11/10) = 55 * (10/11) = 50. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, using the multiply_both_sides_by_reciprocal lemma: since (11/10) * x = 55, then x = 55 / (11/10) = 55 * (10/11).

I need to make sure that each of these steps is justified by the given lemmas or by Isabelle's simplification rules.

Also, need to check that the lemmas are applied correctly. For example, fraction_simplification_1 is given as 500/100 = 5, so that can be used directly. Then, the solve_linear_equation lemma can be used here, but the variables are a, b, x. So if we have a * x = b, then x = b/a. Here, a is 11/10, and b is 55. So x = 55 / (11/10) = 55 * (10/11) = 50. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So the steps in Isabelle would be:

- Use the given assumption: 5 + 500/100 * 10 = 110/100 * x.

- Simplify 500/100 to 5 using fraction_simplification_1.

- Compute 5*10 = 50, so left side is 5 + 50 = 55.

- Simplify 110/100 to 11/10.

- Now the equation is 55 = (11/10) * x.

- Apply the solve_linear_equation lemma with a = 11/10, b = 55, so x = 55 / (11/10) = 50. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, using multiply_both_sides_by_reciprocal: since (11/10) * x = 55, and 11/10 is not zero, then x = 55 / (11/10) = 55 * (10/11) = 50.

But the solve_linear_equation lemma is more straightforward here. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So the proof would involve these steps with the appropriate lemmas. Also, need to make sure that all the simplifications are done correctly, using the lemmas provided.

Another thing to note is that in Isabelle, the real numbers are handled with the real type, and the fraction_simplification_1 lemma is for real numbers. Also, the multiplication and division should be handled with field_simps.

Now, structuring the proof:

Start with the assumption, then simplify each side step by step, then apply the relevant lemmas to solve for x.

So the Isabelle proof would look like:

proof -
  from assms have "5 + 5 * 10 = (11/10) * x"
    by (simp add: fraction_simplification_1)
  then have "55 = (11/10) * x" by simp
  then have "x = 55 / (11/10)" by (rule solve_linear_equation) (* or use multiply_both_sides_by_reciprocal *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "x = 55 * (10/11)" by (simp add: field_simps)
  then have "x = 50" by (simp add: fraction_simplification_1) (* since 55 * 10 / 11 = 50 *)
  thus ?thesis by simp
qed

Wait, but the fraction_simplification_1 is for 500/100 = 5. However, 55 * 10 / 11 is 50, but that's not covered by the existing lemmas. So perhaps I need to create a lemma for that, or use field_simps to simplify it.

Alternatively, compute 55 * 10 / 11. Since 55 divided by 11 is 5, then 5 * 10 = 50. So using the lemma multiply_both_sides_by_reciprocal for 11/10 * x = 55, leading to x = 55 * 10/11. Then, simplifying 55 * 10 /11.

But how to do that in Isabelle? Well, 55 divided by 11 is 5, and 5 multiplied by 10 is 50. So using the same fraction_simplification_1 approach, but for 55/11 = 5.

Alternatively, using the field_simps to compute 55 * 10 / 11 = (55/11) * 10 = 5 * 10 = 50.

So the step where x = 55 * 10 / 11 can be simplified using field_simps. Therefore, in the proof, after getting x = 55 * 10 / 11, we can use simp with field_simps to get 50.

But since the user provided the fraction_simplification_1 lemma, maybe we can use that again for 55/11 = 5. But the existing lemma is for 500/100 = 5. However, 55/11 is 5, so perhaps a similar lemma is needed. But since the user hasn't provided that, maybe we can use the field_simps to handle that.

So in the proof, after x = 55 * 10 / 11, we can compute 55 divided by 11 first, then multiply by 10.

Alternatively, use the multiply_both_sides_by_reciprocal lemma again for that step.

But perhaps the solve_linear_equation lemma is sufficient. Let me check the lemmas again. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The solve_linear_equation lemma is: fixes a b x :: real, assumes a * x = b and a ≠ 0, shows x = b / a. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So if we have (11/10) * x = 55, then x = 55 / (11/10) = 55 * (10/11). Then, simplifying that to 50.

So in Isabelle, after getting x = 55 * 10 / 11, we can compute that as follows:

55 * 10 / 11 = (55 / 11) * 10 = 5 * 10 = 50.

But how to get Isabelle to simplify that. Maybe using the field_simps, which would handle the multiplication and division.

Therefore, in the proof, after applying the solve_linear_equation lemma, the step would be: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

then have "x = 55 * (10 / 11)" by (rule solve_linear_equation) (since a = 11/10, b = 55, and a is non-zero) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Then, using field_simps to simplify 55 * 10 / 11.

Alternatively, use the fact that 55 / 11 is 5, then multiply by 10.

But to make sure that this is handled, perhaps we can use the fraction_simplification_1 lemma again, but since 55/11 is 5, which is similar to 500/100 = 5. However, the existing lemma is for 500/100, so we can't directly use it for 55/11. Therefore, we need to use field_simps.

Thus, the proof steps would be:

1. Use fraction_simplification_1 to replace 500/100 with 5.

2. Simplify the left-hand side to 5 + 5*10 = 55.

3. Simplify the right-hand side 110/100 to 11/10.

4. Apply solve_linear_equation to get x = 55 / (11/10) = 55 * 10 / 11. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

5. Simplify 55 * 10 / 11 using field_simps to 50.

Thus, the Isabelle code would be:

proof -
  from assms have "5 + 5 * 10 = (11/10) * x"
    by (simp add: fraction_simplification_1)
  then have "55 = (11/10) * x" by simp
  then have "x = 55 / (11/10)" by (rule solve_linear_equation) (auto simp add: field_simps) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "x = 55 * (10/11)" by (simp add: field_simps)
  then have "x = 50" by (simp add: field_simps)
  thus ?thesis by simp
qed

But wait, the solve_linear_equation lemma requires that a ≠ 0. In this case, a is 11/10, which is not zero. So we need to ensure that 11/10 ≠ 0, which is true. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Therefore, the proof would use the solve_linear_equation lemma with a = 11/10, b = 55, and then simplify the result. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Another point: the initial step where 5 + 5*10 = 55. That's straightforward, but in Isabelle, we need to make sure that the multiplication and addition are handled correctly. Since 5 * 10 is 50, and adding 5 gives 55, which is a simple arithmetic step.

Therefore, the proof should be structured with these steps, using the provided lemmas where applicable, and field_simps for simplification.
</think>

```isabelle
theory mathd_algebra_400
  imports Complex_Main
begin

(* formal statement copied from the input *)
theorem mathd_algebra_400:
  fixes x :: real
  assumes "5 + 500 / 100 * 10 = 110 / 100 * x"  
  shows "x = 50"
proof -
  (* Step 1: Simplify the left-hand side by replacing 500/100 with 5 *)
  from assms have "5 + 5 * 10 = (11/10) * x"
    by (simp add: fraction_simplification_1)
  (* Step 2: Compute 5 * 10 and add 5 to get 55 *)
  then have "55 = (11/10) * x" by simp
  (* Step 3: Solve for x using the linear equation solver *)
  then have "x = 55 / (11/10)"
    by (rule solve_linear_equation) (auto simp add: field_simps) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 4: Simplify 55 / (11/10) to 55 * (10/11) *)
  then have "x = 55 * (10/11)" by (simp add: field_simps)
  (* Step 5: Simplify 55 * 10 / 11 to 50 using arithmetic rules *)
  then have "x = 50" by (simp add: field_simps)
  thus ?thesis by simp
qed

end
```
