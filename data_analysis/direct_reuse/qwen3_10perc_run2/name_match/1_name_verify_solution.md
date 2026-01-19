# verify_solution

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma verify_solution:
  fixes x :: nat
  assumes "x = 575"
  shows "x + 4 / 100 * x = 598"
proof -
  have "x + 4 / 100 * x = x * (1 + 4 / 100)"
    by (simp add: distrib_left)
  also have "... = x * (26 / 25)"
    by (simp add: field_simps)
  also have "... = 575 * (26 / 25)"
    by (simp add: assms)
  also have "... = (25 * 23) * (26 / 25)"
    by (simp add: assms)
  also have "... = 23 * 26"
    by (simp add: divide_cancel_left)
  also have "... = 598"
    by simp
  finally show ?thesis .
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
Okay, let's tackle this problem. The user wants to prove that last year's enrollment was 575 students given that this year's enrollment is 598, which is a 4% increase. The formal statement is given as a theorem in Isabelle, and I need to write a proof for it.

First, I remember that in the previous examples, there were lemmas that helped simplify expressions involving percentages. For instance, the verify_solution lemma from useful skill 1 shows how to handle equations with percentages by converting them into fractions. Maybe I can use a similar approach here. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The problem starts with the equation x + 4/100 * x = 598. I need to solve for x. Let's see. Combining the terms, that's x*(1 + 4/100) = 598. Simplifying 1 + 4/100 gives 104/100, which reduces to 26/25. So, x*(26/25) = 598. Then, solving for x would involve multiplying both sides by 25/26, leading to x = 598 * (25/26). 

But in Isabelle, handling fractions with nat types can be tricky because division isn't directly supported for natural numbers. However, the problem states that x is a natural number, so the division must result in an integer. Therefore, I need to ensure that 598 is divisible by 26, and then multiply by 25 to get x.

Looking at the previous example, the percentage_increase_solution lemma was used. It had an assumption that x * 26 = 598 * 25 and concluded x = 575. That seems directly applicable here. So, perhaps I can use that lemma.

Wait, the user's problem is to show that x = 575 given the equation x + 4/100 * x = 598. The steps would involve:

1. Rewriting the equation as x * (1 + 4/100) = 598.
2. Simplifying 1 + 4/100 to 26/25.
3. Therefore, x = 598 * (25/26).
4. Since 598 divided by 26 is 23, then 23 * 25 = 575.

So, in Isabelle, I need to formalize these steps. The key is to manipulate the equation using algebraic rules and then show that 598 * 25 / 26 equals 575. 

I should check if there's a lemma that can help with simplifying fractions. The simplify_fraction lemma from useful skill 2 might be useful. It states that if a*d = b*c, then a/b = c/d. But here, I need to show that 598 * 25 = 26 * 575. Let's check that: 26 * 575 = 26 * (500 + 75) = 13000 + 1950 = 14950. 598 *25 = (600 - 2)*25 = 15000 -50 = 14950. So yes, they are equal. Therefore, using the simplify_fraction lemma with a=598, b=26, c=575, d=25 would show that 598/26 = 575/25, hence x = 575.

But in the problem's formal statement, the assumption is x + 4/100 *x = 598. So the steps would be:

- Start with the equation x + (4/100)x = 598.
- Factor x out to get x*(1 + 4/100) = 598.
- Simplify 1 + 4/100 to 26/25, so x*(26/25) = 598.
- Multiply both sides by 25 to get x*26 = 598*25.
- Then apply the percentage_increase_solution lemma, which takes x*26 = 598*25 and concludes x=575.

Yes, that's exactly what the percentage_increase_solution lemma does. So in the proof, I can use that lemma. 

Therefore, the steps in Isabelle would be:

1. Use algebraic manipulation to transform the original equation into x * 26 = 598 * 25.
2. Apply the percentage_increase_solution lemma with the assumption x * 26 = 598 * 25 to conclude x = 575.

So the proof would look something like:

proof -
  have "x * 26 = 598 * 25"
    by (simp add: assms field_simps)
  then show ?thesis
    by (rule percentage_increase_solution)
qed

But I need to make sure that the percentage_increase_solution lemma is correctly applied. Let me check the lemma's parameters. The lemma percentage_increase_solution has:

assumes "x * 26 = 598 * 25" shows "x = 575"

So yes, if I can derive x * 26 = 598 * 25 from the original equation, then applying the lemma would give the result.

Now, how to derive x * 26 = 598 * 25 from the original equation.

Original equation: x + 4/100 *x = 598.

Let me compute 4/100 as 1/25. So x + (1/25)x = 598. That's x*(1 + 1/25) = 598. Which is x*(26/25) = 598. Multiplying both sides by 25 gives x*26 = 598*25. So that's the step.

In Isabelle, to do this, I can use algebraic simplification. For example, using the distributive law and simplifying the fractions.

Therefore, the steps in the proof would be:

1. Start with the given assumption: x + 4/100 * x = 598.
2. Factor x out: x * (1 + 4/100) = 598.
3. Simplify 1 + 4/100 to 26/25.
4. Multiply both sides by 25 to get x * 26 = 598 * 25.
5. Apply the lemma percentage_increase_solution to conclude x = 575.

So in the Isabelle proof, I need to perform these steps using the appropriate theorems. For step 2, the distrib_left rule can be used. For step 3, simplifying the fraction 1 + 4/100 to 26/25 can be done with field_simps. Then, multiplying both sides by 25 would be done via algebraic manipulation.

Putting this all together, the proof would be structured as follows:

proof -
  have "x + 4/100 * x = 598" by (fact assms)
  also have "... = x * (1 + 4/100)" by (simp add: distrib_left)
  also have "... = x * (26/25)" by (simp add: field_simps)
  also have "... = 598" by (fact assms)
  then have "x * 26 = 598 * 25" by (simp add: mult_left_cancel)
  then show ?thesis by (rule percentage_increase_solution)
qed

Wait, but the mult_left_cancel might not directly apply here. Let me think. The equation is x * (26/25) = 598. To get rid of the denominator, multiplying both sides by 25 would be necessary. In Isabelle, how is that handled?

Alternatively, using the fact that 26/25 is equal to 26 divided by 25. So, x * 26 / 25 = 598. Multiplying both sides by 25 gives x * 26 = 598 * 25. 

In Isabelle, this can be done by using the field_simps to handle the division. For example, using the lemma that a/b = c implies a = c*b, assuming b is not zero. Since 25 is a natural number, and we're in the real numbers (assuming real division), this would hold.

Alternatively, since the original problem is in natural numbers, perhaps the division is exact. But the original equation involves fractions, so Isabelle's real numbers would be involved here.

Wait, but the problem states that x is a natural number, so the equation x + 4/100 *x = 598 must hold with x as a natural number. However, 4/100 is a fraction, so x must be such that 4/100 *x is an integer. But since 4/100 reduces to 1/25, x must be a multiple of 25. However, in the solution, x is 575, which is 25*23, so that works.

But in Isabelle's formalization, the variable x is of type nat, but when dealing with fractions, it's possible that the proof is in the real numbers. However, the original equation is in terms of real numbers. Wait, the problem's formal statement uses nat for x, but the equation involves fractions. That might be a problem because in Isabelle, dividing a natural number by another natural number (like 4/100) would be in the real numbers, but the type of x is nat. So perhaps the proof is in real numbers, with x being a natural number.

But I think the original problem's formal statement is correct, and the proof would proceed in the real numbers, using the fact that x is a natural number. Therefore, the steps would be:

Starting with x + (4/100)*x = 598, which is x * (1 + 4/100) = 598. Then 1 + 4/100 is 26/25, so x * 26/25 = 598. Then, multiplying both sides by 25 gives x * 26 = 598 * 25. Then, since 598 = 26 * 23, substituting that in gives x * 26 = 26 * 23 * 25. Then cancelling 26 from both sides gives x = 23 * 25 = 575.

So in the Isabelle proof, I can use the lemma that allows cancelling a common factor from both sides of an equation, which is mult_left_cancel. However, since 26 is a natural number and not zero, that would work.

Putting this all into code, the proof would look like:

proof -
  have "x + 4 / 100 * x = 598" by (fact assms)
  also have "... = x * (1 + 4 / 100)" by (simp add: distrib_left)
  also have "... = x * (26 / 25)" by (simp add: field_simps)
  also have "... = 598" by (fact assms)
  then have "x * 26 = 598 * 25" by (simp add: mult_left_cancel)
  then show ?thesis by (rule percentage_increase_solution)
qed

But I need to check if the percentage_increase_solution lemma is available. In the previous example, the lemma was named percentage_increase_solution, which assumes x * 26 = 598 * 25 and shows x = 575. So yes, using that lemma would be the right approach.

Therefore, the final proof would use the steps to derive x * 26 = 598 * 25 and then apply the lemma to get x = 575.
</think>

```isabelle
theory mathd_algebra_137
  imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_137:
  fixes x::nat
  assumes "x + 4 / 100 * x = 598" 
  shows "x = 575"
proof -
  (* Step 1: Factor x out of the left-hand side *)
  have "x + 4 / 100 * x = x * (1 + 4 / 100)"
    by (simp add: distrib_left)
  also (* Step 2: Simplify 1 + 4/100 to 26/25 *)
  have "... = x * (26 / 25)"
    by (simp add: field_simps)
  also (* Step 3: Substitute the assumption that the expression equals 598 *)
  have "... = 598"
    by (fact assms)
  then (* Step 4: Multiply both sides by 25 to eliminate the denominator *)
  have "x * 26 = 598 * 25"
    by (simp add: mult_left_cancel)
  then (* Step 5: Apply the lemma to conclude x = 575 *)
  show ?thesis
    by (rule percentage_increase_solution)
qed

end
```
