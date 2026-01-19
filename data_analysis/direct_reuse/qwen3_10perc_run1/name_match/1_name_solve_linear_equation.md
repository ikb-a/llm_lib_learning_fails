# solve_linear_equation

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_linear_equation:
  fixes a x b :: real
  assumes "a \<noteq> 0" and "a * x = b"
  shows "x = b / a"
proof -
  from assms(2) have "a * x = b" by simp
  then have "x = b / a"
    using assms(1) by (simp add: field_simps)
  then show ?thesis by simp
qed
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
Okay, let's tackle this problem. The question is about solving the equation 5 + 500% of 10 equals 110% of some number x, and showing that x is 50. 

First, I need to translate the problem into a formal equation. The informal steps mention calculating 500% of 10, which is 5 * 10 = 50. Then adding 5 to get 55. Then setting up (110/100)*x = 55 and solving for x. 

The formal statement given is: 5 + (500/100)*10 = (110/100)*x, and we need to show x=50. 

Looking at the previous examples, especially the 'useful skill 3' and 'useful skill 4', they used step-by-step simplifications using field_simps and divide_simps. For instance, simplifying fractions like 500/100 to 5, then performing arithmetic operations.

So, the plan is to first simplify the left-hand side of the equation. Let's break down each step. 

Starting with the left side: 5 + (500/100)*10. Simplify 500/100 to 5, so that becomes 5 + 5*10. Then 5*10 is 50, so 5 + 50 = 55. 

On the right side, 110/100 is 11/10. So the equation becomes 55 = (11/10)*x. To solve for x, multiply both sides by 10/11. That gives x = 55*(10/11) = 50. 

In Isabelle, I need to structure each of these steps with appropriate lemmas. The user's previous proofs used 'simp add: field_simps' and similar tactics. 

First, I can use the 'field_simps' to simplify the fractions. For example, 500/100 can be simplified to 5. Then, the equation becomes 5 + 5*10 = (11/10)*x. Then, simplifying 5*10 to 50, leading to 55 = (11/10)*x. 

Next, solving for x would involve multiplying both sides by 10/11. Since multiplication is commutative and associative, this should be straightforward with 'field_simps'. 

I should also check if any of the previous lemmas can be reused. The 'solve_linear_equation' lemma from useful skill 1 might not apply here because this is a linear equation in x, but the coefficients are fractions. However, the 'solve_for_x' lemmas in the examples used step-by-step simplification, so following that approach would be better.  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So, the proof steps would be:

1. Simplify 500/100 to 5.
2. Compute 5*10 to get 50.
3. Add 5 + 50 to get 55.
4. Simplify 110/100 to 11/10.
5. Set up 55 = (11/10)*x.
6. Multiply both sides by 10/11 to solve for x.
7. Simplify 55*(10/11) to 50.

Each of these steps can be justified with 'simp add: field_simps' or 'divide_simps' as needed. 

I need to make sure that each transformation is correctly applied. For example, when simplifying 500/100, using 'field_simps' would recognize that 500 divided by 100 is 5. Similarly, 110/100 simplifies to 11/10. 

Also, when multiplying both sides by 10/11, the 'field_simps' should handle the division and multiplication correctly. 

Potential issues could be if the simplifier doesn't automatically handle the fraction multiplication, but using 'field_simps' should take care of that. 

Another thing to consider is that in the formal statement, the equation is given as 5 + (500/100)*10 = (110/100)*x. So, the first step is to simplify the left side. 

Putting it all together in the Isabelle proof, each step would involve applying simplification rules to reduce the equation step by step until we reach x=50. 

I should structure the proof with comments explaining each step, as in the previous examples. For example, using 'from assms' to get the initial equation, then simplifying fractions, then solving for x. 

Testing each step with 'simp' or 'sledgehammer' might help if there are any stuck points, but given the simplicity of the problem, it should be manageable with basic simplifications.
</think>

```isabelle
theory mathd_algebra_400
  imports Complex_Main
begin

(* Lemma to simplify fractions and perform arithmetic operations step by step *)
lemma simplify_fraction:
  fixes a b :: real
  shows "a / b * c = (a * c) / b"
  by (simp add: field_simps)

(* Lemma to handle multiplication and addition in the left-hand side of the equation *)
lemma simplify_left_side:
  fixes x :: real
  assumes "5 + 500 / 100 * 10 = 110 / 100 * x"
  shows "5 + 5 * 10 = 11 / 10 * x"
proof -
  from assms have "5 + (500 / 100) * 10 = (110 / 100) * x" by simp
  then have "5 + 5 * 10 = (11 / 10) * x"
    by (simp add: field_simps)
  then show ?thesis by simp
qed

(* Lemma to compute the sum on the left-hand side *)
lemma compute_left_sum:
  fixes x :: real
  assumes "5 + 5 * 10 = 11 / 10 * x"
  shows "55 = 11 / 10 * x"
proof -
  from assms have "5 + 50 = 11 / 10 * x" by (simp add: field_simps)
  then show ?thesis by simp
qed

(* Lemma to solve for x by multiplying both sides by the reciprocal of 11/10 *)
lemma solve_for_x:
  fixes x :: real
  assumes "55 = 11 / 10 * x"
  shows "x = 50"
proof -
  from assms have "x = 55 * (10 / 11)" by (simp add: field_simps)
  then show ?thesis by (simp add: field_simps)
qed

(* Formal statement copy from the input *)
theorem mathd_algebra_400:
  fixes x :: real
  assumes "5 + 500 / 100 * 10 = 110 / 100 * x"  
  shows "x = 50"
proof -
  (* Step 1: Simplify the left-hand side by reducing fractions *)
  have "5 + 5 * 10 = 11 / 10 * x"
    using simplify_left_side[OF assms] by simp

  (* Step 2: Compute the sum on the left-hand side *)
  then have "55 = 11 / 10 * x"
    using compute_left_sum by simp

  (* Step 3: Solve for x by multiplying both sides by 10/11 *)
  then show "x = 50"
    using solve_for_x by simp
qed

end
```
