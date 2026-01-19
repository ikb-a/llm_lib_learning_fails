# solve_linear_equation

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_linear_equation:
  fixes a b x :: real
  assumes "b \<noteq> 0" and "a = b * x"
  shows "x = a / b"
  using assms
  by auto
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
Okay, I need to prove that x equals 50 given the equation 5 + (500/100)*10 = (110/100)*x. Let's break it down step by step.

First, I'll start by simplifying the left-hand side. The term 500/100 is 5, so multiplying that by 10 gives 50. Adding 5 to that gives 55. So the left side simplifies to 55. The right side is (11/10)*x, so the equation becomes 55 = (11/10)*x.

Next, I need to solve for x. To isolate x, I can multiply both sides by the reciprocal of 11/10, which is 10/11. That would give x = 55 * (10/11). Calculating that, 55 divided by 11 is 5, and 5 times 10 is 50. So x must be 50.

I should check if there are any lemmas or simplification rules that can help here. The user provided some examples, like percentage_and_linear_equation and solve_linear_equation. The solve_linear_equation lemma seems useful here because it handles equations of the form a = b*x leading to x = a/b when b is not zero.  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

In this case, after simplifying the equation to 55 = (11/10)*x, applying the solve_linear_equation lemma with a=55 and b=11/10 should give x = 55/(11/10) = 50. Since 11/10 is not zero, the conditions of the lemma are satisfied. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

I need to make sure that each step is justified with the correct Isabelle tactics. For example, simplifying 500/100*10 to 5*10 can be done using mult_divide_mult_cancel_left. Then, using the lemma to solve the linear equation once it's in the form a = b*x.

Putting it all together, the proof should first simplify the equation, apply the lemma to solve for x, and then conclude that x is 50.
</think>

```isabelle
theory mathd_algebra_400
  imports Complex_Main
begin

theorem mathd_algebra_400:
  fixes x :: real
  assumes "5 + 500 / 100 * 10 = 110 / 100 * x"  
  shows "x = 50"
proof -
  (* Step 1: Simplify the left-hand side of the equation: 5 + (500/100)*10 *)
  from assms have "5 + (5 * 10) = (11 / 10) * x" 
    by (simp add: mult_divide_mult_cancel_left)
  (* Step 2: Simplify the left-hand side further to 5 + 50 = 55 *)
  also have "... = 5 + 50" 
    by (simp add: mult_divide_mult_cancel_left)
  also have "... = 55" 
    by simp
  (* Step 3: Re-express the equation as 55 = (11/10)*x *)
  finally have "55 = (11 / 10) * x" 
    by simp
  (* Step 4: Apply the linear equation solver lemma to isolate x *)
  from this have "x = 55 / (11 / 10)" 
    by (rule solve_linear_equation) (auto simp: field_simps) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 5: Simplify the division to obtain x = 50 *)
  also have "... = 55 * (10 / 11)" 
    by (simp add: divide_real_def)
  also have "... = 50" 
    by simp
  (* Step 6: Conclude that x = 50 satisfies the original equation *)
  finally show ?thesis by simp
qed

end
```
