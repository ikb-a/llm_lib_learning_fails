# solve_x_minus_1_over_x_eq_1

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_x_minus_1_over_x_eq_1:
  fixes x :: real
  assumes "x > 0" and "x - 1/x = 1"
  shows "x = (1 + sqrt 5)/2"
proof -
  from assms(2) have "x^2 - x - 1 = 0" by sos
  then have "x^2 - x + 1/4 = 1 + 1/4" by auto
  then have "(x - 1/2)^2 = 5/4" by sos
  then have "x - 1/2 = sqrt(5)/2 \<or> x - 1/2 = -sqrt(5)/2" by (smt (verit) \<open>x\<^sup>2 - x - 1 = 0\<close> assms(1) assms(2) diff_ge_0_iff_ge divide_le_0_1_iff eq_iff_diff_eq_0 le_divide_eq_1_pos numeral_One real_sqrt_divide real_sqrt_four real_sqrt_ge_one real_sqrt_gt_1_iff real_sqrt_one real_sqrt_unique verit_comp_simplify1(3))
  then have "x = (1 + sqrt 5)/2 \<or> x = (1 - sqrt 5)/2" by (simp add: algebra_simps)
  moreover have "(1 - sqrt 5)/2 < 0" by auto
  ultimately show ?thesis using assms(1) by (fastforce)
qed
```


## Usage 1 of 1:
### Problem:
Task name: `amc12a_2002_p13.json`

Two different positive numbers $a$ and $b$ each differ from their reciprocals by $1$. What is $a+b$?  $ \text{(A) }1 \qquad \text{(B) }2 \qquad \text{(C) }\sqrt 5 \qquad \text{(D) }\sqrt 6 \qquad \text{(E) }3 $ Show that it is (C) \sqrt 5.
### Informal Proof:
Each of the numbers $a$ and $b$ is a solution to $\left| x - \frac 1x \right| = 1$.  Hence it is either a solution to $x - \frac 1x = 1$, or to $\frac 1x - x = 1$. Then it must be a solution either to $x^2 - x - 1 = 0$, or to $x^2 + x - 1 = 0$.  There are in total four such values of $x$, namely $\frac{\pm 1 \pm \sqrt 5}2$.   Out of these, two are positive: $\frac{-1+\sqrt 5}2$ and $\frac{1+\sqrt 5}2$. We can easily check that both of them indeed have the required property, and their sum is $\frac{-1+\sqrt 5}2 + \frac{1+\sqrt 5}2 = (C) \sqrt 5$.
### Solution:
```isabelle
theorem amc12a_2002_p13:
  fixes a b :: real
  assumes h0: "0 < a \<and> 0 < b"
      and h1: "a \<noteq> b"
      and h2: "abs (a - 1/a) = 1"
      and h3: "abs (b - 1/b) = 1" 
    shows "a + b = sqrt 5"
```
AI Generated completion (lemma lines higlighted):
<think>
Okay, let's tackle this problem. The question is about two different positive numbers a and b, each differing from their reciprocals by 1. We need to find a + b and show it's √5.

First, I remember from the informal proof that the absolute value equation |x - 1/x| = 1 can be split into two cases: x - 1/x = 1 or 1/x - x = 1. Each case leads to a quadratic equation. The solutions to these quadratics are the two numbers a and b. Then, adding them together should give √5.

So, I need to formalize this in Isabelle. Let me start by considering the two cases for a and b.

For the first case, if a - 1/a = 1, multiplying both sides by a gives a² - 1 = a, which simplifies to a² - a - 1 = 0. The positive solution here is (1 + √5)/2. Similarly, for the second case, 1/a - a = 1, multiplying by a gives 1 - a² = a, leading to a² + a - 1 = 0. The positive solution here is (-1 + √5)/2. 

But wait, I need to make sure these are distinct and positive. The first solution is (1 + √5)/2 ≈ 1.618, and the second is (-1 + √5)/2 ≈ 0.618. Both are positive and different, so they satisfy the conditions.

Now, adding them together: [(1 + √5)/2] + [(-1 + √5)/2] = (1 -1 + √5 + √5)/2 = (2√5)/2 = √5. That's the answer.

But how to formalize this in Isabelle? I need to create lemmas for solving the quadratics and then use them to find a and b.

Looking at the useful skills provided, there's quadratic_solution_1 and solve_x_minus_1_over_x_eq_1. These lemmas solve equations like x - 1/x = 1. Also, positive_roots ensures that the solutions are positive. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So, first, I can use the lemma solve_x_minus_1_over_x_eq_1 for the first case. Then, for the second case, maybe another lemma for 1/x - x = 1. Wait, the existing lemmas might not cover that. Let me check. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The lemma quadratic_solution_2 gives the two roots of x² - x -1 =0, which are (1 ± √5)/2. But for the second case, the equation is x² + x -1 =0. So I need a lemma that solves this equation. Let me create that.

Let me define a lemma for x² + x -1 = 0. The solutions would be [-1 ± √(1 +4)]/2 = [-1 ± √5]/2. Since we need positive solutions, only [-1 + √5]/2 is positive.

So, I can create a lemma for this equation. Then, using these two lemmas, I can get the two solutions and sum them.

Also, the problem states that a and b are different, so the two solutions must be distinct, which they are.

Putting it all together:

1. Use the lemma for x - 1/x =1 to get a = (1 + √5)/2.
2. Use the lemma for 1/x - x =1 to get b = (-1 + √5)/2.
3. Sum them and simplify to √5.

But I need to make sure that the lemmas are correctly structured and that the steps are properly justified in Isabelle.

Also, need to ensure that the lemmas handle the positive roots correctly. For example, the first case gives a positive solution, and the second case also gives a positive solution.

So, the plan is to create two lemmas: one for x - 1/x =1 leading to (1 + √5)/2, and another for 1/x - x =1 leading to (-1 + √5)/2. Then, sum them and show the result is √5.

Now, translating this into Isabelle code. Let me check the existing lemmas again.

The solve_x_minus_1_over_x_eq_1 lemma is similar to the first case. For the second case, maybe I can use a similar approach. Let me write a lemma for the equation 1/x - x =1, which is equivalent to x² +x -1=0. Then, solving that equation. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

So, the steps in the proof would be:

- Prove that for a and b satisfying their respective equations, their values are the two roots.
- Sum them and show the result.

Also, need to handle the absolute value condition. Since the problem states |a - 1/a| =1, which splits into two cases. So, for each of a and b, they must satisfy one of the two equations.

But since a and b are different, they must be from different cases. Hence, one is from the first equation and the other from the second.

Therefore, in the proof, I can split into cases for a and b, solve each equation, then sum the solutions.

But how to structure this in Isabelle? Maybe use the lemmas to get the solutions, then add them.

Let me draft the lemmas first.

First, for x - 1/x =1:

lemma solve_x_minus_1_over_x_eq_1: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x > 0" and "x - 1/x = 1"
  shows "x = (1 + sqrt 5)/2"

This is similar to the existing skill 2.

For the other case, 1/x - x =1:

lemma solve_1_over_x_minus_x_eq_1:
  fixes x :: real
  assumes "x > 0" and "1/x - x = 1"
  shows "x = (-1 + sqrt 5)/2"

But need to derive this. Let's see:

Starting with 1/x - x =1. Multiply both sides by x: 1 - x² = x → x² + x -1 =0. Then solve using quadratic formula.

So, the solutions are [-1 ± sqrt(1 +4)]/2 = [-1 ± sqrt(5)]/2. Since x>0, only [-1 + sqrt(5)]/2 is positive.

Thus, the lemma would be:

lemma solve_1_over_x_minus_x_eq_1:
  fixes x :: real
  assumes "x > 0" and "1 / x - x = 1"
  shows "x = (sqrt 5 - 1)/2"

Then, using these two lemmas, we can get the values of a and b.

Then, sum them:

(1 + sqrt5)/2 + (sqrt5 -1)/2 = (2 sqrt5)/2 = sqrt5.

So, the sum is sqrt5.

Now, in the Isabelle proof, I can use these lemmas, apply them to a and b, then compute the sum.

But need to make sure that the problem's conditions are met. Since a and b are different, they must come from different cases.

Thus, in the proof:

Assume that a satisfies one case and b the other, then apply the respective lemmas, sum, and show the result.

But how to formalize that in Isabelle?

The theorem states that given a and b satisfy the absolute value condition and are different, their sum is sqrt5.

So, the proof can be structured as:

1. Split into cases for a and b. Since they are different, they must be from different equations.

2. For each case, apply the respective lemma to get their values.

3. Sum them and simplify.

Alternatively, since the absolute value condition allows both possibilities, but the problem says two different numbers, so one must be from each case.

Thus, the proof can be:

- Use the lemmas to get a and b as the two distinct roots, then sum them.

But how to handle the absolute value in the assumptions?

In Isabelle, the assumptions are that |a - 1/a| =1 and |b - 1/b|=1. So, for each of a and b, they satisfy either x - 1/x =1 or 1/x -x =1.

But since a ≠ b, they must be from different equations.

Therefore, in the proof, we can derive that one is (1 + sqrt5)/2 and the other is (sqrt5 -1)/2.

Thus, their sum is sqrt5.

So, the steps in the Isabelle proof would be:

- Use the lemmas to get the values of a and b based on their equations.
- Compute the sum and simplify.

Now, writing the actual Isabelle code with these lemmas.

First, the lemmas:

For solve_x_minus_1_over_x_eq_1, we can use the existing skill 2. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

For solve_1_over_x_minus_x_eq_1, I need to create a new lemma.

Then, in the theorem proof, apply these lemmas to a and b, then sum.

Also, need to ensure that the sum is correctly calculated.

Let me check the arithmetic:

(1 + sqrt5)/2 + (sqrt5 -1)/2 = [1 + sqrt5 + sqrt5 -1]/2 = 2*sqrt5 /2 = sqrt5.

Yes.

So, the code would be structured with the two lemmas, then applying them to a and b, then summing.

Also, need to handle the cases where a and b satisfy different equations.

But the problem states that both a and b satisfy |x - 1/x| =1, but since they are different, they must be from different cases.

Thus, in the proof, we can split into cases for a and b. However, since the problem says a and b are different, but the absolute value equation can have two solutions, we can assume that one is from the first case and the other from the second.

Thus, the code can be:

proof -
  have a_case: "a - 1/a = 1 ∨ 1/a - a = 1" 
    using abs_eq_iff by (simp add: h2)
  have b_case: "b - 1/b = 1 ∨ 1/b - b = 1" 
    using abs_eq_iff by (simp add: h3)

  (* Since a ≠ b, they must be from different cases *)
  (* Assume a satisfies one case and b the other *)
  (* Apply the respective lemmas *)
  (* Then sum them *)

But how to formalize that in Isabelle without splitting into cases? Maybe use the lemmas to get the possible values and then show that their sum is sqrt5 regardless of which case they are in.

Alternatively, since the problem states that a and b are different, but both satisfy the absolute value condition, the only way for them to be different is if one is from the first equation and the other from the second. Therefore, their sum is the sum of the two roots.

So, the proof can proceed by using the two lemmas to get the values of a and b, then sum them.

Thus, in the Isabelle code:

- Use the two lemmas to get the values of a and b.
- Sum them and simplify.

But how to apply the lemmas? Since the problem states that a and b satisfy the absolute value condition, but not which equation they satisfy, we need to consider both possibilities.

But since they are different, they must be from different equations.

So, the code would be:

from h2 have a_eq: "a - 1/a = 1 ∨ 1/a - a = 1" 
  by (simp add: abs_eq_iff)

Similarly for b.

Then, using case analysis on a and b.

But in Isabelle, case analysis can be done with if-then-else or by using cases.

Alternatively, since the problem states that a and b are different, and the only possible solutions are the two roots, then their sum is the sum of the two roots.

Thus, regardless of which one is a and which is b, the sum is sqrt5.

Therefore, the code can proceed as:

have a_val: "a = (1 + sqrt5)/2 ∨ a = (sqrt5 - 1)/2" 
  using solve_x_minus_1_over_x_eq_1 and solve_1_over_x_minus_x_eq_1 and h0 and h2. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Similarly for b.

But how to express that? Maybe using the lemmas and the fact that a and b are different.

Alternatively, since the two possible solutions are the two roots, and since a and b are different, they must be the two roots, so their sum is sqrt5.

But how to formalize that in Isabelle?

Maybe:

Let me consider that the set of solutions to |x - 1/x| =1 is { (1 + sqrt5)/2, (sqrt5 -1)/2 }.

Since a and b are different and in this set, their sum is sqrt5.

Thus, the code can be:

have "a ∈ { (1 + sqrt5)/2, (sqrt5 -1)/2 }" 
  using solve_x_minus_1_over_x_eq_1 and solve_1_over_x_minus_x_eq_1 and h0 and h2. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Similarly for b.

Then, since a ≠ b, the set {a, b} is exactly the two roots, so their sum is sqrt5.

But how to express that in Isabelle?

Alternatively, use the fact that the sum of the roots of the quadratic equations is given by Vieta's formula.

The first equation x² -x -1 =0 has roots with sum 1.

The second equation x² +x -1 =0 has roots with sum -1.

But wait, that's not helpful. Wait, the two roots from the two different equations are (1 + sqrt5)/2 and (sqrt5 -1)/2. Their sum is sqrt5.

But perhaps using Vieta's formula for the product of the two roots?

Alternatively, since the two equations are x² -x -1 =0 and x² +x -1 =0, but the roots are from different equations.

But maybe not. Let me think.

Alternatively, the two solutions are from the two different equations. Their sum is the sum of the two positive roots of x² -x -1 =0 and x² +x -1 =0.

But the first equation's positive root is (1 + sqrt5)/2, and the second equation's positive root is (-1 + sqrt5)/2.

Adding them gives sqrt5.

Thus, the code can directly compute that sum.

But how to derive that in Isabelle?

In the proof, once we have the two lemmas, we can state that a is one root and b is the other, then sum them.

So, the code would be:

from h2 have a_case: "a - 1/a = 1 ∨ 1/a - a = 1" 
  by (simp add: abs_eq_iff)

Similarly for b.

Then, using the two lemmas, we can derive that a is either (1 + sqrt5)/2 or (sqrt5 -1)/2, and similarly for b.

But since a ≠ b, they must be different. Hence, their sum is the sum of the two roots.

But how to handle this in Isabelle.

Perhaps, use the two lemmas to get the possible values of a and b, then compute the sum.

But since the problem states that a and b are different, we can assume that one is from the first case and the other from the second.

Thus, in the code:

have a_val: "a = (1 + sqrt5)/2 ∨ a = (sqrt5 -1)/2" 
  using solve_x_minus_1_over_x_eq_1 and solve_1_over_x_minus_x_eq_1 and h0 and h2. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Similarly for b_val.

Then, since a ≠ b, their sum is the sum of the two roots.

But how to express this in Isabelle.

Alternatively, consider that the set of solutions is { (1 + sqrt5)/2, (sqrt5 -1)/2 }, and since a and b are different, they are the two elements of the set. Therefore, their sum is the sum of the elements.

Thus, the code can be:

have "a + b = (1 + sqrt5)/2 + (sqrt5 -1)/2" 
  by (simp add: ...)

But how to justify that.

Alternatively, since the problem states that a and b are different and satisfy the equations, and the only possible solutions are the two roots, their sum is sqrt5.

But to formalize this, perhaps using the fact that the sum of the roots of the two equations is sqrt5.

But I need to write the code with these steps.

Putting it all together, the Isabelle code would include the two lemmas, then in the theorem proof, use them to get the values of a and b and sum them.
</think>

```isabelle
theory amc12a_2002_p13
  imports Complex_Main
begin

(* Lemma for solving x - 1/x = 1 *)
lemma solve_x_minus_1_over_x_eq_1: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x > 0" and "x - 1 / x = 1"
  shows "x = (1 + sqrt 5)/2"
proof -
  from assms(2) have "x^2 - x - 1 = 0" by sos
  then have "x^2 - x + 1/4 = 1 + 1/4" by auto
  then have "(x - 1/2)^2 = 5/4" by sos
  then have "x - 1/2 = sqrt(5)/2 ∨ x - 1/2 = -sqrt(5)/2" 
    by (smt (verit) assms(1) assms(2) diff_ge_0_iff_ge divide_le_0_1_iff eq_iff_diff_eq_0 le_divide_eq_1_pos numeral_One real_sqrt_divide real_sqrt_four real_sqrt_ge_one real_sqrt_gt_1_iff real_sqrt_one real_sqrt_unique verit_comp_simplify1(3))
  then have "x = (1 + sqrt 5)/2 ∨ x = (1 - sqrt 5)/2" 
    by (auto simp add: field_simps)
  moreover
  have "(1 - sqrt 5)/2 < 0" by auto
  ultimately show ?thesis using assms(1) by (fastforce)
qed

(* Lemma for solving 1/x - x = 1 *)
lemma solve_1_over_x_minus_x_eq_1:
  fixes x :: real
  assumes "x > 0" and "1 / x - x = 1"
  shows "x = (sqrt 5 - 1)/2"
proof -
  from assms(2) have "x^2 + x - 1 = 0" by (sos)
  then have "x^2 + x + 1/4 = 1 + 1/4" by auto
  then have "(x + 1/2)^2 = 5/4" by sos
  then have "x + 1/2 = sqrt(5)/2 ∨ x + 1/2 = -sqrt(5)/2" 
    by (smt (verit) assms(1) assms(2) diff_ge_0_iff_ge divide_le_0_1_iff eq_iff_diff_eq_0 le_divide_eq_1_pos numeral_One real_sqrt_divide real_sqrt_four real_sqrt_ge_one real_sqrt_gt_1_iff real_sqrt_one real_sqrt_unique verit_comp_simplify1(3))
  then have "x = (sqrt 5 - 1)/2 ∨ x = (-sqrt 5 - 1)/2" 
    by (auto simp add: field_simps)
  moreover
  have "(-sqrt 5 - 1)/2 < 0" by auto
  ultimately show ?thesis using assms(1) by (fastforce)
qed

(* Formal statement *)
theorem amc12a_2002_p13:
  fixes a b :: real
  assumes h0: "0 < a \<and> 0 < b"
      and h1: "a \<noteq> b"
      and h2: "abs (a - 1/a) = 1"
      and h3: "abs (b - 1/b) = 1" 
    shows "a + b = sqrt 5"
proof -
  (* Case analysis for a and b *)
  from h2 have a_case: "a - 1/a = 1 ∨ 1/a - a = 1" 
    by (simp add: abs_eq_iff)
  from h3 have b_case: "b - 1/b = 1 ∨ 1/b - b = 1" 
    by (simp add: abs_eq_iff)

  (* Since a ≠ b, they must satisfy different cases *)
  (* Apply respective lemmas to a and b *)
  have a_val: "a = (1 + sqrt 5)/2 ∨ a = (sqrt 5 - 1)/2" 
    by (metis a_case h0 solve_x_minus_1_over_x_eq_1 solve_1_over_x_minus_x_eq_1) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have b_val: "b = (1 + sqrt 5)/2 ∨ b = (sqrt 5 - 1)/2" 
    by (metis b_case h0 solve_x_minus_1_over_x_eq_1 solve_1_over_x_minus_x_eq_1) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Since a ≠ b, they must be the two distinct roots *)
  (* Compute their sum *)
  have "a + b = (1 + sqrt 5)/2 + (sqrt 5 - 1)/2" 
    by (metis a_val b_val h1)
  also have "... = (1 + sqrt 5 + sqrt 5 - 1)/2" 
    by (simp add: field_simps)
  also have "... = (2 * sqrt 5)/2" 
    by (simp add: field_simps)
  also have "... = sqrt 5" 
    by (simp add: field_simps)
  finally show ?thesis by simp
qed

end
```
