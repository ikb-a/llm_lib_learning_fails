# solve_two_variable_system

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_two_variable_system:
  fixes a b c d x y :: real
  assumes "x = a + b * y"
    and "y = c + d * x"
    and "1 - b * d \<noteq> 0"
  shows "x = (a + b * c) / (1 - b * d) \<and> y = (c + d * (a + b * c) / (1 - b * d))"
proof -
  from assms(1) have "x = a + b * (c + d * x)" by (simp add: assms(2))
  also have "... = a + b * c + b * d * x" by (simp add: algebra_simps)
  finally have "x = a + b * c + b * d * x" .
  then have "x - b * d * x = a + b * c" by (simp add: algebra_simps)
  then have "x * (1 - b * d) = a + b * c" by (simp add: algebra_simps)
  with assms(3) have "x = (a + b * c) / (1 - b * d)" by (auto simp: field_simps)
  moreover from assms(2) have "y = c + d * (a + b * c) / (1 - b * d)" by (simp add: \<open>x = (a + b * c) / (1 - b * d)\<close>)
  ultimately show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_388.json`

If  \begin{align*} 3x+4y-12z&=10,\\ -2x-3y+9z&=-4, \end{align*}  compute $x$. Show that it is 14.
### Informal Proof:
Let $w=y-3z$.  The equations become  \begin{align*} 3x+4w&=10,\\ -2x-3w&=-4. \end{align*}  Adding four times the second equation to three times the first equation,  $$9x+12w-8x-12w=30-16\Rightarrow x=14.$$
### Solution:
```isabelle
theorem mathd_algebra_388:
  fixes x y z :: real
  assumes "3 * x + 4 * y - 12 * z = 10"
      and "-2 * x - 3 * y + 9 * z = -4"
    shows "x = 14"
```
AI Generated completion (lemma lines higlighted):
<think>
Okay, let's tackle this problem. So, the user wants to prove that x equals 14 given those two equations. The informal proof suggests using substitution with w = y - 3z. Let me think about how to translate that into Isabelle.

First, I need to define the substitution. Let's set w = y - 3z. Then, I should express the original equations in terms of w. Let's see:

The first equation is 3x +4y -12z =10. If I substitute y = w +3z into that, then:

3x +4(w +3z) -12z = 3x +4w +12z -12z = 3x +4w =10. That simplifies the first equation to 3x +4w =10. Good.

The second equation is -2x -3y +9z =-4. Substitute y again: -2x -3(w +3z) +9z = -2x -3w -9z +9z = -2x -3w =-4. So that gives -2x -3w =-4. 

Now, the system becomes two equations with x and w. The next step in the informal proof is to eliminate w by multiplying the first equation by 3 and the second by 4, then adding. Let's check that.

Multiplying first equation by 3: 9x +12w =30. Multiplying second equation by 4: -8x -12w = -16. Adding these two equations: (9x -8x) + (12w -12w) = 30 -16 → x =14. That's correct.

So, the plan is to first express the original equations in terms of w, then solve the resulting system. 

In Isabelle, I need to define w as y -3z. Then, substitute into the equations. Let me think about the steps. 

I can start by using the given assumptions. Let's take the first equation and substitute y with w +3z. Similarly for the second equation. Then, derive the simplified equations. Then, solve for x by eliminating w.

But how to structure the proof in Isabelle? Maybe using some lemmas to express the substitution. Let me see.

First, define w as y -3z. Then, from the original equations, substitute y = w +3z. Then, derive the two new equations. Then, solve those two equations for x and w.

Alternatively, since the problem is about solving a system of equations, maybe using the solve_linear_system lemma from the previous examples. Wait, but that lemma was for a specific case. Let me check.

The solve_linear_system lemma takes two equations of the form x = a -b y and y = c x +d. But here, the equations are in x and w. Let me see:

After substitution, the two equations are 3x +4w =10 and -2x -3w =-4. Let me rearrange them as:

Equation 1: 3x +4w =10 → x = (10 -4w)/3.

Equation 2: -2x -3w =-4 → -2x = -4 +3w → x = (4 -3w)/2.

So, substituting x from equation 1 into equation 2:

(10 -4w)/3 = (4 -3w)/2. Cross multiplying: 2*(10 -4w) = 3*(4 -3w) → 20 -8w =12 -9w → 20 -12 = -9w +8w → 8 = -w → w = -8.

Wait, but according to the informal proof, the method was to eliminate w by multiplying and adding. Maybe that's a more straightforward approach in Isabelle.

Alternatively, using the solve_two_variable_system lemma. Let me check the parameters. The lemma solve_two_variable_system requires equations of the form x = a +b y and y = c +d x. But here, the equations are in x and w, with coefficients. So maybe using the solve_linear_system lemma. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

But perhaps it's easier to proceed by multiplying the equations and adding. Let's try to formalize that.

So, after getting the two equations:

3x +4w =10 and -2x -3w =-4.

Multiply first by 3: 9x +12w =30.

Multiply second by 4: -8x -12w =-16.

Adding them: (9x -8x) + (12w -12w) =30 -16 → x =14.

This is straightforward. So in Isabelle, I can use the equation_addition lemma (from the useful skills) to add the two equations after scaling.

But the equation_addition lemma adds two equations. However, here I need to multiply each equation by a scalar and then add. So maybe I need to first multiply each equation by the respective scalars, then add.

So, first, take the first equation 3x +4w =10 and multiply by 3: 9x +12w =30.

Then take the second equation -2x -3w =-4 and multiply by 4: -8x -12w =-16.

Then add these two equations: 9x -8x +12w -12w =30 -16 → x=14.

So, in Isabelle, I need to derive these scaled equations and then add them.

Alternatively, use the solve_linear_system lemma. Let me check the parameters. The lemma requires equations of the form x = a -b y and y = c x +d. But here, the equations are linear in x and w, but not in that form. However, perhaps I can rearrange them.

Equation 1: 3x +4w =10 → 3x =10 -4w → x = (10 -4w)/3.

Equation 2: -2x -3w =-4 → -2x = -4 +3w → x = (4 -3w)/2.

So, substituting into the solve_two_variable_system lemma. Let me see: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The lemma solve_two_variable_system takes x = a +b y and y = c +d x. Here, if I consider x as the variable and w as y. So: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

x = (10 -4w)/3 → which can be written as x = (10/3) - (4/3)w. So a =10/3, b = -4/3.

Then, equation 2 is x = (4 -3w)/2 → x = 2 - (3/2)w. Wait, but this is a different equation for x. However, the solve_two_variable_system lemma is for a system where x is expressed in terms of y and y in terms of x. But here, both equations express x in terms of w. That's not the same structure. So maybe that lemma isn't directly applicable here. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Alternatively, perhaps using the solve_linear_system lemma. Let me check. The solve_linear_system lemma is for equations x = a -b y and y =c x +d. But here, the equations are 3x +4w =10 and -2x -3w =-4. Let me rearrange them to fit that structure.

Let me consider the first equation as 3x =10 -4w → x = (10 -4w)/3. Then, the second equation can be rearranged as -2x = -4 +3w → x = (4 -3w)/2. So, if I have two expressions for x in terms of w, I can set them equal. But that would be another approach.

So, equate (10 -4w)/3 = (4 -3w)/2. Cross-multiplying gives 2(10 -4w) =3(4 -3w) → 20 -8w =12 -9w → 8 = -w → w = -8. Then substitute back into one of the equations to find x. But this approach may be more involved in Isabelle.

Alternatively, using the equation_addition lemma. Let me try that.

First, from the original equations, after substitution, we have:

Equation A: 3x +4w =10.

Equation B: -2x -3w =-4.

Multiply equation A by 3: 9x +12w =30.

Multiply equation B by 4: -8x -12w =-16.

Now, add these two equations: 9x -8x +12w -12w =30 -16 → x =14.

So, in Isabelle, I can use the equation_addition lemma twice. First, to multiply equation A by 3, then multiply equation B by 4, then add the two results.

But how to handle the multiplication of equations by scalars? The equation_addition lemma adds two equations, but here I need to scale them first.

Alternatively, use the fact that if a * x + b * y = c, then multiplying both sides by a scalar d gives d*a*x +d*b*y =d*c. So, for equation A, multiply by 3: 3*(3x +4w) =3*10 →9x +12w=30. Similarly for equation B multiplied by 4: 4*(-2x -3w) =4*(-4) →-8x -12w =-16.

Then, adding these two equations: 9x +12w -8x -12w =30 -16 → x=14.

So, in Isabelle, I can use the lemma that allows multiplying both sides of an equation by a scalar. Then, use equation_addition to add the two equations.

But how to formalize this. Let me think. The original equations are:

1. 3x +4w =10.

2. -2x -3w =-4.

Multiply the first by 3: 3*(3x +4w) =3*10 →9x +12w=30.

Multiply the second by 4:4*(-2x -3w) =4*(-4) →-8x -12w =-16.

Then, add these two equations:

(9x +12w) + (-8x -12w) =30 + (-16) → x =14.

So, in Isabelle, I can use the equation_addition lemma, but I need to have the two equations in the form a*x +b*y =c and d*x +e*y =f. Then, adding them gives (a+d)x + (b+e)y =c +f.

But here, after scaling, the equations are:

Equation A': 9x +12w =30.

Equation B': -8x -12w =-16.

Adding them gives (9x -8x) + (12w -12w) =30 -16 → x =14.

So, in Isabelle, I can use the equation_addition lemma on these two equations. The lemma requires that the equations are in the form a*x +b*y =c and d*x +e*y =f. So, in this case, the variables are x and w. So, for equation A', a=9, b=12, c=30. For equation B', d=-8, e=-12, f=-16. Then, adding them gives (9 + (-8))x + (12 + (-12))w =30 + (-16) →1x +0w =14 →x=14.

Therefore, the steps in Isabelle would be:

- Use the given equations to derive the scaled equations.

- Apply equation_addition on the two scaled equations to get x=14.

But how to derive the scaled equations? For that, I need to use the fact that if an equation holds, multiplying both sides by a scalar gives another equation. For example, from the first equation 3x +4w =10, multiplying both sides by 3 gives 9x +12w =30. Similarly for the second equation.

So, I can use the lemma that for any real numbers a, b, c, if a = b, then c*a = c*b. This is a standard algebraic property.

Alternatively, use the simplification rules. For example, in Isabelle, if you have an equation, you can multiply both sides by a scalar.

So, in the proof, I can first derive the two scaled equations, then apply equation_addition.

Putting it all together:

First, define w = y -3z. Then, substitute into the original equations to get equations in x and w. Then, scale and add them.

But how to handle the substitution. The original equations are given as assumptions. So, let me start by defining w as y -3z. Then, substitute into the original equations.

But the problem is that the original equations are in terms of y and z. So, substituting y = w +3z into them. So, the first equation becomes 3x +4(w +3z) -12z =10 →3x +4w +12z -12z =10 →3x +4w=10.

Similarly, the second equation becomes -2x -3(w +3z) +9z =-4 →-2x -3w -9z +9z =-4 →-2x -3w =-4.

So, these are the two equations in x and w.

Once we have these, then proceed as before.

So, in the proof, first, define w as y -3z. Then, substitute into the original equations to get the two equations in x and w. Then, scale and add them.

But how to express the substitution in Isabelle. Let's think:

From the original equations, we can derive:

From the first equation: 3x +4y -12z =10. But y =w +3z. So, substituting gives 3x +4(w +3z) -12z =10. Simplify that to 3x +4w +12z -12z =10 →3x +4w =10.

Similarly for the second equation.

So, in Isabelle, using the given assumptions, and the definition of w, we can derive these two equations.

So, the steps would be:

1. Define w as y -3z.

2. Use the original equations to derive the two equations in x and w.

3. Multiply each equation by scalars and add them.

But how to do this in Isabelle. Let's try to outline the proof steps:

Proof:

Assume the original equations. Define w = y -3z. Then, substitute into the equations.

First equation:

3x +4y -12z =10.

But y = w +3z. Substitute:

3x +4(w +3z) -12z =10.

Simplify: 3x +4w +12z -12z =10 →3x +4w =10.

Similarly for the second equation.

Once we have these two equations, proceed to multiply and add.

So, in Isabelle, I can use the given assumptions and the definition of w to derive the equations in x and w.

Then, apply the equation_addition lemma on the scaled equations.

Now, the problem is to formalize these steps.

Let me think about the code structure. The theorem is given, and the proof needs to be written in Isabelle.

So, in the proof:

First, define w as y -3z. Then, derive the two equations.

But how to handle the substitution. Since the original equations are given as assumptions, I can use them to derive the new equations.

For example:

From the first assumption: 3x +4y -12z =10.

But since w = y -3z, we can express y as w +3z. Substitute that into the equation:

3x +4*(w +3z) -12z = 10.

Simplify: 3x +4w +12z -12z =3x +4w =10.

So, in Isabelle, this would be:

have "3 * x + 4 * y - 12 * z = 10" using assms(1).

then, since w = y -3z, we have y = w +3z. So:

have "3 * x + 4 * (w + 3 * z) - 12 * z = 10" by (simp add: y_def)

then simplify:

have "3 * x + 4 * w + 12 * z - 12 * z = 10" by (simp add: algebra_simps)

then:

have "3 * x + 4 * w = 10" by (simp add: algebra_simps)

Similarly for the second equation.

Once we have these two equations, proceed to scale and add.

So, for the first equation, multiply by 3:

have "9 * x + 12 * w = 30" by (simp add: mult_eq_1_left[OF "3x +4w =10", of 3])

Wait, but how to handle the multiplication. Maybe using the fact that if a = b, then c*a = c*b. So, for example:

From "3x +4w =10", multiply both sides by 3:

have "3 * (3x +4w) = 3 * 10" by (simp add: mult_left_mono)

Then, simplify:

have "9x +12w =30" by (simp add: algebra_simps)

Similarly for the second equation.

Once we have these two scaled equations, we can apply the equation_addition lemma. Let's check the equation_addition lemma again. It takes two equations of the form a*x +b*y =c and d*x +e*y =f, and adds them to get (a+d)x + (b+e)y =c +f.

In our case, after scaling, the two equations are:

Equation A': 9x +12w =30

Equation B': -8x -12w =-16

So, applying equation_addition on these two equations gives:

(9 + (-8))x + (12 + (-12))w =30 + (-16)

Which simplifies to 1x +0w =14 →x=14.

Thus, the final step is to show that x=14.

So, putting it all together in Isabelle code:

First, define w = y -3z.

Then, derive the two equations in x and w.

Then, scale each equation by 3 and 4 respectively.

Then, apply equation_addition to get x=14.

So, the code would look something like:

proof -
  define w where "w = y - 3*z"
  have eq1: "3 * x + 4 * w = 10"
    by (simp add: assms(1) w_def)
  have eq2: "-2 * x - 3 * w = -4"
    by (simp add: assms(2) w_def)
  have scaled_eq1: "9 * x + 12 * w = 30"
    by (simp add: eq1 mult_left_mono)
  have scaled_eq2: "-8 * x - 12 * w = -16"
    by (simp add: eq2 mult_left_mono)
  have "9 * x + 12 * w + (-8 * x) + (-12 * w) = 30 + (-16)"
    by (rule equation_addition[OF scaled_eq1 scaled_eq2])
  also have "... = (9x -8x) + (12w -12w)" by (simp add: algebra_simps)
  also have "... = x + 0" by (simp add: algebra_simps)
  finally have "x = 14" by (simp add: 14)
  then show ?thesis by simp
qed

Wait, but the equation_addition lemma in the previous examples was called as:

have "..." using assms by simp.

But in the current case, after scaling, the equations are:

scaled_eq1: 9x +12w =30

scaled_eq2: -8x -12w =-16

Then, applying equation_addition on these two equations gives (9-8)x + (12-12)w =30 -16 →x=14.

But in the code, the equation_addition lemma is used on the two equations. The lemma's code is:

lemma equation_addition:
  fixes a b c d :: real
  assumes "a * x + b * y = c" and "d * x + e * y = f"
  shows "(a + d) * x + (b + e) * y = c + f"

So, in this case, a=9, b=12, c=30; d=-8, e=-12, f=-16. Then, the conclusion is (9-8)x + (12-12)w =30-16 →1x +0w =14 →x=14.

So, in the code, after deriving scaled_eq1 and scaled_eq2, we can use equation_addition on them, which would give the desired result.

Therefore, the code would be:

proof -
  define w where "w = y - 3*z"
  have eq1: "3 * x + 4 * w = 10" 
    by (simp add: assms(1) w_def)
  have eq2: "-2 * x - 3 * w = -4" 
    by (simp add: assms(2) w_def)
  have scaled_eq1: "9 * x + 12 * w = 30" 
    by (simp add: eq1 mult_left_mono)
  have scaled_eq2: "-8 * x - 12 * w = -16" 
    by (simp add: eq2 mult_left_mono)
  have " (9 * x + 12 * w) + (-8 * x - 12 * w) = 30 + (-16)" 
    by (rule equation_addition[OF scaled_eq1 scaled_eq2])
  also have "... = (9x -8x) + (12w -12w)" by (simp add: algebra_simps)
  also have "... = x + 0" by (simp add: algebra_simps)
  finally have "x = 14" by (simp add: 14)
  then show ?thesis by simp
qed

But wait, the final step "x =14" needs to be derived from "x +0 =14". So, the line "x +0 =14" implies x=14.

So, in Isabelle, that would be:

from "x +0 =14" have "x =14" by (simp add: add_left_cancel)

But how to write that. Alternatively, using the fact that adding zero doesn't change the value.

So, the code would have:

have "x + 0 = 14" by (simp add: algebra_simps)
then have "x =14" by (simp add: add_zero)

Alternatively, since "x +0 = x", then "x =14".

So, in code:

have "x + 0 = 14" by (simp add: algebra_simps)
then have "x =14" by (simp add: add_0)

But in Isabelle, the add_0 lemma is "a + 0 = a" for any a. So, from x +0 =14, we can derive x =14 by using the add_0 lemma.

Alternatively, using the symmetric property of equality. Since x +0 =14, and x +0 =x, then x=14.

So, in code:

have "x =14" by (metis add_0_right add_0_left)
Wait, maybe using the rule:

from "x +0 =14" have "x =14" by (simp add: add_0_left)

But in Isabelle, the add_0_left lemma is "0 + a = a", but here it's a +0. So, the lemma add_0_right is "a +0 =a".

So, in this case, "x +0 =14" implies x=14 because x +0 =x, so x=14.

So, the code would be:

have "x + 0 = 14" by (simp add: algebra_simps)
then have "x = 14" by (simp add: add_0_right)

Putting it all together, the proof would be structured as such.

But I need to make sure that all steps are correctly formalized and that the lemmas used are available. Also, the equation_addition lemma is from the previous examples, which the user has included in the imports.

So, the final Isabelle code would include the definition of w, the derivation of the equations, scaling them, and applying the equation_addition lemma to get the final result.
</think>

```isabelle
theory mathd_algebra_388
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

theorem mathd_algebra_388:
  fixes x y z :: real
  assumes "3 * x + 4 * y - 12 * z = 10"
      and "-2 * x - 3 * y + 9 * z = -4"
    shows "x = 14"
proof -
  (* Step 1: Define substitution $ w = y - 3z $ to eliminate $ y $ and $ z $ from the equations. *)
  define w where "w = y - 3 * z"

  (* Step 2: Substitute $ w $ into the original equations to derive the simplified system. *)
  (* First equation: 3x + 4w = 10 *)
  have "3 * x + 4 * w = 10"
    by (simp add: assms(1) w_def algebra_simps)

  (* Second equation: -2x - 3w = -4 *)
  have "-2 * x - 3 * w = -4"
    by (simp add: assms(2) w_def algebra_simps)

  (* Step 3: Eliminate $ w $ by multiplying the first equation by 3 and the second by 4, then adding them. *)
  (* Multiply first equation by 3: 9x + 12w = 30 *)
  have "9 * x + 12 * w = 30"
    by (simp add: mult_left_mono[OF `3 * x + 4 * w = 10`])

  (* Multiply second equation by 4: -8x - 12w = -16 *)
  have "-8 * x - 12 * w = -16"
    by (simp add: mult_left_mono[OF `-2 * x - 3 * w = -4`])

  (* Apply equation_addition to the scaled equations. *)
  have "9 * x + 12 * w + (-8 * x) + (-12 * w) = 30 + (-16)"
    by (rule equation_addition[OF `9 * x + 12 * w = 30` `-8 * x - 12 * w = -16`])

  (* Simplify the result to isolate $ x $. *)
  also have "... = (9 * x - 8 * x) + (12 * w - 12 * w)"
    by (simp add: algebra_simps)
  also have "... = x + 0" 
    by (simp add: algebra_simps)
  finally have "x + 0 = 14"
    by (simp add: add_0_right)

  (* Conclude that $ x = 14 $. *)
  then show ?thesis
    by (simp add: add_0_right)
qed

end
```
