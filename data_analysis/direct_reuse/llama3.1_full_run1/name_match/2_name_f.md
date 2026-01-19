# f, f_x

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 2

Lemma:
```isabelle
fun f :: "real \<Rightarrow> real" where
  "f x = 5 * x + 4"

lemma f_x:
  fixes x :: real
  shows "5 * x + 4 = f x"
proof -
  show ?thesis by auto
qed
```


## Usage 1 of 2:
### Problem:
Task name: `mathd_algebra_171.json`

Consider the function $f(x)=5x+4$.  What is $f(1)$? Show that it is 9.
### Informal Proof:
We have $f(1) = 5\cdot 1+4 =5+4=9$.
### Solution:
```isabelle
theorem mathd_algebra_171:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall>x. f x = 5 * x + 4" 
  shows "f 1 = 9"
```
AI Generated completion (lemma lines higlighted):
Here's the formal proof in Isabelle: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

```isabelle
theory mathd_algebra_171
  imports Complex_Main
begin

(* formal statement copy from the input *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
theorem mathd_algebra_171:
  fixes f :: "real \<Rightarrow> real" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  assumes "\<forall>x. f x = 5 * x + 4"  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  shows "f 1 = 9" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
proof - %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 1: Substitute x = 1 into the function f(x) = 5x + 4 *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "f 1 = 5 * 1 + 4" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    using assms by simp

  (* Step 2: Simplify the expression to get f(1) = 5 * 1 + 4 *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "... = 5 + 4"
    by simp

  (* Step 3: Perform the addition to get f(1) = 9 *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then show ?thesis
    by simp
qed
```

This proof follows the informal steps exactly, using Isabelle's syntax to express the mathematical reasoning. The `by simp` commands simplify the expressions according to the rules of simplification, and the `then` command is used to chain the simplifications together. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Note that this proof is very similar to the first example you provided, but with a different function and input value. The key difference is that we're using the `assumes` command to state the property of the function `f`, and then using that property to derive the value of `f 1`. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


## Usage 2 of 2:
### Problem:
Task name: `mathd_algebra_478.json`

The volume of a cone is given by the formula $V = \frac{1}{3}Bh$, where $B$ is the area of the base and $h$ is the height. The area of the base of a cone is 30 square units, and its height is 6.5 units. What is the number of cubic units in its volume? Show that it is 65.
### Informal Proof:
We are given that $B = 30$ and $h = 6.5$ and asked to find $\frac{1}{3}Bh$.  We find that \[\frac{1}{3}Bh = \frac{1}{3}(30)(6.5) = (10)(6.5) = 65.\]
### Solution:
```isabelle
theorem mathd_algebra_478:
  fixes b h v ::real
  assumes "0 < b \<and> 0 < h \<and> 0 < v"
      and "v = 1 / 3 * (b * h)"
      and "b = 30"
      and "h = 13 / 2"
    shows "v = 65"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_478
imports Complex_Main
begin

(* no helper function required in this theorem *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* formal statement copy from the input *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
theorem mathd_algebra_478:
  fixes b h v ::real %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  assumes "0 < b \<and> 0 < h \<and> 0 < v"
      and "v = 1 / 3 * (b * h)"
      and "b = 30"
      and "h = 13 / 2"
    shows "v = 65"
proof - %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 1: Given the formula for the volume of a cone, substitute the values of b and h into the formula. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "v = 1 / 3 * (b * h)"
    using assms(2) by auto
  then have "v = 1 / 3 * (30 * (13 / 2))"
    using assms(3, 4) by auto
  (* Step 2: Simplify the expression for v. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "v = 1 / 3 * (390 / 2)"
    by (simp add: mult.assoc)
  then have "v = 1 / 3 * 195"
    by (simp add: mult.assoc)
  (* Step 3: Evaluate the expression for v. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "v = 65"
    by (simp add: of_rat_divide of_rat_mult of_rat_numeral of_rat_numeral) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then show ?thesis
    by auto
qed

end
```

Please note that the above proof uses the `of_rat` function to convert the result from a fraction to a decimal. This is because Isabelle's `real` type is a more general type than the `real` type in mathematics, and it can represent both exact and inexact numbers. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
