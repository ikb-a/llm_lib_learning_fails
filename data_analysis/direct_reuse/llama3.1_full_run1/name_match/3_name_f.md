# f, f_x

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 3

Lemma:
```isabelle
fun f :: "real \<Rightarrow> real" where
  "f x = 5 * x + 4"

lemma f_x:
  fixes x :: real
  shows "5 * x + 4 = f x"
proof -
  have "f x = 5 * x + 4" by auto
  then show ?thesis by simp
qed
```


## Usage 1 of 3:
### Problem:
Task name: `mathd_algebra_143.json`

If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? Show that it is 8.
### Informal Proof:
We are asked to apply the function $f$ to the number $g(2)$.  First, we need to find $g(2)$.  We substitute $x=2$ into the expression given for $g$ to find that $g(2)=2^2+3=7$.  Then we substitute $x=7$ into the expression for $f$ to find $f(7)=7+1=8$.
### Solution:
```isabelle
theorem mathd_algebra_143:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<forall> x. f x = x + 1"
    and "\<forall> x. g x = x^2 + 3" 
  shows "f (g 2) = 8"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_143
imports Complex_Main 
begin

(* Define f and g as functions from real numbers to real numbers *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
fun f :: "real \<Rightarrow> real" where %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  "f x = x + 1" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fun g :: "real \<Rightarrow> real" where %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  "g x = x^2 + 3"

(* formal statement copy from the input *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
theorem mathd_algebra_143:
  fixes f g :: "real \<Rightarrow> real" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  assumes "\<forall> x. f x = x + 1" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    and "\<forall> x. g x = x^2 + 3"  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  shows "f (g 2) = 8" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
proof - %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 1: Evaluate g(2) by substituting x=2 into the expression for g(x). *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "g 2 = 2^2 + 3" by simp
  (* &\equiv 7 *)
  hence c0: "g 2 = 7" by auto

  (* Step 3: Evaluate f(g(2)) by substituting x=g(2)=7 into the expression for f(x). *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "f (g 2) = f 7" using c0 by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* &\equiv 8 *)
  hence "f (g 2) = 8" using assms(1) by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Conclude f(g(2)) = 8. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then show ?thesis by auto
qed

end
```


## Usage 2 of 3:
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


## Usage 3 of 3:
### Problem:
Task name: `mathd_algebra_412.json`

The sum of two numbers is 25 and their difference is 11. What is the larger of the two numbers? Show that it is 18.
### Informal Proof:
Let $x,y$ be the two numbers, $x>y$. Then $x+y=25$ and $x-y=11$, thus:  $x=\frac{1}{2}\left((x+y)+(x-y)\right)=\frac{1}{2}(25+11)=18$.
### Solution:
```isabelle
theorem mathd_algebra_412:
  fixes x y :: real
    assumes "x + y = 25"
      and "x - y = 11" 
    shows "x = 18"
```
AI Generated completion (lemma lines higlighted):
## Proof %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```isabelle
theory mathd_algebra_412
  imports Complex_Main
begin

(* formal statement copied from the input *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
theorem mathd_algebra_412:
  fixes x y :: real %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  assumes "x + y = 25"
    and "x - y = 11"
  shows "x = 18"
proof - %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  (* Step 1: Express the given information as equations: *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "x + y = 25" and "x - y = 11" using assms by auto

  (* Step 2: Add the two equations together to eliminate y and find the value of x. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "2*x = 25 + 11" by (smt add_diff_cancel_left') %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "2*x = 36" by (simp add: add_pos_pos)

  (* Step 3: Simplify the equation to find that x = (1/2)(25 + 11). *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then have "x = 18" by (simp add: divide_pos_pos)

  (* Step 4: Calculate the value of x to conclude the proof. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then show ?thesis by simp
qed
end
```
