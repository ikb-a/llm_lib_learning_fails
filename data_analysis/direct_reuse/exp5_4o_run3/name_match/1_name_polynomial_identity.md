# polynomial_identity

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma polynomial_identity:
  fixes x :: real
  shows "x^4 - 5*x^2 + 6 = (x^2 - 3)*(x^2 - 2)"
proof -
  have "(x^2 - 3)*(x^2 - 2) = x^4 - 2*x^2 - 3*x^2 + 6"
    by (simp add: algebra_simps)
  then show ?thesis
    by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_156.json`

The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? Show that it is 1.
### Informal Proof:
At the intersection points, the $y$-coordinates of the two graphs must be equal, so we have the equation $x^4=y=5x^2-6$, or $x^4=5x^2-6$. Putting all the terms on one side, we get $x^4-5x^2+6=0$. Factoring, we get $(x^2-3)(x^2-2)=0$, so $x^2-3=0 \Rightarrow x=\pm \sqrt{3}$ or $x^2-2=0 \Rightarrow x=\pm \sqrt{2}$. Thus, $m=3$ and $n=2$ and $m-n=1$.
### Solution:
```isabelle
theorem mathd_algebra_156:
  fixes x y :: real
    and f g :: "real \<Rightarrow> real"
  assumes "\<forall>t. f t = t^4"
  and "\<forall>t. g t = 5 * t^2 - 6"
  and "f x = g x"
  and "f y = g y"
  and "x^2 < y^2" 
  shows "y^2 - x^2 = 1"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_156
  imports Complex_Main
begin

(* Helper lemma 1: A lemma to factor the polynomial x^4 - 5x^2 + 6. *)
lemma polynomial_identity_1: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  shows "x^4 - 5*x^2 + 6 = (x^2 - 3)*(x^2 - 2)"
proof -
  (* Use the identity from the problem statement to factor the polynomial. *)
  have "(x^2 - 3)*(x^2 - 2) = x^4 - 2*x^2 - 3*x^2 + 6"
    by (simp add: algebra_simps)
  then show ?thesis
    by simp
qed

(* Formal statement copy from the input *)
theorem mathd_algebra_156:
  fixes x y :: real
    and f g :: "real \<Rightarrow> real"
  assumes "\<forall>t. f t = t^4"
  and "\<forall>t. g t = 5 * t^2 - 6"
  and "f x = g x"
  and "f y = g y"
  and "x^2 < y^2" 
  shows "y^2 - x^2 = 1"
proof -
  (* Step 1: Set the equations of the graphs equal to each other at the intersection points: x^4 = 5x^2 - 6. This gives us the equation x^4 - 5x^2 + 6 = 0. *)
  have "(x^4 - 5*x^2 + 6 = 0) \<and> (y^4 - 5*y^2 + 6 = 0)"
    using assms by auto

  (* Step 2: Factor the equation x^4 - 5x^2 + 6 = 0 using polynomial_identity_1. *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  hence "(x^2 - 3)*(x^2 - 2) = 0" and "(y^2 - 3)*(y^2 - 2) = 0"
    using polynomial_identity_1[of x] polynomial_identity_1[of y] by simp_all %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 3: Solve for x^2 and y^2 from the factors: u^2 - 5u + 6 = 0. *)
  hence "x^2 = 3 \<or> x^2 = 2" and "y^2 = 3 \<or> y^2 = 2"
    by auto

  (* Step 4: Identify m and n from the x-coordinates. Since m > n, we have m = 3 and n = 2. *)
  hence "x^2 = 2" and "y^2 = 3"
    using assms by auto

  (* Step 5: Calculate y^2 - x^2 = 3 - 2 = 1. *)
  hence "y^2 - x^2 = 3 - 2"
    by simp

  (* Step 6: Conclude that y^2 - x^2 = 1. *)
  thus ?thesis
    by simp
qed

end
```
