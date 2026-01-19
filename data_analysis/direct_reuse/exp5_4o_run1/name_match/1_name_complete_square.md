# complete_square

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma complete_square:
  fixes a b c :: real
  shows "a^2 - 2*a*b + b^2 = (a - b)^2"
proof -
  have "(a - b)^2 = a^2 - 2*a*b + b^2"
    by (simp add: power2_eq_square algebra_simps)
  thus ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_113.json`

What value of $x$ will give the minimum value for $x^2- 14x + 3$? Show that it is 7.
### Informal Proof:
We start by completing the square: \begin{align*} x^2-14x+3&= x^2-14x +\left(\frac{14}{2}\right)^2 - \left(\frac{14}{2}\right)^2 + 3\\ & = x^2 -14x + 7^2 - 49 + 3\\ &=(x-7)^2 - 46.\end{align*}Since the square of a real number is at least 0, we have $$(x-7)^2\ge 0,$$where $(x-7)^2 =0$ only if $x=7$.   Therefore, $(x-7)^2 - 46$ is minimized when $x=7.$
### Solution:
```isabelle
theorem mathd_algebra_113:
  fixes x ::real
  shows "x^2 - 14 * x + 3 \<ge> 7^2 - 14 * 7 + 3"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_113
  imports Complex_Main
begin

(* lemma 1: Completing the square transformation for a quadratic expression *)
lemma complete_square_transformation: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: real
  shows "a^2 - 2*a*b + b^2 + c = (a - b)^2 + c"
proof -
  have "(a - b)^2 = a^2 - 2*a*b + b^2" 
    by (simp add: power2_eq_square algebra_simps)
  thus ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_113:
  fixes x ::real
  shows "x^2 - 14 * x + 3 \<ge> 7^2 - 14 * 7 + 3"
proof -
  (* Step 1: Complete the square for the quadratic expression x^2 - 14x + 3 *)
  have "x^2 - 14*x + 3 = (x - 7)^2 - 46"
  proof -
    have "(x^2 - 14*x + 3) = (x^2 - 14*x + 49) - 49 + 3"
      by algebra
    also have "... = (x - 7)^2 - 46"
      using complete_square_transformation[of x 7 "3 - 49"] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    finally show ?thesis by simp
  qed

  (* Step 2: Identify the minimum value of the squared term (x - 7)^2 *)
  have "(x - 7)^2 \<ge> 0" by simp

  (* Step 3: Determine the minimum value of the original expression *)
  hence "(x - 7)^2 - 46 \<ge> 0 - 46" by simp

  (* Step 4: Conclude the proof *)
  thus ?thesis using `x^2 - 14*x + 3 = (x - 7)^2 - 46` by simp
qed

end
```

This Isabelle proof shows that the quadratic expression \(x^2 - 14x + 3\) has a minimum value when \(x = 7\), achieved by completing the square and observing that the squared term is non-negative.
