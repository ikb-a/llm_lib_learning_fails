# mathd_algebra_313

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_313:
  fixes v i z ::complex
  assumes "v = i * z"
    and "v = 1 + \<i>"
    and "z = c"
  shows "i = (1 + \<i>) / c"
proof -
  have "i * z = 1 + \<i>" using assms by simp
  then have "i * c = 1 + \<i>" by (metis assms(3))
  then have "i = (1 + \<i>) / c" by (metis \<open>i * z = 1 + \<i>\<close> add.commute add_eq_0_iff assms(3) complex_i_mult_minus complex_i_not_one div_by_1 eq_neg_iff_add_eq_0 frac_eq_eq mult_cancel_left2 mult_cancel_right2 zero_neq_one)
  then show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_313.json`

Complex numbers are often used when dealing with alternating current (AC) circuits. In the equation $V = IZ$, $V$ is voltage, $I$ is current, and $Z$ is a value known as impedance. If $V = 1+i$ and $Z=2-i$, find $I$. Show that it is \frac{1}{5} + \frac{3}{5}i.
### Informal Proof:
We have $$ I = \frac{V}{Z} = \frac{1+i}{2-i}. $$ Multiplying the numerator and denominator by the conjugate of the denominator, we get $$ I = \frac{1+i}{2-i} \cdot \frac{2+i}{2+i} = \frac{1(2) + 1(i) + i(2) + i(i)}{2(2) + 2(i) - i(2) - i(i)} = \frac{1+3i}{5} = \frac{1}{5} + \frac{3}{5}i. $$
### Solution:
```isabelle
theorem mathd_algebra_313:
  fixes v i z ::complex
  assumes "v = i * z"
    and "v = 1 + \<i>"
    and "z = 2 - \<i>" 
  shows "i = 1/5 + 3/5 * \<i>"
```
AI Generated completion (lemma lines higlighted):
Here's the formal proof in Isabelle for the problem:

```isabelle
theory mathd_algebra_313 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_313: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes v i z :: complex
  assumes "v = i * z"
    and "v = 1 + \<i>"
    and "z = 2 - \<i>" 
  shows "i = 1/5 + 3/5 * \<i>"
proof -
  (* Step 1: Divide $V$ by $Z$. So, $I = \frac{V}{Z} = \frac{1+i}{2-i}$. *)
  have "i * z = 1 + \<i>" using assms by simp
  then have "i * (2 - \<i>) = 1 + \<i>" by (metis assms(3))
  then have "i = (1 + \<i>) / (2 - \<i>)" by (metis assms(3) complex_i_not_one div_by_1 mult_cancel_left2 mult_cancel_right2 zero_neq_one)

  (* Step 2: Multiply the numerator and denominator by the conjugate of the denominator. The conjugate of $2-i$ is $2+i$. *)
  also have "... = (1 + \<i>) / (2 - \<i>) * (2 + \<i>) / (2 + \<i>)" by eval

  (* Step 3: Simplify the numerator and denominator. *)
  also have "... = (2 + \<i> + 2 * \<i> + \<i>^2) / (4 + 1)" by (simp add: algebra_simps)
  also have "... = (2 + 3 * \<i> - 1) / 5" by (simp add: power2_eq_square algebra_simps)

  (* Step 4: Simplify the numerator and denominator. *)
  also have "... = 1/5 + 3/5 * \<i>" by (simp add: algebra_simps)
  finally show ?thesis by simp
qed

end
```

This proof follows the steps outlined in the informal proof, using the properties of complex numbers and algebraic manipulations to simplify the expression and arrive at the final result.
