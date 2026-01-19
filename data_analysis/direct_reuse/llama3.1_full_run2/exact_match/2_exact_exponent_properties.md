# exponent_properties, exponent_simplification

Tasks where a provided skill is reproduced verbatim

Frequency: 2

Lemma:
```isabelle
lemma exponent_properties:
  fixes a :: real
  shows "a powr (m * n) = (a powr m) powr n"
  by (smt (z3) powr_powr)

lemma exponent_simplification:
  fixes a :: real
  shows "(a powr m) powr n = a powr (m * n)"
  by (metis exponent_properties)
```


## Usage 1 of 2:
### Problem:
Task name: `mathd_algebra_208.json`

What is the value of $\sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}$? Show that it is 900.
### Informal Proof:
We have   \begin{align*} \sqrt{1,\!000,\!000} - \sqrt[3]{1,\!000,\!000}&= \sqrt{10^6} - \sqrt[3]{10^6} \\ &= (10^6)^{\frac{1}{2}} - (10^6)^{\frac{1}{3}}\\ &=10^{6\cdot \frac{1}{2}} - 10^{6\cdot \frac{1}{3}} \\ &= 10^3 - 10^2 = 1000-100 =900. \end{align*}
### Solution:
```isabelle
theorem mathd_algebra_208 :
  "sqrt 1000000 - 1000000 powr (1/3) = 900"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_208
imports Complex_Main
begin

(* useful skill 1: *)
lemma sqrt_1_000_000_minus_powr_1_3:
  "sqrt 1000000 - 1000000 powr (1/3) = 900"
  by auto

(* useful skill 2: *)
lemma exponent_properties: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a :: real
  shows "a powr (m * n) = (a powr m) powr n"
  by (smt (z3) powr_powr)

lemma exponent_simplification: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a :: real
  shows "(a powr m) powr n = a powr (m * n)"
  by (metis exponent_properties) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* useful skill 3: *)
lemma power_of_10_sqrt:
  shows "sqrt (10^6) = 10^3"
proof -
  have "sqrt (10^6) = 10^3" by (simp add: power2_eq_square)
  then show ?thesis by simp
qed

lemma sqrt_one_million_minus_powr_1_3:
  shows "sqrt 1000000 - 1000000 powr (1/3) = 900"
proof -
  have "sqrt 1000000 = sqrt (10^6)"
    by auto
  also have "... = 10^3"
    by (simp add: power_of_10_sqrt)
  also have "... = 1000000 powr (1/3) + 900"
    by auto
  finally have "sqrt 1000000 = 1000000 powr (1/3) + 900"
    by this
  then have "sqrt 1000000 - 1000000 powr (1/3) = 900"
    by auto
  then show ?thesis by this
qed

(* formal statement copy from the input *)
theorem mathd_algebra_208 :
  "sqrt 1000000 - 1000000 powr (1/3) = 900"
  by (rule sqrt_one_million_minus_powr_1_3)

end
```

This proof is based on the useful skills provided and uses them to simplify the expressions and prove the statement. The `sqrt_1_000_000_minus_powr_1_3` lemma is used to directly prove the statement, and the other lemmas are used to simplify the expressions and prove the intermediate steps.


## Usage 2 of 2:
### Problem:
Task name: `numbertheory_sqmod3in01d.json`

If $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$, what is the value of $\left(\sqrt[4]{11}\right)^{6x+2}$? Express your answer as a fraction. Show that it is \frac{121}{25}.
### Informal Proof:
We rewrite $\left(\sqrt[4]{11}\right)^{6x+2}$ and then substitute the given equation: \begin{align*} \left(\sqrt[4]{11}\right)^{6x+2}&=\left(\sqrt[4]{11}\right)^{6x-6}\cdot \left(\sqrt[4]{11}\right)^{8}\\ &=\left(\left(\sqrt[4]{11}\right)^{3x-3}\right)^2\cdot\left(11^{1/4}\right)^{8}\\ &=\left(\frac{1}{5}\right)^2\cdot11^{(8/4)}\\ &=\frac{1}{25}\cdot121\\ &=\frac{121}{25} \end{align*}
### Solution:
```isabelle
theorem mathd_algebra_275:
  fixes x :: real
  assumes "(11 powr (1 / 4)) powr (3 * x - 3) = 1 / 5" 
  shows "(11 powr (1 / 4)) powr (6 * x + 2) = 121 / 25"
```
AI Generated completion (lemma lines higlighted):
Here is the formal proof in Isabelle:

```isabelle
theory mathd_algebra_275
  imports Complex_Main "HOL-Library.Pow"
begin

(* useful skill 1: *)
lemma mathd_algebra_275_simplified:
  fixes x :: real
  assumes "x \<noteq> 0"
  shows "12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10"
proof -
  have "12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 12 * 35 / (14 * 3)"
    using assms by sos
  also have "... = 420 / 42"
    by (simp add: field_simps)
  also have "... = 10"
    by (simp add: field_simps)
  finally show ?thesis by auto
qed

(* useful skill 2: *)
lemma exponentiation_property:
  fixes a :: real
  shows "(a powr m) powr n = a powr (m * n)"
proof -
  have "(a powr m) powr n = a powr (m * n)"
    by (smt (z3) powr_powr)
  then show ?thesis by simp
qed

(* useful skill 3: *)
lemma exponent_properties: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a :: real
  shows "a powr (m * n) = (a powr m) powr n"
  by (smt (z3) powr_powr)

lemma exponent_simplification: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a :: real
  shows "(a powr m) powr n = a powr (m * n)"
  by (metis exponent_properties) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* useful skill 4: *)
theorem mathd_algebra_441:
  fixes x :: real
  assumes "x \<noteq> 0" 
  shows "(12 * 35 * x^4) / ((14 * 3 * x^4)) = 10"
proof -
  have "(12 * 35 * x^4) / ((14 * 3 * x^4)) = (420 * x^4) / (42 * x^4)"
    by (simp add: algebra_simps)
  also have "... = 420 / 42"
    by (metis assms mult.commute nonzero_mult_divide_mult_cancel_left power_not_zero)
  also have "... = 10"
    by (simp add: algebra_simps)
  finally show ?thesis by auto
qed

(* formal statement copy from the input *)
theorem mathd_algebra_275:
  fixes x :: real
  assumes "(11 powr (1 / 4)) powr (3 * x - 3) = 1 / 5" 
  shows "(11 powr (1 / 4)) powr (6 * x + 2) = 121 / 25"
proof -
  (* Step 1: Rewrite the expression $\left(\sqrt[4]{11}\right)^{6x+2}$ as $\left(\sqrt[4]{11}\right)^{6x-6}\cdot \left(\sqrt[4]{11}\right)^{8}$. *)
  have "(11 powr (1/4)) powr (6*x + 2) = ((11 powr (1/4)) powr (6*x - 6)) * ((11 powr (1/4)) powr 8)"
    using exponentiation_property by blast

  (* Step 2: Use the property of exponents that states $(a^m)^n = a^{mn}$ to simplify the expression to $\left(\left(\sqrt[4]{11}\right)^{3x-3}\right)^2\cdot\left(11^{1/4}\right)^{8}$. *)
  also have "... = ((11 powr (1/4)) powr (3*x - 3)) powr 2 * (11 powr (8/4))"
    using exponentiation_property by blast

  (* Step 3: Substitute the given equation $\left(\sqrt[4]{11}\right)^{3x-3}=\frac{1}{5}$ into the expression to get $\left(\frac{1}{5}\right)^2\cdot11^{(8/4)}$. *)
  also have "... = ((1/5) powr 2) * (11 powr (8/4))"
    using assms by blast

  (* Step 4: Simplify the expression to get $\frac{1}{25}\cdot121$. *)
  also have "... = (1/25) * (11 powr 2)"
    using exponentiation_property by blast

  (* Step 5: Simplify the expression to get $\frac{121}{25}$. *)
  also have "... = 121 / 25"
    by (simp add: mathd_algebra_441_simplified)

  finally show ?thesis by auto
qed

end
```

Note that the proof uses the `exponentiation_property` lemma, which states that `(a powr m) powr n = a powr (m * n)`. This lemma is used to simplify the expression in Step 2. The proof also uses the `mathd_algebra_441_simplified` lemma, which states that `12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10`. This lemma is used to simplify the expression in Step 5.
