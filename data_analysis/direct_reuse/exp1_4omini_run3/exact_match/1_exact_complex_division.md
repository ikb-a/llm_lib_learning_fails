# complex_division

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma complex_division:
  fixes v z :: complex
  assumes "v = 1 + \<i>" "z = 2 - \<i>"
  shows "v / z = (1 / 5) + (3 / 5) * \<i>"
proof -
  have "v / z = (1 + \<i>) / (2 - \<i>)" using assms by simp
  also have "... = (1 + \<i>) * (2 + \<i>) / ((2 - \<i>) * (2 + \<i>))" 
    by (simp add: field_simps)
  then have "v / z = (1*2 + 1*\<i> + 2*\<i> + \<i>*\<i>) / (2^2 + 1^2)" 
    by (smt (verit) assms(1) assms(2) diff_minus_eq_add diff_numeral_special(11) distrib_left distrib_right group_cancel.add1 i_squared left_diff_distrib' mult.commute mult_1s_ring_1(1) mult_1s_ring_1(2) numeral_One one_add_one one_power2 power2_diff power2_i power_minus power_minus_Bit0 right_diff_distrib' square_diff_square_factored)
  then have "v / z = (2 + 3*\<i> - 1) / (4 + 1)" 
    by (simp add: complex_i_mult_minus)
  then have "v / z = (1 + 3*\<i>) / 5" 
    by (simp add: field_simps)
  hence "v / z = (1 / 5) + (3 / 5) * \<i>" 
    by (simp add: field_simps)
  thus ?thesis by simp
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
```isabelle
theory mathd_algebra_313
  imports Complex_Main
begin

(* lemma for complex division *)
lemma complex_division: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes v z :: complex
  assumes "v = 1 + \<i>" "z = 2 - \<i>"
  shows "v / z = (1 / 5) + (3 / 5) * \<i>"
proof -
  have "v / z = (1 + \<i>) / (2 - \<i>)" using assms by simp
  also have "... = (1 + \<i>) * (2 + \<i>) / ((2 - \<i>) * (2 + \<i>))" 
    by (simp add: field_simps)
  then have "v / z = (1*2 + 1*\<i> + 2*\<i> + \<i>*\<i>) / (2^2 + 1^2)" 
    by (smt (verit) assms(1) assms(2) diff_minus_eq_add diff_numeral_special(11) distrib_left distrib_right group_cancel.add1 i_squared left_diff_distrib' mult.commute mult_1s_ring_1(1) mult_1s_ring_1(2) numeral_One one_add_one one_power2 power2_diff power2_i power_minus power_minus_Bit0 right_diff_distrib' square_diff_square_factored)
  then have "v / z = (2 + 3*\<i> - 1) / (4 + 1)" 
    by (simp add: complex_i_mult_minus)
  then have "v / z = (1 + 3*\<i>) / 5" 
    by (simp add: field_simps)
  hence "v / z = (1 / 5) + (3 / 5) * \<i>" 
    by (simp add: field_simps)
  thus ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_313:
  fixes v i z ::complex
  assumes "v = i * z"
    and "v = 1 + \<i>"
    and "z = 2 - \<i>" 
  shows "i = 1/5 + 3/5 * \<i>"
proof -
  (* Step 1: Start with the equation \( I = \frac{V}{Z} \) where \( V = 1 + i \) and \( Z = 2 - i \). *)
  have "i = v / z" using assms(1) by auto

  (* Step 2: Substitute the values of \( V \) and \( Z \) into the equation to get: *)
  have "i = (1 + \<i>) / (2 - \<i>)" using assms(2) assms(3) by simp

  (* Step 3: Use the previously proven lemma to simplify the fraction *)
  have "i = (1 / 5) + (3 / 5) * \<i>" using complex_division by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Conclude the proof *)
  thus ?thesis by simp
qed

end
```
