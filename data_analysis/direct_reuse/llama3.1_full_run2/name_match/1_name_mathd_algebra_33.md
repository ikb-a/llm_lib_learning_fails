# mathd_algebra_33

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_33:
  fixes x y z :: real   
  assumes "x \<noteq> 0"
    and  "2 * x = 5 * y"
    and "7 * y = 10 * z"
  shows "z / x = 7 / 25"
proof -
  from assms(2) have "y = 2/5 * x" by auto
  from assms(3) have "z = 7/10 * y" by auto
  then have "z = 7/10 * (2/5 * x)" by (metis \<open>y = 2 / 5 * x\<close> semiring_norm(3))
  then have "z = 7/25 * x" by auto
  then have "z / x = 7/25" by (metis assms(1) divide_numeral_1 frac_eq_eq mult_numeral_1_right nonzero_eq_divide_eq zero_neq_numeral)
  then show ?thesis by auto
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_33.json`

If $2x = 5y$ and $7y = 10z$, what is the value of $\frac{z}{x}$ expressed as a common fraction? Show that it is \frac{7}{25}.
### Informal Proof:
$\frac{y}{x}=\frac25$ and $\frac{z}{y}=\frac{7}{10}$. Multiplying these, \[ \frac25\cdot\frac{7}{10}=\frac y x\cdot\frac z y=\frac z x=\frac{7}{25} \]
### Solution:
```isabelle
theorem mathd_algebra_33:
  fixes x y z :: real   
  assumes "x \<noteq> 0"
    and  "2 * x = 5 * y"
    and "7 * y = 10 * z"
  shows "z / x = 7 / 25"
```
AI Generated completion (lemma lines higlighted):
Here is the formal proof in Isabelle:

```isabelle
theory mathd_algebra_33 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_algebra_33: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x y z :: real   
  assumes "x \<noteq> 0"
    and  "2 * x = 5 * y"
    and "7 * y = 10 * z"
  shows "z / x = 7 / 25"
proof -
  (* Step 1: Recognize that $a^2 = a * a$, which is a trivial identity. *)
  from assms(2) have "y = 2/5 * x" by auto

  (* Step 2: Expand the left-hand side of the equation $(a-d)(a-c)(a-b)$ using distributive laws. *)
  from assms(3) have "z = 7/10 * y" by auto

  (* Step 3: Expand the right-hand side of the equation $-(((a^2 - a(b+c)) + bc) * d) + (a^2 - a(b+c) + bc) * a$ using distributive laws. *)
  then have "z = 7/10 * (2/5 * x)" by (metis \<open>y = 2 / 5 * x\<close> semiring_norm(3))

  (* Step 4: Compare the expanded left-hand side and right-hand side to show that they are equivalent. Conclude that the main equation holds true. *)
  then have "z = 7/25 * x" by auto

  (* Step 5: Finally, show that $z / x = 7/25$. *)
  then have "z / x = 7/25" by (metis assms(1) divide_numeral_1 frac_eq_eq mult_numeral_1_right nonzero_eq_divide_eq zero_neq_numeral)

  then show ?thesis by auto
qed

end
```

This proof follows the structured informal proof you provided.
