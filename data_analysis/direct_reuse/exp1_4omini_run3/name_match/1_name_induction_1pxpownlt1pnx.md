# induction_1pxpownlt1pnx

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem induction_1pxpownlt1pnx:
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n * x) \<le> (1 + x)^n"
proof (induction n)
  case 0
  then show ?case by (simp add: assms)
next
  case (Suc n)
  then show ?case
  proof -
    have "1 + (Suc n) * x = 1 + n * x + x" by (simp add: field_simps)
    also have "... = (1 + n * x) + x" by simp
    also have "... \<le> (1 + x)^n + x" using Suc.IH by simp
    also have "... = (1 + x)^n + (1 + x - 1)" by (simp add: algebra_simps)
    also have "... = (1 + x)^n + (1 + x) - 1" by simp
    also have "... = (1 + x)^n + (1 + x) - (1 + x)^0" by simp
    finally show ?case using power_add by (smt (verit) Bernoulli_inequality assms less_eq_real_def)
  qed
qed
```


## Usage 1 of 1:
### Problem:
Task name: `induction_1pxpownlt1pnx.json`

Show that for any real number $x$ and any natural number $n$, if $x > -1$, then $(1+nx)\leq (1+x)^n$.
### Informal Proof:
We show the result by induction on $n$. The result is trivial for $n=0$ or $n=1$. Let us assume the property is true in $n$. By the induction hypothesis we know that $(1+nx)\leq (1+x)^n$. Moreover, as $x > -1$, we have that $x \leq x (1 + x)^n$. The inequality is trivial if $x \geq 0$, and is also true if $x < 0$ as $-1 < x < 0 \implies 0 < (1 + x)^n < 1$. So, $(1+nx) + x \leq (1+x)^n + x (1+x)^n$ and we have that $(1+(n+1)x) \leq (1+x)^(n+1)$, so the property is true in $n+1$. By induction, we have that the result is true for any natural number $n$.
### Solution:
```isabelle
theorem induction_1pxpownlt1pnx:
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n*x) \<le> (1 + x)^n"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory induction_1pxpownlt1pnx %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* Lemma for the base case when n = 0 *)
lemma induction_base_case_n_0:
  fixes x :: real
  assumes "-1 < x"
  shows "1 + 0 * x \<le> (1 + x)^0"
proof -
  show ?thesis by simp
qed

(* Lemma for the induction step *)
lemma induction_step:
  fixes x :: real and n :: nat
  assumes "-1 < x" and "1 + n * x \<le> (1 + x)^n"
  shows "1 + (n + 1) * x \<le> (1 + x)^(n + 1)"
proof -
  have "1 + (n + 1) * x = 1 + n * x + x"
    by (auto simp: field_simps)
  also have "... \<le> (1 + x)^n + x" using assms(2) by simp
  finally show "1 + (n + 1) * x \<le> (1 + x)^(n + 1)"
    by (smt (verit) Bernoulli_inequality assms(1) less_eq_real_def)
qed

(* Main theorem using induction *)
theorem induction_1pxpownlt1pnx: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n * x) \<le> (1 + x)^n"
proof (induction n)
  case 0
  then show ?case by (simp add: assms)
next
  case (Suc n)
  then show ?case
  proof -
    (* Using the induction hypothesis for n *)
    have "1 + (Suc n) * x = 1 + n * x + x" by (simp add: field_simps)
    also have "... = (1 + n * x) + x" by simp
    also have "... \<le> (1 + x)^n + x" using Suc.IH by simp
    also have "... = (1 + x)^n + (1 + x - 1)" by (simp add: algebra_simps)
    also have "... = (1 + x)^n + (1 + x) - 1" by simp
    also have "... = (1 + x)^n + (1 + x) - (1 + x)^0" by simp
    finally show ?case using power_add by (smt (verit) Bernoulli_inequality assms less_eq_real_def)
  qed
qed

end
```
