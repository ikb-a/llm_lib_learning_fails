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
  then show ?case by (simp add: power_0)
next
  case (Suc n)
  have "1 + Suc n * x = 1 + n * x + x" by (simp add: field_simps)
  also have "(1 + x) ^ Suc n = (1 + x) * (1 + x)^n" by simp
  hence "1 + Suc n * x \<le> (1 + x) * (1 + x)^n" 
    by (smt (verit) Bernoulli_inequality assms less_eq_real_def)
  ultimately show ?case by simp
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

(* This theorem states that for any real number x and any natural number n, if x > -1, then (1 + nx) <= (1 + x)^n. *)
theorem induction_1pxpownlt1pnx: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n * x) \<le> (1 + x)^n"
proof (induction n)
  case 0
  (* Base case: n = 0 *)
  then show ?case by (simp add: power_0)
next
  case (Suc n)
  (* Assume the property holds for n, i.e., 1 + n * x <= (1 + x)^n *)
  have "1 + Suc n * x = 1 + n * x + x" by (simp add: field_simps)
  also have "(1 + x) ^ Suc n = (1 + x) * (1 + x)^n" by simp
  (* We need to show that 1 + Suc n * x <= (1 + x) * (1 + x)^n *)
  have "1 + n * x <= (1 + x)^n" using Suc.IH by simp
  then have "1 + n * x + x <= (1 + x) * (1 + x)^n" 
    by (smt (verit) assms less_eq_real_def add_le_mono)
  (* Now we can conclude that the property holds for Suc n *)
  ultimately show ?case by simp
qed

end
```
