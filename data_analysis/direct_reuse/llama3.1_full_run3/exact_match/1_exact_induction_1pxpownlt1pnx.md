# induction_1pxpownlt1pnx

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem induction_1pxpownlt1pnx:
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n*x) \<le> (1 + x)^n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "(1 + (Suc n)*x) \<le> (1 + x)^(Suc n)"
    using assms Suc.IH by (smt (verit) Bernoulli_inequality nless_le)
  then show ?case by simp
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
Here's a formal proof using Isabelle:

```isabelle
theory induction_1pxpownlt1pnx %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* formal statement copied from the input *)
theorem induction_1pxpownlt1pnx: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n*x) \<le> (1 + x)^n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "(1 + (Suc n)*x) \<le> (1 + x)^(Suc n)"
    using assms Suc.IH by (smt (verit) Bernoulli_inequality nless_le)
  then show ?case by simp
qed

end
```

This proof uses the Bernoulli inequality, which states that for any real number $x$ and any natural number $n$, if $x \geq -1$, then $(1 + x)^n \geq 1 + nx$. We also use the fact that for any real number $x$ and any natural number $n$, if $x > -1$, then $x \leq x (1 + x)^n$.
