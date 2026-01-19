# induction_1pxpownlt1pnx_base

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma induction_1pxpownlt1pnx_base:
  fixes x :: real
  assumes "-1 < x"
  shows "(1 + 0 * x) \<le> (1 + x)^0"
proof -
  have "(1 + 0 * x) = 1" by simp
  moreover have "(1 + x)^0 = 1" by simp
  ultimately show ?thesis by simp
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
theory induction_1pxpownlt1pnx
  imports Complex_Main
begin

(* Step 1: Base case where n = 0 *)
lemma induction_1pxpownlt1pnx_base: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "-1 < x"
  shows "(1 + 0 * x) \<le> (1 + x)^0"
proof -
  have "(1 + 0 * x) = 1" by simp
  moreover have "(1 + x)^0 = 1" by simp
  ultimately show ?thesis by simp
qed

(* Step 2: Inductive step *)
lemma induction_1pxpownlt1pnx_step:
  fixes x :: real and n :: nat
  assumes "-1 < x" "(1 + n * x) \<le> (1 + x)^n"
  shows "(1 + (n + 1) * x) \<le> (1 + x)^(n + 1)"
proof -
  (* Using the inductive hypothesis: (1 + n * x) \<le> (1 + x)^n *)
  have ih: "(1 + n * x) \<le> (1 + x)^n" using assms(2) by simp

  (* Add x to both sides: (1 + n * x) + x \<le> (1 + x)^n + x *)
  have "(1 + n * x) + x = 1 + (n + 1) * x" by simp
  hence lhs: "1 + (n + 1) * x = (1 + n * x) + x" by simp

  (* For the RHS: (1 + x)^n + x \<le> (1 + x)^(n + 1) *)
  have "(1 + x)^n + x = (1 + x)^n + x * 1" by simp
  hence rhs: "(1 + x)^n + x = (1 + x)^n + x * (1 + x)^0" by simp

  (* Since x > -1, we have x ≤ x * (1 + x)^n *)
  have "x * (1 + x)^n \<ge> x" 
  proof (cases "x \<ge> 0")
    case True
    then show ?thesis by simp
  next
    case False
    with assms(1) have "-1 < x \<and> x < 0" by simp
    hence "(1 + x)^n > 0" by simp
    then show ?thesis using mult_left_le_imp_le[of x "(1 + x)^n" x] False by simp
  qed

  (* Thus, (1 + x)^n + x ≤ (1 + x)^n + x * (1 + x)^n = (1 + x)^(n + 1) *)
  have "(1 + x)^n + x \<le> (1 + x)^(n + 1)"
  proof -
    have "(1 + x)^n + x \<le> (1 + x)^n + x * (1 + x)^n" by (simp add: `x * (1 + x)^n \<ge> x`)
    moreover have "(1 + x)^n + x * (1 + x)^n = (1 + x)^(n + 1)" by (simp add: distrib_left)
    ultimately show ?thesis by simp
  qed

  (* Conclude the inductive step *)
  from ih lhs rhs show ?thesis by simp
qed

(* Step 3: Conclusion using induction *)
theorem induction_1pxpownlt1pnx:
  fixes x :: real and n :: nat
  assumes "-1 < x"
  shows "(1 + n * x) \<le> (1 + x)^n"
proof (induction n)
  case 0
  then show ?case using induction_1pxpownlt1pnx_base[OF assms] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
next
  case (Suc n)
  then show ?case using induction_1pxpownlt1pnx_step[OF assms Suc.IH] by simp
qed

end
```
