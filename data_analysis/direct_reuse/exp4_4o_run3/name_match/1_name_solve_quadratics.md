# solve_quadratics

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_quadratics:
  fixes x :: real
  assumes "x^2 - x - 1 = 0 \<or> x^2 + x - 1 = 0"
  shows "x = (1 + sqrt 5) / 2 \<or> x = (1 - sqrt 5) / 2 \<or> x = (-1 + sqrt 5) / 2 \<or> x = (-1 - sqrt 5) / 2"
proof -
  {
    assume "x^2 - x - 1 = 0"
    then have "(x - (1 + sqrt 5) / 2) * (x - (1 - sqrt 5) / 2) = 0"
      by (simp add: field_simps power2_eq_square)
    hence "x = (1 + sqrt 5) / 2 \<or> x = (1 - sqrt 5) / 2"
      by simp
  }
  moreover
  {
    assume "x^2 + x - 1 = 0"
    then have "(x - (-1 + sqrt 5) / 2) * (x - (-1 - sqrt 5) / 2) = 0"
      by (simp add: field_simps power2_eq_square)
    hence "x = (-1 + sqrt 5) / 2 \<or> x = (-1 - sqrt 5) / 2"
      by simp
  }
  ultimately show ?thesis
    using assms by blast
qed
```


## Usage 1 of 1:
### Problem:
Task name: `amc12a_2002_p13.json`

Two different positive numbers $a$ and $b$ each differ from their reciprocals by $1$. What is $a+b$?  $ \text{(A) }1 \qquad \text{(B) }2 \qquad \text{(C) }\sqrt 5 \qquad \text{(D) }\sqrt 6 \qquad \text{(E) }3 $ Show that it is (C) \sqrt 5.
### Informal Proof:
Each of the numbers $a$ and $b$ is a solution to $\left| x - \frac 1x \right| = 1$.  Hence it is either a solution to $x - \frac 1x = 1$, or to $\frac 1x - x = 1$. Then it must be a solution either to $x^2 - x - 1 = 0$, or to $x^2 + x - 1 = 0$.  There are in total four such values of $x$, namely $\frac{\pm 1 \pm \sqrt 5}2$.   Out of these, two are positive: $\frac{-1+\sqrt 5}2$ and $\frac{1+\sqrt 5}2$. We can easily check that both of them indeed have the required property, and their sum is $\frac{-1+\sqrt 5}2 + \frac{1+\sqrt 5}2 = (C) \sqrt 5$.
### Solution:
```isabelle
theorem amc12a_2002_p13:
  fixes a b :: real
  assumes h0: "0 < a \<and> 0 < b"
      and h1: "a \<noteq> b"
      and h2: "abs (a - 1/a) = 1"
      and h3: "abs (b - 1/b) = 1" 
    shows "a + b = sqrt 5"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory amc12a_2002_p13
  imports Complex_Main
begin

(* Lemma 1: Solve quadratic equations that have two different positive solutions, which is useful for Step 3 in the main theorem. *)
lemma solve_quadratics: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: real
  assumes "x^2 - x - 1 = 0 \<or> x^2 + x - 1 = 0"
  shows "x = (1 + sqrt 5) / 2 \<or> x = (1 - sqrt 5) / 2 \<or> x = (-1 + sqrt 5) / 2 \<or> x = (-1 - sqrt 5) / 2"
proof -
  {
    assume "x^2 - x - 1 = 0"
    then have "(x - (1 + sqrt 5) / 2) * (x - (1 - sqrt 5) / 2) = 0"
      by (simp add: field_simps power2_eq_square)
    hence "x = (1 + sqrt 5) / 2 \<or> x = (1 - sqrt 5) / 2"
      by simp
  }
  moreover
  {
    assume "x^2 + x - 1 = 0"
    then have "(x - (-1 + sqrt 5) / 2) * (x - (-1 - sqrt 5) / 2) = 0"
      by (simp add: field_simps power2_eq_square)
    hence "x = (-1 + sqrt 5) / 2 \<or> x = (-1 - sqrt 5) / 2"
      by simp
  }
  ultimately show ?thesis
    using assms by blast
qed

(* formal statement copy from the input *)
theorem amc12a_2002_p13:
  fixes a b :: real
  assumes h0: "0 < a \<and> 0 < b"
      and h1: "a \<noteq> b"
      and h2: "abs (a - 1/a) = 1"
      and h3: "abs (b - 1/b) = 1" 
    shows "a + b = sqrt 5"
proof -
  (* Step 1 and Step 2: Consider the case $a - 1/a = 1$, which implies $a^2 - a - 1 = 0$. By Lemma 1, the positive solution is $a = \frac{1 + \sqrt{5}}{2}$. *)
  have c0: "a^2 - a - 1 = 0 \<or> a^2 + a - 1 = 0"
  proof -
    {
      assume "a - 1/a = 1"
      hence "a^2 - a = 1"
        by (metis (no_types, lifting) diff_divide_eq_iff eq_divide_eq)
      hence "a^2 - a - 1 = 0"
        by simp
    }
    moreover
    {
      assume "1/a - a = 1"
      hence "1 - a^2 = a"
        by (metis (no_types, lifting) eq_divide_eq_iff)
      hence "a^2 + a - 1 = 0"
        by simp
    }
    ultimately show ?thesis
      using h2 by fastforce
  qed

  (* Step 3: Similarly, consider the case $b - 1/b = 1$, which implies $b^2 - b - 1 = 0$. By Lemma 1, the positive solution is $b = \frac{-1 + \sqrt{5}}{2}$. *)
  have c1: "b^2 - b - 1 = 0 \<or> b^2 + b - 1 = 0"
  proof -
    {
      assume "b - 1/b = 1"
      hence "b^2 - b = 1"
        by (metis (no_types, lifting) diff_divide_eq_iff eq_divide_eq)
      hence "b^2 - b - 1 = 0"
        by simp
    }
    moreover
    {
      assume "1/b - b = 1"
      hence "1 - b^2 = b"
        by (metis (no_types, lifting) eq_divide_eq_iff)
      hence "b^2 + b - 1 = 0"
        by simp
    }
    ultimately show ?thesis
      using h3 by fastforce
  qed

  (* Step 4: Use Lemma 1 to identify the correct positive solutions for $a$ and $b$. *)
  have "a = (1 + sqrt 5) / 2 \<or> a = (-1 + sqrt 5) / 2"
    using solve_quadratics c0 by blast %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  moreover
  have "b = (1 + sqrt 5) / 2 \<or> b = (-1 + sqrt 5) / 2"
    using solve_quadratics c1 by blast %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  ultimately have "(a = (1 + sqrt 5) / 2 \<and> b = (-1 + sqrt 5) / 2) \<or> (a = (-1 + sqrt 5) / 2 \<and> b = (1 + sqrt 5) / 2)"
    using h1 by auto

  (* Step 5: Calculate the sum of the positive solutions $a$ and $b$. *)
  hence "a + b = sqrt 5"
    by (simp add: field_simps)

  show ?thesis
    using `a + b = sqrt 5` by auto
qed

end
```
