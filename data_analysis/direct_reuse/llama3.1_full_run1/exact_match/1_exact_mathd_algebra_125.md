# mathd_algebra_125

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_125:
  fixes x y :: nat
  assumes "5 * x = y"
    and  "(x - 3) + (y - 3) = 30" 
  shows "x = 6"
proof -
  have "5 * x = y" and "(x - 3) + (y - 3) = 30" using assms by auto
  then have "5 * x + x - 6 = 30" by auto
  then have "6 * x = 36" by auto
  then have "x = 6" by (simp add: divide_pos_pos)
  then show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_125.json`

Today a father's age is five times his son's age. Exactly three years ago, the sum of their ages was 30. How old is the son today? Show that it is 6.
### Informal Proof:
Let $x$ be the son's age today and his father's age $y$.  We know: $5x = y$, and that $(x -3) + (y -3) = 30$.  Substituting the first equation into the second, we get: $6x = 36$, and thus, $x=6$.
### Solution:
```isabelle
theorem mathd_algebra_125:
  fixes x y :: nat
  assumes "5 * x = y"
    and  "(x - 3) + (y - 3) = 30" 
  shows "x = 6"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_125 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
imports Main
begin

(* formal statement copied from the input *)
theorem mathd_algebra_125: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x y :: nat
  assumes "5 * x = y"
    and  "(x - 3) + (y - 3) = 30" 
  shows "x = 6"
proof -
  have "5 * x = y" and "(x - 3) + (y - 3) = 30" using assms by auto
  then have "5 * x + x - 6 = 30" by auto
  then have "6 * x = 36" by auto
  then have "x = 6" by (simp add: divide_pos_pos)
  then show ?thesis by simp
qed

(* useful lemma *)
lemma linear_equation_solution:
  fixes x :: nat
  shows "6 * x = 36 \<Longrightarrow> x = 6"
proof -
  assume "6 * x = 36"
  then have "x * 6 = 36" by auto
  then have "x = 36 / 6" by (simp add: divide_eq_eq)
  then have "x = 6" by (simp add: divide_pos_pos)
  then show ?thesis by simp
qed
```

Note: In Isabelle, it's generally more idiomatic to define lemmas in a separate theory file and import that theory into the main theory file. However, for simplicity, I've included the lemma directly in the proof.
