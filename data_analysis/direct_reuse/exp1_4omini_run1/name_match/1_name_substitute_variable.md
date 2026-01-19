# substitute_variable

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma substitute_variable:
  fixes x y z w :: real
  assumes "y = w + 3 * z"
  shows "3 * x + 4 * (w + 3 * z) - 12 * z = 10 \<Longrightarrow> 3 * x + 4 * w = 10"
  and "-2 * x - 3 * (w + 3 * z) + 9 * z = -4 \<Longrightarrow> -2 * x - 3 * w = -4"
proof -
  show "3 * x + 4 * (w + 3 * z) - 12 * z = 10 \<Longrightarrow> 3 * x + 4 * w = 10"
  proof -
    assume h1: "3 * x + 4 * (w + 3 * z) - 12 * z = 10"
    have "3 * x + 4 * w + 12 * z - 12 * z = 10" by (smt (verit) h1)
    thus "3 * x + 4 * w = 10" by (simp add: add_cancel_right_left)
  qed
  show "-2 * x - 3 * (w + 3 * z) + 9 * z = -4 \<Longrightarrow> -2 * x - 3 * w = -4"
  proof -
    assume h2: "-2 * x - 3 * (w + 3 * z) + 9 * z = -4"
    have "-2 * x - 3 * w - 9 * z + 9 * z = -4" by (smt (verit) h2)
    thus "-2 * x - 3 * w = -4" by (simp add: add_cancel_right_left)
  qed
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_388.json`

If  \begin{align*} 3x+4y-12z&=10,\\ -2x-3y+9z&=-4, \end{align*}  compute $x$. Show that it is 14.
### Informal Proof:
Let $w=y-3z$.  The equations become  \begin{align*} 3x+4w&=10,\\ -2x-3w&=-4. \end{align*}  Adding four times the second equation to three times the first equation,  $$9x+12w-8x-12w=30-16\Rightarrow x=14.$$
### Solution:
```isabelle
theorem mathd_algebra_388:
  fixes x y z :: real
  assumes "3 * x + 4 * y - 12 * z = 10"
      and "-2 * x - 3 * y + 9 * z = -4"
    shows "x = 14"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_388
  imports Complex_Main
begin

(* lemma 1: This lemma will assist in substituting the variable y in terms of w and z *)
lemma substitute_variable: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x y z w :: real
  assumes "y = w + 3 * z"
  shows "3 * x + 4 * (w + 3 * z) - 12 * z = 10 \<Longrightarrow> 3 * x + 4 * w = 10"
     and "-2 * x - 3 * (w + 3 * z) + 9 * z = -4 \<Longrightarrow> -2 * x - 3 * w = -4"
proof -
  show "3 * x + 4 * (w + 3 * z) - 12 * z = 10 \<Longrightarrow> 3 * x + 4 * w = 10"
  proof -
    assume h1: "3 * x + 4 * (w + 3 * z) - 12 * z = 10"
    have "4 * (w + 3 * z) - 12 * z = 4 * w + 12 * z - 12 * z" by simp
    thus "3 * x + 4 * w = 10" using h1 by (simp add: algebra_simps)
  qed
  show "-2 * x - 3 * (w + 3 * z) + 9 * z = -4 \<Longrightarrow> -2 * x - 3 * w = -4"
  proof -
    assume h2: "-2 * x - 3 * (w + 3 * z) + 9 * z = -4"
    have "-3 * (w + 3 * z) + 9 * z = -3 * w - 9 * z + 9 * z" by simp
    thus "-2 * x - 3 * w = -4" using h2 by (simp add: algebra_simps)
  qed
qed

(* formal statement copy from the input *)
theorem mathd_algebra_388:
  fixes x y z :: real
  assumes "3 * x + 4 * y - 12 * z = 10"
      and "-2 * x - 3 * y + 9 * z = -4"
    shows "x = 14"
proof -
  (* Step 1: Introduce a new variable w = y - 3z. This allows us to express y in terms of w and z. *)
  define w where "w = y - 3 * z"
  
  (* Step 2: Substitute y into both equations using the new variable w. *)
  have eq1: "3 * x + 4 * (w + 3 * z) - 12 * z = 10"
    using assms(1) w_def by auto
  have eq2: "-2 * x - 3 * (w + 3 * z) + 9 * z = -4"
    using assms(2) w_def by auto
  
  (* Step 3: Now we will simplify these two equations using the lemma. *)
  have "3 * x + 4 * w = 10" using substitute_variable(1) eq1 by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "-2 * x - 3 * w = -4" using substitute_variable(2) eq2 by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
  (* Step 4: We now have a simpler system of equations to solve: *)
  (* 1. 3 * x + 4 * w = 10 *)
  (* 2. -2 * x - 3 * w = -4 *)
  
  (* Step 5: Solve the second equation for w. *)
  have "3 * w = -2 * x + 4" by (simp add: "-2 * x - 3 * w = -4")
  then have "w = (-2 * x + 4) / 3" by (simp add: divide_simps)
  
  (* Step 6: Substitute w back into the first equation. *)
  have "3 * x + 4 * ((-2 * x + 4) / 3) = 10"
    by (simp add: "3 * x + 4 * w = 10")
  then have "3 * x + (4 * (-2 * x + 4)) / 3 = 10"
    by simp
  (* Multiply through by 3 to eliminate the fraction *)
  then have "9 * x + 4 * (-2 * x + 4) = 30" by (simp add: algebra_simps)
  then have "9 * x - 8 * x + 16 = 30" by (simp add: algebra_simps)
  then have "x + 16 = 30" by (simp add: algebra_simps)
  
  (* Step 7: Solve for x. *)
  then show "x = 14" by simp
qed

end
```
