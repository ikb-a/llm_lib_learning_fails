# solve_linear_equations

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma solve_linear_equations:
  fixes a d :: real
  assumes "a + 6 * d = 30" and "a + 10 * d = 60"
  shows "d = 15 / 2"
proof -
  have "a + 10 * d - (a + 6 * d) = 60 - 30" using assms by (simp add: algebra_simps)
  then have "4 * d = 30" by simp
  then show "d = 15 / 2" by (simp add: field_simps)
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_354.json`

In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence? Show that it is 135.
### Informal Proof:
Let $a$ be the first term in this arithmetic sequence, and let $d$ be the common difference.  Then the $7^{\text{th}}$ term is $a + 6d = 30$, and the $11^{\text{th}}$ term is $a + 10d = 60$.  Subtracting these equations, we get $4d = 30$, so $d = 30/4 = 15/2$.  Then the $21^{\text{st}}$ term is $a + 20d = (a + 10d) + 10d = 60 + 10 \cdot 15/2 = 135$.
### Solution:
```isabelle
theorem mathd_algebra_354:
  fixes a d :: real
  assumes "a + 6 * d = 30"
    and "a + 10 * d = 60" 
  shows "a + 20 * d = 135"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_354
  imports Complex_Main
begin

(* lemma 1: Solve the system of linear equations to find d. *)
lemma solve_linear_equations: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a d :: real
  assumes "a + 6 * d = 30" and "a + 10 * d = 60"
  shows "d = 15 / 2"
proof -
  have "a + 10 * d - (a + 6 * d) = 60 - 30" using assms by (simp add: algebra_simps)
  then have "4 * d = 30" by simp
  then show "d = 15 / 2" by (simp add: field_simps)
qed

(* lemma 2: Substitute d back into the equation to find a. *)
lemma find_a:
  fixes a d :: real
  assumes "a + 6 * d = 30" and "d = 15/2"
  shows "a = -15"
proof -
  have "a + 6 * (15 / 2) = 30" using assms by simp
  then have "a + 45 = 30" by simp
  then show "a = -15" by simp
qed

(* main theorem proof *)
theorem mathd_algebra_354:
  fixes a d :: real
  assumes "a + 6 * d = 30"
    and "a + 10 * d = 60" 
  shows "a + 20 * d = 135"
proof -
  (* Step 1: Find d using the previously defined lemma. *)
  have d_val: "d = 15 / 2" using solve_linear_equations assms by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 2: Find a using the previously defined lemma with the value of d. *)
  have a_val: "a = -15" using find_a[where d="15/2"] d_val assms by simp

  (* Step 3: Calculate the 21st term using a and d. *)
  have "a + 20 * d = -15 + 20 * (15 / 2)" by (simp add: d_val a_val)
  also have "... = -15 + 150" by simp
  finally show ?thesis by simp
qed

end
```
