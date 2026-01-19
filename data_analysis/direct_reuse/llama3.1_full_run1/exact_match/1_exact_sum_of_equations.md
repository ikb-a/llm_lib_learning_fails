# sum_of_equations

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_equations:
  fixes a b c :: real
  assumes "3 * a + b + c = -3"
    and "a + 3 * b + c = 9"
    and "a + b + 3 * c = 19" 
  shows "5 * a + 5 * b + 5 * c = 25"
proof -
  have "(3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) = (-3) + 9 + 19"
    using assms by simp
  then have "3 * a + b + c + a + 3 * b + c + a + b + 3 * c = 25"
    by (simp add: algebra_simps)
  then have "5 * a + 5 * b + 5 * c = 25"
    by (simp add: algebra_simps)
  then show ?thesis
    by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_338.json`

If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. Show that it is -56.
### Informal Proof:
Summing all three equations yields that $5a + 5b + 5c = -3 + 9 + 19 = 25$. Thus, $a + b + c = 5$. Subtracting this from each of the given equations, we obtain that $2a = -8, 2b = 4, 2c = 14$. Thus, $a = -4, b = 2, c =7$, and their product is $abc = -4 \times 2 \times 7 = -56$.
### Solution:
```isabelle
theorem mathd_algebra_338:
  fixes a b c :: real
  assumes "3 * a + b + c = -3"
    and "a + 3 * b + c = 9"
    and "a + b + 3 * c = 19" 
  shows "a * b * c = -56"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_338
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

(* useful lemma *)
lemma sum_of_equations: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: real
  assumes "3 * a + b + c = -3"
    and "a + 3 * b + c = 9"
    and "a + b + 3 * c = 19" 
  shows "5 * a + 5 * b + 5 * c = 25"
proof -
  have "(3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) = (-3) + 9 + 19"
    using assms by simp
  then have "3 * a + b + c + a + 3 * b + c + a + b + 3 * c = 25"
    by (simp add: algebra_simps)
  then have "5 * a + 5 * b + 5 * c = 25"
    by (simp add: algebra_simps)
  then show ?thesis
    by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_338:
  fixes a b c :: real
  assumes "3 * a + b + c = -3"
    and "a + 3 * b + c = 9"
    and "a + b + 3 * c = 19" 
  shows "a * b * c = -56"
proof -
  (* Step 1: Sum all three given equations to obtain $5a + 5b + 5c = -3 + 9 + 19 = 25$. *)
  have "5 * a + 5 * b + 5 * c = 25"
    using sum_of_equations assms by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 2: Divide both sides of the equation by 5 to get $a + b + c = 5$. *)
  then have "a + b + c = 5"
    by (simp add: algebra_simps)

  (* Step 3: Subtract the equation $a + b + c = 5$ from each of the given equations to obtain $2a = -8, 2b = 4, 2c = 14$. *)
  have "2 * a = -8"
    using assms(1) by (simp add: algebra_simps)
  have "2 * b = 4"
    using assms(2) by (simp add: algebra_simps)
  have "2 * c = 14"
    using assms(3) by (simp add: algebra_simps)

  (* Step 4: Divide both sides of each of the equations $2a = -8, 2b = 4, 2c = 14$ by 2 to get $a = -4, b = 2, c = 7$. *)
  then have "a = -4"
    by (simp add: divide_eq_if)
  have "b = 2"
    by (simp add: divide_eq_if)
  have "c = 7"
    by (simp add: divide_eq_if)

  (* Step 5: Calculate the product of $a, b, c$ to get $abc = -4 \times 2 \times 7 = -56$. *)
  then show ?thesis
    by (simp add: mult_assoc)
qed

end
```
