# floor_of_multiple

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma floor_of_multiple:
  fixes n :: real
  assumes "n = 1 / 3"
  shows "floor (10 * n) = 3" and "floor (100 * n) = 33" and "floor (1000 * n) = 333" and "floor (10000 * n) = 3333"
proof -
  have "10 * n = 10 / 3" using assms by simp
  then show "floor (10 * n) = 3" by arith
  have "100 * n = 100 / 3" using assms by simp
  then show "floor (100 * n) = 33" by arith
  have "1000 * n = 1000 / 3" using assms by simp
  then show "floor (1000 * n) = 333" by arith
  have "10000 * n = 10000 / 3" using assms by simp
  then show "floor (10000 * n) = 3333" by arith
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_153.json`

We write $\lfloor X \rfloor$ to mean the greatest integer less than or equal to $X$; for example $\lfloor 3\frac{1}{2} \rfloor = 3$. If $N = \frac{1}{3}$, what is the value of $\lfloor 10N \rfloor + \lfloor 100N \rfloor + \lfloor 1000N \rfloor + \lfloor 10,000N \rfloor$? Show that it is 3702.
### Informal Proof:
Substituting, we get:  $\lfloor 10N \rfloor$ = $\lfloor \frac {10}{3} \rfloor = 3$  $\lfloor 100N \rfloor$ = $\lfloor \frac {100}{3} \rfloor = 33$  $\lfloor 1000N \rfloor$ = $\lfloor \frac {1000}{3} \rfloor = 333$  $\lfloor 10000N \rfloor$ = $\lfloor \frac {10000}{3} \rfloor = 3333$  Adding these values, we get $3+33+333+3333 = 3702$
### Solution:
```isabelle
theorem mathd_algebra_153:
  fixes n :: real
  assumes "n = 1 / 3" 
  shows "floor (10 * n) + floor (100 * n) 
    + floor (1000 * n) + floor (10000 * n) = 3702"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_153
  imports Complex_Main
begin

(* lemma to calculate the floor of multiples of 1/3 *)
lemma floor_of_multiple: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes n :: real
  assumes "n = 1 / 3"
  shows "floor (10 * n) = 3" and "floor (100 * n) = 33" and "floor (1000 * n) = 333" and "floor (10000 * n) = 3333"
proof -
  have "10 * n = 10 / 3" using assms by simp
  then show "floor (10 * n) = 3" by arith
  have "100 * n = 100 / 3" using assms by simp
  then show "floor (100 * n) = 33" by arith
  have "1000 * n = 1000 / 3" using assms by simp
  then show "floor (1000 * n) = 333" by arith
  have "10000 * n = 10000 / 3" using assms by simp
  then show "floor (10000 * n) = 3333" by arith
qed

(* formal statement copy from the input *)
theorem mathd_algebra_153:
  fixes n :: real
  assumes "n = 1 / 3" 
  shows "floor (10 * n) + floor (100 * n) + floor (1000 * n) + floor (10000 * n) = 3702"
proof -
  (* Step 1: Use the lemma to find the individual floor values *)
  have floor_10: "floor (10 * n) = 3" using floor_of_multiple[of n] assms by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have floor_100: "floor (100 * n) = 33" using floor_of_multiple[of n] assms by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have floor_1000: "floor (1000 * n) = 333" using floor_of_multiple[of n] assms by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have floor_10000: "floor (10000 * n) = 3333" using floor_of_multiple[of n] assms by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 2: Summing the floors obtained *)
  have sum: "floor (10 * n) + floor (100 * n) + floor (1000 * n) + floor (10000 * n) = 3 + 33 + 333 + 3333"
    using floor_10 floor_100 floor_1000 floor_10000 by simp

  (* Step 3: Calculate the sum *)
  have "3 + 33 + 333 + 3333 = 3702" by simp
  
  (* Step 4: Thus, we conclude the theorem *)
  then show ?thesis using sum by simp
qed

end
```
