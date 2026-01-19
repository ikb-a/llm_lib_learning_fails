# mathd_algebra_141

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_141:
  fixes a b :: real
  assumes "(a * b) = 180" 
      and "2 * (a + b) = 54"
  shows "a^2 + b^2 = 369"
proof -
  have "a + b = 27" 
    using assms(2) by simp
  have "a^2 + b^2 = (a + b)^2 - 2 * (a * b)" 
    by sos  
  also have "... = 27^2 - 2 * 180" 
    using `a + b = 27` assms(1) by simp 
  also have "... = 729 - 360" 
    by simp
  finally show ?thesis 
    by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_141.json`

A rectangular patio has an area of $180$ square feet and a perimeter of $54$ feet. What is the length of the diagonal (in feet) squared? Show that it is 369.
### Informal Proof:
Set one side of the patio equal to $a$ and the other equal to $b$, producing two equations: \begin{align*} ab&=180,\text{ and}\\ 2a+2b&=54. \end{align*}The second equation can be rewritten as $b=27-a$. Substituting, we have \begin{align*} 180&=a\left(27-a\right) \quad \Rightarrow \\ 180&=27a-a^2 \quad \Rightarrow \\ -180&=a^2-27a \quad \Rightarrow \\ 0&=a^2-27a+180 \quad \Rightarrow \\ 0&=\left(a-12\right)\left(a-15\right). \end{align*}So $12$ feet and $15$ feet are the lengths of the two sides of the patio. Therefore, the diagonal is $\sqrt{12^2+15^2}$, or $\sqrt{369}$. Therefore, the length of the diagonal squared is $369$.
### Solution:
```isabelle
theorem mathd_algebra_141:
  fixes a b ::real
  assumes "(a * b)=180"
    and "2 * (a + b)=54"
  shows "a^2 + b^2 = 369"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_141 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* formal statement copied from the input *)
theorem mathd_algebra_141: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b ::real
  assumes "(a * b) = 180"
    and "2 * (a + b) = 54"
  shows "a^2 + b^2 = 369"
proof -
  (* Step 1: From the perimeter equation, we can simplify to find a + b = 27. *)
  have "a + b = 27" 
    using assms(2) by simp
    
  (* Step 2: We can express b in terms of a: b = 27 - a. *)
  have "b = 27 - a" 
    using `a + b = 27` by simp
  
  (* Step 3: Substitute b into the area equation: a(27 - a) = 180. *)
  have "a * (27 - a) = 180" 
    using assms(1) `b = 27 - a` by auto
  
  (* Step 4: Expanding gives us: 27a - a^2 = 180. *)
  (* Rearranging leads to: a^2 - 27a + 180 = 0. *)
  have "a^2 - 27 * a + 180 = 0" 
    using `a * (27 - a) = 180` by sos
  
  (* Step 5: We can factor this quadratic equation. The roots are a = 12 and a = 15. *)
  have "a = 12 ∨ a = 15" 
    using `a^2 - 27 * a + 180 = 0` by auto
  
  (* Step 6: Consequently, the corresponding values for b are b = 15 when a = 12 and b = 12 when a = 15. *)
  have "b = 15 ∨ b = 12" 
    using `b = 27 - a` by auto
  
  (* Step 7: To find the length of the diagonal d, we use the Pythagorean theorem: d^2 = a^2 + b^2. *)
  have "a^2 + b^2 = (a + b)^2 - 2 * (a * b)" 
    by (simp add: algebra_simps) 
  
  (* Step 8: Substitute the known values: (12 + 15)^2 - 2 * 180. *)
  also have "... = 27^2 - 2 * 180" 
    using `a + b = 27` `a * b = 180` by auto
  
  (* Step 9: Now calculate the right-hand side: 729 - 360. *)
  also have "... = 369" 
    by simp
  
  (* Step 10: Thus we conclude that a^2 + b^2 = 369. *)
  finally show ?thesis 
    by simp
qed

end
```
