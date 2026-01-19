# sum_of_squares

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_squares:
  fixes a b :: real
  assumes "(a * b) = 180"
    and "2 * (a + b) = 54"
  shows "a^2 + b^2 = (a + b)^2 - 2 * a * b"
proof -
  have "a^2 + b^2 = (a + b)^2 - 2 * a * b"
    by sos
  then show ?thesis using assms(1) assms(2) by auto
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
theory mathd_algebra_141
  imports Complex_Main
begin

(* lemma 1. A base lemma proving a^2+b^2 = (a+b)^2 - 2*a*b *)
lemma sum_of_squares: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: real
  assumes "(a * b) = 180"
    and "2 * (a + b) = 54"
  shows "a^2 + b^2 = (a + b)^2 - 2 * a * b"
proof -
  have "a^2 + b^2 = (a + b)^2 - 2 * a * b"
    by sos
  then show ?thesis using assms(1) assms(2) by auto
qed

(* lemma 2.  A base lemma proving a^2+b^2 = 369 *)
lemma a_square_plus_b_square:
  fixes a b :: real
  assumes "(a * b) = 180" and "2 * (a + b) = 54"
  shows "a^2 + b^2 = 369"
proof -
  have "a^2 + b^2 = (a + b)^2 - 2 * a * b" by sos
  also have "(a + b)^2 - 2 * a * b = 729 - 360" using assms by sos
  finally show ?thesis by simp
qed

(* formal statement copy from the input *)
theorem mathd_algebra_141:
  fixes a b ::real
  assumes "(a * b)=180"
    and "2 * (a + b)=54"
  shows "a^2 + b^2 = 369"
proof -
  have "a^2 + b^2 = (a + b)^2 - 2 * a * b" by (rule sum_of_squares) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  also have "(a + b)^2 - 2 * a * b = 729 - 360" using assms by (rule a_square_plus_b_square)
  finally show ?thesis by simp
qed

end
```
