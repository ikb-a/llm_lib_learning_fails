# sum_of_three_equations

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_three_equations:
  fixes a b c :: real
  assumes "a * (b + c) = 152" "b * (c + a) = 162" "c * (a + b) = 170"
  shows "2 * (a * b + b * c + c * a) = 484"
proof -
  have "2 * (a * b + b * c + c * a) = a * (b + c) + b * (c + a) + c * (a + b)"
    by (simp add: algebra_simps)
  also have "... = 152 + 162 + 170" using assms by simp
  also have "... = 484" by simp
  finally show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `amc12b_2002_p19.json`

If $a,b,$ and $c$ are positive [[real number]]s such that $a(b+c) = 152, b(c+a) = 162,$ and $c(a+b) = 170$, then $abc$ is  $\mathrm{(A)}\ 672 \qquad\mathrm{(B)}\ 688 \qquad\mathrm{(C)}\ 704 \qquad\mathrm{(D)}\ 720 \qquad\mathrm{(E)}\ 750$ Show that it is 720.
### Informal Proof:
Adding up the three equations gives $2(ab + bc + ca) = 152 + 162 + 170 = 484 \Longrightarrow ab + bc + ca = 242$. Subtracting each of the above equations from this yields, respectively, $bc = 90, ca = 80, ab = 72$. Taking their product, $ab \cdot bc \cdot ca = a^2b^2c^2 = 90 \cdot 80 \cdot 72 = 720^2 \Longrightarrow abc = 720 \Rightarrow \mathrm{(D)}$.
### Solution:
```isabelle
theorem amc12b_2002_p19:
  fixes a b c::real
  assumes h0: "0 < a \<and> 0 < b \<and> 0 < c"
    and h1: "a * (b + c) = 152"
    and h2: "b * (c + a) = 162"
    and h3: "c * (a + b) = 170"
  shows "a * b * c = 720"
```
AI Generated completion (lemma lines higlighted):
## Proof
```isabelle
theory amc12b_2002_p19
  imports Complex_Main
begin

(* useful lemma to prove useful properties *)
lemma real_number_properties:
  fixes a b c :: real
  assumes "a * (b + c) = b * (c + a)"
  shows "a * b + a * c = b * c + a * b"
proof -
  from assms have "a * (b + c) = b * (c + a)" by simp
  then have "a * b + a * c = b * c + b * a" by (simp add: algebra_simps)
  then have "a * b + a * c = b * c + a * b" by (simp add: ac_simps)
  then show ?thesis by simp
qed

(* useful lemma to prove useful properties *)
lemma sum_of_three_equations: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: real
  assumes "a * (b + c) = 152" "b * (c + a) = 162" "c * (a + b) = 170"
  shows "2 * (a * b + b * c + c * a) = 484"
proof -
  have "2 * (a * b + b * c + c * a) = a * (b + c) + b * (c + a) + c * (a + b)"
    by (simp add: algebra_simps)
  also have "... = 152 + 162 + 170" using assms by simp
  also have "... = 484" by simp
  finally show ?thesis by simp
qed

(* formal statement copy from the input *)
theorem amc12b_2002_p19:
  fixes a b c::real
  assumes h0: "0 < a \<and> 0 < b \<and> 0 < c"
    and h1: "a * (b + c) = 152"
    and h2: "b * (c + a) = 162"
    and h3: "c * (a + b) = 170"
  shows "a * b * c = 720"
proof -
  (* Step 1: Add up the three given equations to obtain $2(ab + bc + ca) = 484$. *)
  have "2 * (a * b + b * c + c * a) = 484" using assms by (rule sum_of_three_equations) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 2: Simplify the result to get $ab + bc + ca = 242$. *)
  then have "a * b + b * c + c * a = 242" by (simp add: divide_real_def)

  (* Step 3: Subtract each of the given equations from the result to obtain $bc = 90, ca = 80, ab = 72$. *)
  then have "b * c = 90" and "c * a = 80" and "a * b = 72" using assms by (simp add: algebra_simps)

  (* Step 4: Take the product of these three equations to get $ab \cdot bc \cdot ca = a^2b^2c^2 = 90 \cdot 80 \cdot 72$. *)
  then have "a^2 * b^2 * c^2 = 90 * 80 * 72" by (simp add: algebra_simps)

  (* Step 5: Simplify the product to get $a^2b^2c^2 = 720^2$. *)
  then have "a^2 * b^2 * c^2 = 720^2" by (simp add: power2_eq_square)

  (* Step 6: Take the square root of both sides to get $abc = 720$. *)
  then have "a * b * c = 720" by (simp add: power2_eq_square)

  show ?thesis by (simp add: h0)
qed

end
```
The final answer is 720.
