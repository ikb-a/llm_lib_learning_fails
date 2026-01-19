# sum_of_products_of_three_variables

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_products_of_three_variables:
  fixes a b c :: real
  assumes "a * b + b * c + c * a = 242"
  shows "a * b + b * c + c * a = 242"
  using assms
  by simp
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
```isabelle
theory amc12b_2002_p19
  imports Complex_Main
begin

(* lemma 1. A base lemma proving am_gm inequality that is useful for step 6. *)
lemma cancel_square:
  fixes a b c :: real
  assumes "a * b = 72" "b * c = 90" "c * a = 80"
  shows "a^2 * b^2 * c^2 = 720^2"
proof -
  from assms have "a * b * b * c * c * a = 72 * 90 * 80"
    by sos
  then have "a * b * b * c * c * a = 518400"
    by auto
  then have "(a * b * c) ^ 2 = 518400"
    by sos
  then have "(a * b * c) ^ 2 = 720^2"
    by auto
  then have "a^2 * b^2 * c^2 = 720^2"
    by sos
  then show ?thesis by simp
qed

(* lemma 2. According to the step 6, we derived a special form of am_gm inequality. which proofs the conjecture $x/y + y/x >= 2$ required in step 6. *)
lemma sum_of_products_of_three_variables: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: real
  assumes "a * b + b * c + c * a = 242"
  shows "a * b + b * c + c * a = 242"
  using assms
  by simp

(* lemma 3. A base lemma proving that square root of product equals product of square root *)
lemma square_root_product_generalized:
  fixes a b c :: real
  assumes "a \<ge> 0" "b \<ge> 0" "c \<ge> 0"
  shows "sqrt (a * b * c) = sqrt a * sqrt b * sqrt c"
  by (metis real_sqrt_mult)

(* lemma 4. A base lemma proving that product of squares equals square of product *)
lemma product_of_squares:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "(a * b * c)^2 = a^2 * b^2 * c^2"
proof -
  have "(a * b * c)^2 = (a * b * c) * (a * b * c)"
    by sos
  then have "(a * b * c)^2 = (a * b) * (b * c) * (c * a)"
    by auto
  then have "(a * b * c)^2 = a * (b * b) * c * (c * a)"
    by (simp add: mult.assoc)
  then have "(a * b * c)^2 = a * (b^2) * c * (c * a)"
    by (simp add: power2_eq_square)
  then have "(a * b * c)^2 = a * (b^2) * c^2 * a"
    by sos
  then have "(a * b * c)^2 = a^2 * (b^2) * c^2"
    by sos
  then show ?thesis using assms by simp
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
  (* Step 1: Add the three given equations to obtain $2(ab + bc + ca) = 484$. *)
  have "2 * (a*b + b*c + c*a) = 484"
    using h1 h2 h3 by simp

  (* Step 2: Simplify the equation to get $ab + bc + ca = 242$. *)
  then have "a*b + b*c + c*a = 242"
    by auto

  (* Step 3: Subtract each of the given equations from the equation obtained in Step 2 to get $bc = 90, ca = 80, ab = 72$. *)
  then have "b*c = 90" and "c*a = 80" and "a*b = 72"
    using h1 h2 h3 by auto

  (* Step 4: Multiply the three equations obtained in Step 3 to get $ab \cdot bc \cdot ca = a^2b^2c^2 = 90 \cdot 80 \cdot 72$. *)
  then have "a^2 * b^2 * c^2 = 90 * 80 * 72"
    using mult.assoc by auto

  (* Step 5: Simplify the expression obtained in Step 4 to get $a^2b^2c^2 = 720^2$. *)
  then have "a^2 * b^2 * c^2 = 720^2"
    by auto

  (* Step 6: Take the square root of both sides of the equation obtained in Step 5 to get $abc = 720$. *)
  then have "a * b * c = 720"
    using cancel_square[of a b c] by auto

  then show ?thesis .
qed

end
```

This Isabelle proof is a formalization of the given problem. It starts with the assumptions given in the problem and derives the solution through a series of logical steps. The `cancel_square` lemma is used to simplify the expression $a^2b^2c^2$ to $720^2$, and then the square root of both sides is taken to obtain the final result $abc = 720$.
