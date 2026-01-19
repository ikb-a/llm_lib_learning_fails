# mathd_algebra_478

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem mathd_algebra_478:
  fixes b h v :: real
  assumes "0 < b" and "0 < h" and "0 < v" and "v = 1 / 3 * (b * h)" and "b = 30" and "h = 13 / 2"
  shows "v = 65"
proof -
  have h0: "v = 1 / 3 * (b * h)" using assms by auto
  have h1: "b = 30" using assms by auto
  have h2: "h = 13 / 2" using assms by auto
  have h3: "v = 1 / 3 * (30 * (13 / 2))" using h0 h1 h2 by auto
  then have h4: "v = 1 / 3 * (390 / 2)" using h3 by auto
  then have h5: "v = 1 / 3 * 195" using h4 by auto
  then have h6: "v = 65" using h5 by auto
  then show ?thesis by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_algebra_478.json`

The volume of a cone is given by the formula $V = \frac{1}{3}Bh$, where $B$ is the area of the base and $h$ is the height. The area of the base of a cone is 30 square units, and its height is 6.5 units. What is the number of cubic units in its volume? Show that it is 65.
### Informal Proof:
We are given that $B = 30$ and $h = 6.5$ and asked to find $\frac{1}{3}Bh$.  We find that \[\frac{1}{3}Bh = \frac{1}{3}(30)(6.5) = (10)(6.5) = 65.\]
### Solution:
```isabelle
theorem mathd_algebra_478:
  fixes b h v ::real
  assumes "0 < b \<and> 0 < h \<and> 0 < v"
      and "v = 1 / 3 * (b * h)"
      and "b = 30"
      and "h = 13 / 2"
    shows "v = 65"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_algebra_478 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* algebraic manipulation lemma *)
lemma algebraic_manipulation:
  fixes b h v :: real
  assumes "v = 1 / 3 * (b * h)"
  shows "v = (1/3) * (b * h)"
proof -
  from assms show ?thesis by simp
qed

(* formal statement copy from the input*)
theorem mathd_algebra_478: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes b h v ::real
  assumes "0 < b \<and> 0 < h \<and> 0 < v"
      and "v = 1 / 3 * (b * h)"
      and "b = 30"
      and "h = 13 / 2"
    shows "v = 65"
proof -
  (* Step 1: Substitute the given values for $B$ and $h$ into the formula. *)
  have c0: "v = 1 / 3 * (b * h)" 
    using assms(2) sledgehammer

  (* Step 2: Simplify the expression to find the volume. *)
  have "b = 30" 
    using assms(4) sledgehammer
  then have c1: "v = 1 / 3 * (30 * (13 / 2))" 
    using c0 sledgehammer
  then have c2: "v = 1 / 3 * (390 / 2)" 
    sledgehammer
  then have c3: "v = 1 / 3 * 195" 
    sledgehammer

  (* Step 3: Perform the arithmetic to find the volume. *)
  then have c4: "v = 65" 
    sledgehammer

  (* Step 4: Conclude that the volume of the cone is 65 cubic units. *)
  then show ?thesis 
    sledgehammer
qed

end
```

This proof is a direct application of the formula for the volume of a cone and the given values for the area of the base and the height.
