# multiplicative_inverse

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma multiplicative_inverse:
  fixes a b m :: int
  assumes "a * b mod m = 1"
  shows "\<exists>n. n * b mod m = 1"
proof -
  have "b * (a mod m) mod m = 1"
    using assms by (metis mod_mult_right_eq mult.commute)
  thus ?thesis by (auto simp: field_simps)
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_321.json`

Notice that  \[35\cdot40=1400.\]Find some integer $n$ with $0\leq n<1399$ such that $n$ is the multiplicative inverse to 160 modulo 1399. Show that it is 1058.
### Informal Proof:
Taking the given equation modulo 1399 gives \[35\cdot40\equiv1\pmod{1399},\]so we know that 35 is the multiplicative inverse to 40.  We want to use this to find the multiplicative inverse to $4\cdot40=160$, so we want to try to "divide" 35 by 4.  The difficulty in dividing by 4 is that 35 is odd.  We do know, though, that  \[35\equiv35+1399\equiv1434\pmod{1399}\]and this number is even!  Let's go even further, though, to find a multiple of 4: \[35\equiv35+3\cdot1399\equiv4232\pmod{1399}.\]Factoring 4 we get  \[35\equiv4\cdot1058\pmod{1399}.\]Finally we multiply by 40: \[1\equiv 40\cdot35\equiv40\cdot4\cdot1058\equiv160\cdot1058\pmod{1399}.\]This argument is inelegant.  Let's write it in a more clear order: \begin{align*} 1058\cdot160&\equiv1058\cdot(4\cdot40)\\ &\equiv(1058\cdot4)\cdot40\\ &\equiv35\cdot40\\ &\equiv1\pmod{1399}. \end{align*}The multiplicative inverse to 160 modulo 1399 is $1058$.
### Solution:
```isabelle
theorem mathd_numbertheory_321:
  fixes n::int
  assumes "\<forall>n::int. 1\<le>n \<and> n\<le> 1399 \<and> [n*160 = 1] (mod 1399)"
  shows "n = 1058"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_321
  imports Complex_Main
begin

(* This lemma will help us establish the multiplicative inverse relationship *)
lemma multiplicative_inverse: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b m :: int
  assumes "a * b mod m = 1"
  shows "\<exists>n. n * b mod m = 1"
proof -
  have "b * (a mod m) mod m = 1"
    using assms by (metis mod_mult_right_eq mult.commute)
  thus ?thesis by (auto simp: field_simps)
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_321:
  fixes n::int
  assumes "\<forall>n::int. 1\<le>n \<and> n\<le> 1399 \<and> [n*160 = 1] (mod 1399)"
  shows "n = 1058"
proof -
  (* Step 1: Given that \(35 \cdot 40 = 1400\), we have \(1400 \mod 1399 = 1\), indicating that \(35\) is the multiplicative inverse of \(40\) modulo \(1399\). *)
  have "35 * 40 mod 1399 = 1"
    by (simp add: mod_eq_0_iff_dvd)

  (* Step 2: We express \(160\) in terms of \(40\). Since \(160 = 4 \cdot 40\), we need to find the inverse of \(4\) with respect to \(35\). *)
  have "4 * 35 mod 1399 = 1400 mod 1399"
    by (simp add: mod_eq_0_iff_dvd)

  (* Step 3: As \(35 \equiv 4 \cdot 1058 \mod 1399\), we find that \(1058\) is a candidate for the multiplicative inverse of \(160\). *)
  have "4 * 1058 mod 1399 = 35"
    using mod_mult_left_eq[of 4 1058 1399] by simp

  (* Step 4: Now we multiply by \(40\) to show that \(160 \cdot 1058 \equiv 1 \mod 1399\). *)
  have "160 * 1058 mod 1399 = (4 * 40) * 1058 mod 1399"
    by (simp add: algebra_simps)

  (* Step 5: Simplifying gives us \( (160 \cdot 1058) \mod 1399 = (4 \cdot 40 \cdot 1058) \mod 1399 \equiv 1 \mod 1399\). *)
  have "4 * (40 * 1058) mod 1399 = 1"
    using multiplicative_inverse[of "40" "35" "1399"] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 6: By the assumptions of the theorem, we conclude that \(1058\) is indeed the multiplicative inverse of \(160\) modulo \(1399\). *)
  then show ?thesis
    using \<open>4 * (40 * 1058) mod 1399 = 1\<close> by simp
qed

end
```
