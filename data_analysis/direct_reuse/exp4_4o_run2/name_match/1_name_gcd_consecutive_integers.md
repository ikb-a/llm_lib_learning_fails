# gcd_consecutive_integers

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma gcd_consecutive_integers:
  fixes a b :: int
  assumes "b = a + 1"
  shows "gcd a b = 1"
proof -
  have "gcd a (a + 1) = gcd a 1"
    by auto
  thus ?thesis using assms by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_435.json`

Find the smallest positive integer $k$ such that, for every positive integer $n$, $6n+k$ is relatively prime to each of $6n+3$, $6n+2$, and $6n+1$. Show that it is 5.
### Informal Proof:
Obviously, we have that $k > 3$, because otherwise two of the integers would be identical and not be relatively prime. Start by testing $k=4$. $6n+4$ and $6n+3$ are relatively prime because they are consecutive integers, but $6n+4$ and $6n+2$ are both even and are therefore not relatively prime. The next candidate to test is $k=5$. Firstly, we have that \begin{align*} \gcd(6n+5, 6n+3) &= \gcd(6n+3, (6n+5)-(6n+3)) \\ &= \gcd(6n+3, 2).  \end{align*}Since $6n+3$ is always odd, the two integers $6n+5$ and $6n+3$ are relatively prime. Secondly, \begin{align*} \gcd(6n+5, 6n+2) &= \gcd(6n+2, (6n+5)-(6n+2)) \\&= \gcd(6n+2, 3).  \end{align*}Note that $6n+3$ is always divisible by 3, so $6n+2$ is never divisible by 3. As a result, we have that $6n+5$ and $6n+2$ are relatively prime. Finally, \begin{align*} \gcd(6n+5, 6n+1) &= \gcd(6n+1, (6n+5)-(6n+1)) \\ &= \gcd(6n+1, 4).  \end{align*}Note that $6n+1$ is always odd, so $6n+5$ and $6n+1$ are also relatively prime. Therefore, the smallest positive integer $k$ that permits $6n+k$ to be relatively prime with each of $6n+3$, $6n+2$, and $6n+1$ is $k = 5$.
### Solution:
```isabelle
theorem mathd_numbertheory_435:
  fixes k :: nat
  assumes "0 < k"
    and "\<forall> n. gcd (6 * n + k) (6 * n + 3) = 1"
    and "\<forall> n. gcd (6 * n + k) (6 * n + 2) = 1"
    and "\<forall> n. gcd (6 * n + k) (6 * n + 1) = 1" 
  shows "5 \<le> k"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_435
  imports Complex_Main
begin

(* lemma 1: gcd of consecutive integers is 1 *)
lemma gcd_consecutive_integers: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b :: nat
  assumes "b = a + 1"
  shows "gcd a b = 1"
proof -
  have "gcd a (a + 1) = gcd a 1"
    by (simp add: gcd_rec)
  thus ?thesis using assms by simp
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_435:
  fixes k :: nat
  assumes "0 < k"
    and "\<forall> n. gcd (6 * n + k) (6 * n + 3) = 1"
    and "\<forall> n. gcd (6 * n + k) (6 * n + 2) = 1"
    and "\<forall> n. gcd (6 * n + k) (6 * n + 1) = 1"
  shows "5 \<le> k"
proof (rule ccontr)
  assume "\<not> 5 \<le> k"
  hence "k < 5" by simp
  consider (k_eq_1) "k = 1" | (k_eq_2) "k = 2" | (k_eq_3) "k = 3" | (k_eq_4) "k = 4" using `k < 5` `0 < k` by arith
  then show False
  proof cases
    case k_eq_1
    (* Step 1: Test k = 1 *)
    have "\<exists> n. gcd (6 * n + 1) (6 * n + 1) \<noteq> 1"
      by (metis gcd_self nat_1_add_1)
    thus False using k_eq_1 assms(2) by blast
  next
    case k_eq_2
    (* Step 2: Test k = 2 *)
    have "\<exists> n. gcd (6 * n + 2) (6 * n + 2) \<noteq> 1"
      by (metis gcd_self nat_1_add_1)
    thus False using k_eq_2 assms(3) by blast
  next
    case k_eq_3
    (* Step 3: Test k = 3 *)
    have "\<exists> n. gcd (6 * n + 3) (6 * n + 3) \<noteq> 1"
      by (metis gcd_self nat_1_add_1)
    thus False using k_eq_3 assms(2) by blast
  next
    case k_eq_4
    (* Step 4: Test k = 4 *)
    have "\<exists> n. gcd (6 * n + 4) (6 * n + 2) \<noteq> 1"
      by (metis gcd_nonzero_nat nat_1_add_1)
    thus False using k_eq_4 assms(3) by blast
  qed
qed

end
```

In this proof, we check all possible values for \( k \) less than 5. Each case demonstrates a contradiction with the assumption that \( k \) satisfies the conditions for being relatively prime to \( 6n+3 \), \( 6n+2 \), and \( 6n+1 \). Therefore, the smallest possible value for \( k \) is 5.
