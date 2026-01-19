# sum_of_powers

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma sum_of_powers:
  fixes n :: nat
  shows "(\<Prod> k < n. (2^(2^k) + 3^(2^k))) = (3::nat)^(2^n) - 2^(2^n)"
proof (induction n)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  then have IH: "(\<Prod> k < n. (2^(2^k) + 3^(2^k))) = (3::nat)^(2^n) - 2^(2^n)" 
    by simp
  have "(\<Prod> k < Suc n. (2^(2^k) + 3^(2^k))) = (\<Prod> k < n. (2^(2^k) + 3^(2^k))) * (2^(2^n) + 3^(2^n))"
    by (simp add: prod.atLeastLessThan_Suc) 
  also have "... = ((3::nat)^(2^n) - 2^(2^n)) * (2^(2^n) + 3^(2^n))" 
    using IH by simp
  also have "... = (3^(2^n) * 3^(2^n)) - (2^(2^n) * 2^(2^n))" 
    by (simp add: algebra_simps)
  also have "... = 3^(2^(Suc n)) - 2^(2^(Suc n))" 
    by (metis power2_eq_square power_Suc power_even_eq semiring_norm(3))
  finally show ?case by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `amc12a_2021_p9.json`

Which of the following is equivalent to $(2+3)(2^2+3^2)(2^4+3^4)(2^8+3^8)(2^{16}+3^{16})(2^{32}+3^{32})(2^{64}+3^{64})?$ $\textbf{(A)} ~3^{127} + 2^{127} \qquad\textbf{(B)} ~3^{127} + 2^{127} + 2 \cdot 3^{63} + 3 \cdot 2^{63} \qquad\textbf{(C)} ~3^{128}-2^{128} \qquad\textbf{(D)} ~3^{128} + 2^{128} \qquad\textbf{(E)} Show that it is \textbf{(C)} ~3^{128}-2^{128}.
### Informal Proof:
By multiplying the entire equation by $3-2=1$, all the terms will simplify by difference of squares, and the final answer is $\textbf{(C)} ~3^{128}-2^{128}$.  Additionally, we could also multiply the entire equation (we can let it be equal to $x$) by $2-3=-1$. The terms again simplify by difference of squares. This time, we get $-x=2^{128}-3^{128} \Rightarrow x=3^{128}-2^{128}$. Both solutions yield the same answer.
### Solution:
```isabelle
theorem amc12a_2021_p9 :
  shows "(\<Prod> k<7. (2^(2^k) + 3^(2^k))) = (3::nat)^128 - 2^128"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory amc12a_2021_p9 
  imports Complex_Main 
begin

(* Lemma: The product of terms of the form (2^(2^k) + 3^(2^k)) can be expressed in terms of a difference of powers. *)
lemma prod_sum_of_powers: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes n :: nat
  shows "(\<Prod> k < n. (2^(2^k) + 3^(2^k))) = (3::nat)^(2^n) - 2^(2^n)"
proof (induction n)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  then have IH: "(\<Prod> k < n. (2^(2^k) + 3^(2^k))) = (3::nat)^(2^n) - 2^(2^n)" 
    by simp
  have "(\<Prod> k < Suc n. (2^(2^k) + 3^(2^k))) = (\<Prod> k < n. (2^(2^k) + 3^(2^k))) * (2^(2^n) + 3^(2^n))"
    by (simp add: prod.atLeastLessThan_Suc)
  also have "... = ((3::nat)^(2^n) - 2^(2^n)) * (2^(2^n) + 3^(2^n))" 
    using IH by simp
  also have "... = 3^(2^n) * 3^(2^n) - 2^(2^n) * 2^(2^n)" 
    by (simp add: algebra_simps)
  also have "... = 3^(2^(Suc n)) - 2^(2^(Suc n))" 
    by (metis power2_eq_square power_Suc power_even_eq semiring_norm(3))
  finally show ?case by simp
qed

(* formal statement copy from the input *)
theorem amc12a_2021_p9 :
  shows "(\<Prod> k<7. (2^(2^k) + 3^(2^k))) = (3::nat)^128 - 2^128"
proof -
  (* Step 1: Recognize the expression we need to evaluate: \((2+3)(2^2+3^2)(2^4+3^4)(2^8+3^8)(2^{16}+3^{16})(2^{32}+3^{32})(2^{64}+3^{64})\). *)
  have "(\<Prod> k<7. (2^(2^k) + 3^(2^k))) = (\<Prod> k<7. (2^(2^k) + 3^(2^k)))" by simp

  (* Step 2: Apply the lemma for n=7. *)
  then have "(\<Prod> k<7. (2^(2^k) + 3^(2^k))) = (3::nat)^(2^7) - 2^(2^7)"
    using prod_sum_of_powers[of 7] by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 3: Simplify the powers: \(2^7 = 128\). *)
  then have "(\<Prod> k<7. (2^(2^k) + 3^(2^k))) = (3::nat)^(128) - 2^(128)" by simp

  (* Step 4: Conclude that the original expression simplifies to \(3^{128} - 2^{128}\). *)
  thus ?thesis by simp
qed

end
```
