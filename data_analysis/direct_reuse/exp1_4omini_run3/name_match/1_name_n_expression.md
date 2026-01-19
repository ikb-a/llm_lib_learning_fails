# n_expression

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma n_expression:
  fixes n :: nat
  assumes "n mod 5 = 3"
  shows "n = 5 * (n div 5) + 3"
  using assms by presburger
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_185.json`

When a number is divided by 5, the remainder is 3. What is the remainder when twice the number is divided by 5? Show that it is 1.
### Informal Proof:
If our number is $n$, then $n\equiv 3\pmod5$.  This tells us that  \[2n=n+n\equiv 3+3\equiv1\pmod5.\] The remainder is $1$ when the number is divided by 5.
### Solution:
```isabelle
theorem mathd_numbertheory_185:
  fixes n ::nat
  assumes "n mod 5 = 3" 
  shows "(2 * n) mod 5 = 1"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_185
imports Complex_Main 
begin

(* Lemma: Express a natural number n in terms of its modulo with respect to 5. This will be useful for the main theorem, allowing us to manipulate the expression easily. *)
lemma n_expression: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes n :: nat
  assumes "n mod 5 = 3"
  shows "n = 5 * (n div 5) + 3"
  using assms by presburger

(* formal statement copy from the input *)
theorem mathd_numbertheory_185:
  fixes n ::nat
  assumes "n mod 5 = 3" 
  shows "(2 * n) mod 5 = 1"
proof -
  (* Step 1: Using the lemma to express n in terms of its modulo 5. *)
  have "n = 5 * (n div 5) + 3" 
    using n_expression assms by simp %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  (* Step 2: Calculate 2n using the expression obtained. *)
  then have "2 * n = 2 * (5 * (n div 5) + 3)" 
    by simp

  (* Step 3: Expand the expression for 2n. *)
  hence "2 * n = 10 * (n div 5) + 6" 
    by (simp add: algebra_simps)

  (* Step 4: We will now compute (2n) mod 5. Using properties of mod, we can separate the terms. *)
  have "(2 * n) mod 5 = (10 * (n div 5) + 6) mod 5" 
    by simp

  (* Step 5: Since 10 is divisible by 5, we simplify 10 * (n div 5) mod 5. *)
  also have "... = (10 * (n div 5) mod 5 + 6 mod 5)" 
    by presburger

  (* Step 6: We know that 10 mod 5 is 0, so we have: *)
  also have "... = (0 + 1)" 
    by (simp add: mod_mult_self2)

  (* Step 7: Therefore, we conclude that (2n) mod 5 = 1. *)
  finally show "(2 * n) mod 5 = 1" 
    by simp
qed

end
```
