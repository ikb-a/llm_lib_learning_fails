# units_digit_of_sum

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma units_digit_of_sum:
  fixes a b :: nat
  shows "(a + b) mod 10 = ((a mod 10) + (b mod 10)) mod 10"
  by (simp add: mod_add_eq)
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_3.json`

What is the units digit of the sum of the squares of the first nine positive integers? Show that it is 5.
### Informal Proof:
We can reduce the amount of work we have to do in this problem by realizing that the units digit of the sum of the squares is the units digit of the sum of the units digits of the squares. In other words, the units digit of $1^2+2^2+\ldots+9^2$ is the units digit of $1+4+9+6+5+6+9+4+1=45$, which is $5$.
### Solution:
```isabelle
theorem mathd_numbertheory_3 :
  "(\<Sum> x < 10. ((x + 1)^2)) mod 10 = (5::nat)"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_3
  imports Complex_Main
begin

(* We will use the lemma 'units_digit_squared' to determine the units digit of each square. *)

(* formal statement copy from the input *)
theorem mathd_numbertheory_3 :
  "(\<Sum> x < 10. ((x + 1)^2)) mod 10 = (5::nat)"
proof -
  (* Step 1: Calculate the square of each of the first nine positive integers and determine their units digits. *)
  have units_digits: "map (\<lambda>x. ((x + 1)^2) mod 10) [0..<9] = [1,4,9,6,5,6,9,4,1]"
  proof -
    (* We use the lemma 'units_digit_squared' to verify each units digit. *)
    have "((1::nat)^2) mod 10 = 1" by (simp add: units_digit_squared)
    moreover have "((2::nat)^2) mod 10 = 4" by (simp add: units_digit_squared)
    moreover have "((3::nat)^2) mod 10 = 9" by (simp add: units_digit_squared)
    moreover have "((4::nat)^2) mod 10 = 6" by (simp add: units_digit_squared)
    moreover have "((5::nat)^2) mod 10 = 5" by (simp add: units_digit_squared)
    moreover have "((6::nat)^2) mod 10 = 6" by (simp add: units_digit_squared)
    moreover have "((7::nat)^2) mod 10 = 9" by (simp add: units_digit_squared)
    moreover have "((8::nat)^2) mod 10 = 4" by (simp add: units_digit_squared)
    moreover have "((9::nat)^2) mod 10 = 1" by (simp add: units_digit_squared)
    ultimately show ?thesis by eval
  qed
  
  (* Step 2: Sum the units digits obtained from Step 1. *)
  have sum_units_digits: "sum_list [1,4,9,6,5,6,9,4,1] = 45" by eval

  (* Step 3: Determine the units digit of the sum calculated in Step 2. *)
  have "(45::nat) mod 10 = 5" by eval

  (* Step 4: Conclude that the units digit of the sum of the squares of the first nine positive integers is 5. *)
  show ?thesis 
    using units_digits sum_units_digits by (simp add: sum_list_mod units_digit_of_sum) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
qed

end
```

