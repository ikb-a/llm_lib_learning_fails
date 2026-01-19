# base_conversion_sum

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
fun base_conversion_sum :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "base_conversion_sum [] b = 0" |
  "base_conversion_sum (d # ds) b = d * b ^ length ds + base_conversion_sum ds b"
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_207.json`

Convert $852_9$ to base 10. Show that it is 695.
### Informal Proof:
We have that $852_9 = 8(9^2) +5(9^1)+ 2(9^0) = 8(81)+5(9)+2(1)=648 + 45 + 2 = 695$.
### Solution:
```isabelle
theorem mathd_numbertheory_207:
  "8 * 9^2 + 5 * 9 + 2 = (695::nat)"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_207
imports Complex_Main 
begin

(* Helper function for base conversion from a list of digits and a base *)
fun base_conversion_sum :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  "base_conversion_sum [] b = 0" | %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  "base_conversion_sum (d # ds) b = d * b ^ length ds + base_conversion_sum ds b" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* formal statement copy from the input *)
theorem mathd_numbertheory_207:
  "8 * 9^2 + 5 * 9 + 2 = (695::nat)"
proof -
  (* Step 1: Use the base_conversion_sum function to evaluate the sum for the digits [8, 5, 2] in base 9 *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  have "base_conversion_sum [8, 5, 2] 9 = 8 * 9^2 + 5 * 9 + 2" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    by simp

  (* Step 2: Evaluate the sum to get the base 10 conversion, which should be 695 *)
  also have "... = 695"
    by eval

  (* Step 3: Conclude that the base 10 representation of 852_9 is 695 *)
  finally show ?thesis by simp
qed

end
```
