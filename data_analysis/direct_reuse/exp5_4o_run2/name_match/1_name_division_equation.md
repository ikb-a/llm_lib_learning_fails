# division_equation

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma division_equation:
  fixes a b q r :: nat
  assumes "a = q * b + r" and "r < b"
  shows "a mod b = r"
proof -
  from assms(1) have "a = q * b + r" .
  hence "a mod b = (q * b + r) mod b" by simp
  also have "... = r mod b" by (simp add: mod_add_eq)
  also have "... = r" using assms(2)
    by (simp add: mod_less)
  finally show "a mod b = r" .
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_66.json`

Determine the remainder of 194 (mod 11). Show that it is 7.
### Informal Proof:
$$194 = 17 \cdot 11 + 7 \implies 194 \equiv 7 \pmod{11}.$$
### Solution:
```isabelle
theorem mathd_numbertheory_66:
  "194 mod 11 = (7::nat)"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_66
  imports Complex_Main
begin

(* Lemma 1: Using a known lemma for computing the remainder of a division *)
lemma division_remainder:
  fixes a b q r :: nat
  assumes "a = q * b + r"
  assumes "r < b"
  shows "a mod b = r"
  using assms by (simp add: division_equation) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(* Formal statement copied from the input *)
theorem mathd_numbertheory_66:
  "194 mod 11 = (7::nat)"
proof -
  (* Step 1: Express 194 in terms of a multiple of 11 plus a remainder. *)
  (* Perform the division: \(194 \div 11 = 17\) with a remainder. *)
  let ?q = "17::nat"
  let ?r = "194 - ?q * 11"
  have "194 = ?q * 11 + ?r" by simp

  (* Step 3: Calculate the remainder: \(194 - 17 \times 11 = 194 - 187 = 7\). *)
  hence "?r = 7" by simp

  (* Step 4: Verify that the remainder is less than 11, which is true *)
  have "?r < 11" by simp

  (* Applying the division_remainder lemma to conclude the result *)
  show ?thesis using division_remainder[of 194 11 ?q ?r]
    by (simp add: `194 = ?q * 11 + ?r` `?r < 11`)
qed

end
```
