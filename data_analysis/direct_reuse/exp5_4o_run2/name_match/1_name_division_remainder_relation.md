# division_remainder_relation

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma division_remainder_relation:
  fixes a b q r :: nat
  assumes "b > 0"
  assumes "a = q * b + r"
  assumes "r < b"
  shows "a mod b = r"
proof -
  have "a mod b = r"
    using assms by auto
  thus ?thesis
    by simp
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_551.json`

Determine the remainder of 1529 (mod 6). Show that it is 5.
### Informal Proof:
$1529 = 254 \cdot 6 + 5 \Rightarrow 1529 \equiv 5 \pmod{6}$.
### Solution:
```isabelle
theorem mathd_numbertheory_551 :
  "1529 mod 6 = (5::nat)"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_551
  imports Complex_Main
begin

(* We will use a lemma to express 1529 in terms of a multiple of 6 plus a remainder. *)

(* Helper lemma stating the division remainder relation *)
lemma division_remainder_relation: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b q r :: nat
  assumes "b > 0"
  assumes "a = q * b + r"
  assumes "r < b"
  shows "a mod b = r"
proof -
  have "a mod b = r"
    using assms by auto
  thus ?thesis
    by simp
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_551 :
  "1529 mod 6 = (5::nat)"
proof -
  (* Step 1: Express 1529 as a multiple of 6 plus a remainder. We calculate the quotient q and remainder r. *)
  let ?q = "254::nat"
  let ?r = "1529 - ?q * 6"
  
  (* Step 2: Perform the division to find the remainder. *)
  have "1529 = ?q * 6 + ?r" by simp
  hence "?r = 5" by simp
  have "?r < 6" by simp

  (* Step 3: Conclude that the remainder when 1529 is divided by 6 is 5. *)
  show ?thesis using division_remainder_relation[of 1529 6 ?q ?r] %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    by auto
qed

end
```
