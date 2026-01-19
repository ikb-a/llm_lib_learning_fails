# total_marbles_general, mathd_numbertheory_254

Tasks where a provided skill's *name* is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma total_marbles_general:
  fixes a b c :: nat
  assumes "a > 0" and "b > 0" and "c > 0"
  shows "a + b + c = (a + b + c)"
proof -
  show ?thesis by simp
qed

theorem mathd_numbertheory_254:
  fixes a b c :: nat
  assumes "a = 239" and "b = 174" and "c = 83"
  shows "(a + b + c) mod 10 = (6::nat)"
proof -
  have "a + b + c = 496" using total_marbles_general[of a b c] assms by simp
  thus ?thesis by auto
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_254.json`

Sally, Wei-Hwa, and Zoe are playing a game of marbles involving first arranging as many piles of 10 marbles as possible.  Sally brought 239 marbles, Wei-Hwa brought 174 marbles, and Zoe brought 83 marbles.  If all their marbles are grouped together, how many must be removed in order to start the game? Show that it is 6.
### Informal Proof:
The marbles will be grouped into piles of 10.  We might as well group the number of marbles each of Sally, Wei-Hwa, and Zoe brought into as many piles of 10 as possible before sorting out the rest.  This means we only need to consider the modulo 10 residues of the numbers of marbles each of them brought:  \begin{align*} 239 &\equiv 9 \pmod{10} \\ 174 &\equiv 4 \pmod{10} \\ 83 &\equiv 3 \pmod{10} \end{align*}  Our goal is to find the modulo 10 residue of the total number of marbles.  We find this by adding the residues above: $9 + 4 + 3 = 16 \equiv 6 \pmod{10}$.  Since we were working in modulo 10, this is the same as a units digit calculation.
### Solution:
```isabelle
theorem mathd_numbertheory_254:
  "(239 + 174 + 83) mod 10 = (6::nat)"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory mathd_numbertheory_254 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
imports Complex_Main
begin

(* formal statement copy from the input *)
theorem mathd_numbertheory_254: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  "(239 + 174 + 83) mod 10 = (6::nat)"
proof -
  (* Step 1: Calculate the total number of marbles brought by Sally, Wei-Hwa, and Zoe. *)
  have total_marbles: "239 + 174 + 83 = 496" by auto

  (* Step 2: Compute the total. This has been calculated in the previous step. *)
  (* Therefore, we can go directly to finding the modulo. *)

  (* Step 3: Find the remainder when the total number of marbles (496) is divided by 10. *)
  show ?thesis using total_marbles by (simp add: mod_simps)
qed

end
```
