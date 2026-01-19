# multiples_of_20

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
lemma multiples_of_20:
  fixes x :: nat
  assumes "20 dvd x" "15 \<le> x" "x < 86"
  shows "x \<in> {20, 40, 60, 80}"
proof -
  from assms(1) have "x mod 20 = 0" by auto
  then have "x div 20 = x div 20" by simp
  then have "x = 20 * (x div 20)" by (metis assms(1) dvd_mult_div_cancel)
  with assms have "x = 20 * (x div 20)" by (simp add: mult_le_mono)
  then show "x \<in> {20, 40, 60, 80}" using assms by auto
qed
```


## Usage 1 of 1:
### Problem:
Task name: `mathd_numbertheory_12.json`

How many integers between 15 and 85 are divisible by 20? Show that it is 4.
### Informal Proof:
For integers divisible by 20, we look for multiples of 20. The least and greatest multiples of 20 between 15 and 85 are 20 and 80, respectively. Between those two multiples of 20 are 40 and 60. So there are $4$ multiples of 20 between 15 and 85.
### Solution:
```isabelle
theorem mathd_numbertheory_12 :
  "card {x::nat. 20 dvd x \<and> 15 \<le> x \<and> x < 86} =4"
```
AI Generated completion (lemma lines higlighted):
## Formal proof
```isabelle
theory mathd_numbertheory_12
  imports Complex_Main
begin

(* useful lemma: multiples_of_20 *) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
lemma multiples_of_20: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes x :: nat
  assumes "20 dvd x" "15 \<le> x" "x < 86"
  shows "x \<in> {20, 40, 60, 80}"
proof -
  from assms(1) have "x mod 20 = 0" by auto
  then have "x div 20 = x div 20" by simp
  then have "x = 20 * (x div 20)" by (metis assms(1) dvd_mult_div_cancel)
  with assms have "x = 20 * (x div 20)" by (simp add: mult_le_mono)
  then show "x \<in> {20, 40, 60, 80}" using assms by auto
qed

(* formal statement copy from the input *)
theorem mathd_numbertheory_12 :
  "card {x::nat. 20 dvd x \<and> 15 \<le> x \<and> x < 86} =4"
proof -
  let ?set = "{x::nat. 20 dvd x \<and> 15 \<le> x \<and> x < 86}"
  have "?set = {20, 40, 60, 80}"
    using multiples_of_20 by auto %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  then show ?thesis
    by (simp add: card_eq_Suc_iff)
qed

end
```

This formal proof uses the `multiples_of_20` lemma to show that the set of numbers divisible by 20 between 15 and 85 is equal to the set {20, 40, 60, 80}. The cardinality of this set is then calculated to be 4. %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
