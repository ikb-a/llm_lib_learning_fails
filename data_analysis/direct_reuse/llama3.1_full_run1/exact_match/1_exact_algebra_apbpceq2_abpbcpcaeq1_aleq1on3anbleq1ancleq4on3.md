# algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3

Tasks where a provided skill is reproduced verbatim

Frequency: 1

Lemma:
```isabelle
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3:
  fixes a b c :: real
  assumes "a \<le> b \<and> b \<le> c"
    and "a + b + c = 2"
    and "a * b + b * c + c * a = 1" 
  shows "0 \<le> a \<and> a \<le> 1 / 3 \<and> 1 / 3 \<le> b \<and> b \<le> 1 \<and> 1 \<le> c \<and> c \<le> 4 / 3"
proof -
  have "0 \<le> a" using assms by sos
  have "a \<le> 1 / 3" using assms by sos
  have "1 / 3 \<le> b" using assms by sos
  have "b \<le> 1" using assms by sos
  have "1 \<le> c" using assms by sos
  have "c \<le> 4 / 3" using assms by sos
  then show ?thesis by (metis \<open>0 \<le> a\<close> \<open>1 / 3 \<le> b\<close> \<open>1 \<le> c\<close> \<open>a \<le> 1 / 3\<close> \<open>b \<le> 1\<close>)
qed
```


## Usage 1 of 1:
### Problem:
Task name: `algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3.json`

Let $a, b, c$ be real numbers satisfying $a \leq b \leq c$, $a+b+c=2$, and $ab+bc+ca=1$. Show that $0 \leq a \leq \frac{1}{3}$, $\frac{1}{3} \leq b \leq 1$, and $1 \leq c \leq \frac{4}{3}$.
### Informal Proof:
From $a+b+c=2$ and $ab+bc+ca=1$, we know that \begin{align} \label{eq:a2b2c2} a^2 + b^2 + c^2 = (a+b+c)^2 - 2(ab+bc+ca) = 2. \end{align} First, if $a \leq b < 0$, we have $c = 2 - a - b > 2$, which is impossible because of $\eqref{eq:a2b2c2}$. \\  Next, if $a < 0 \leq b$, then $b + c = 2 - a > 2$. Consequently,  \[2(b^2 + c^2) \geq b^2 + 2bc + c^2 = (b+c)^2 > 4 \Longrightarrow b^2 + c^2 > 2,\] which is impossible, again because of $\eqref{eq:a2b2c2}$. So we have $0 \leq a \leq b \leq c$. \\  If $a=0$, it is easy to find $b=c=1$; if $a=b$, it is easy to find $a=b=1/3$ and $c=4/3$; if $b=c$, it is easy to find $a=0$ and $b=c=1$. \\   From now on, suppose $0<a<b<c$. Plugging $b+c=2-a$ into $ab+bc+ca=bc+a(b+c)=1$, we obtain \[a(2-a)+bc=1 \Longleftrightarrow a^2-2a+(1-bc) = 0.\] Thus, we have \[a = \frac{2 \pm \sqrt{4 - 4(1-bc)}}{2} \quad \Longrightarrow \quad a = 1-\sqrt{bc} \quad \mbox{ or } \quad a = 1 + \sqrt{bc}.\] If $a = 1 + \sqrt{bc}$, we have $a > 1 + b > b$ which is contradictory. Thus, $a = 1-\sqrt{bc}$. \\   Similarly, we obtain $b = 1\pm\sqrt{ac}$ and $c = 1\pm\sqrt{ab}$. \\   If $b = 1 + \sqrt{ac} > 1 + \sqrt{ab}$ as $c > b$, which implies $b > c = 1\pm\sqrt{ab}$. This is contradictory. So, we have $b = 1 - \sqrt{ac} < 1$. So we have showed that $\underline{0 \leq a \leq b \leq 1}$. \\   Next, if $c = 1 - \sqrt{ab} < 1 - a$ as $a < b$, we obtain $a + c < 1$ which implies $b > 1$ as $a + b + c = 2$. This is impossible as $c > b$. Thus, we have $\underline{c = 1 + \sqrt{ab} > 1}$. \\   Now, plugging $a = 1 - \sqrt{bc}$, $b = 1 - \sqrt{ac}$ and $c = 1 + \sqrt{ab}$ into $a+b+c = 2$, we obtain \begin{align*} 3 + \sqrt{ab} - \sqrt{c}(\sqrt{a} + \sqrt{b}) = 2 \quad \Longleftrightarrow \quad \sqrt{c}(\sqrt{a} + \sqrt{b}) = 1 + \sqrt{ab} = c \quad \Longrightarrow \quad \sqrt{c} = \sqrt{a} + \sqrt{b}. \end{align*} So we have \begin{align} \label{eq:abab1} c = (\sqrt{a} + \sqrt{b})^2 = a + b + 2\sqrt{ab} = 1 + \sqrt{ab} \quad \Longrightarrow \quad a + b + \sqrt{ab} = 1. \end{align} From~\eqref{eq:abab1}, we have \begin{align*} &1 = a + b + \sqrt{ab} \leq b + b + b \Longrightarrow b \geq 1/3, \\  &1 = a + b + \sqrt{ab} \geq a + a + a \Longrightarrow a \leq 1/3. \end{align*} Thus, we obtain $\underline{0 \leq a \leq 1/3}$ and $\underline{1/3 \leq b \leq 1}$. \\   It remains to show $c \leq 4/3$. From~\eqref{eq:abab1}, we obtain \[\sqrt{a} = \frac{-\sqrt{b} + \sqrt{4-3b}}{2}.\] So \[\sqrt{c} = \sqrt{a} + \sqrt{b} = \frac{-\sqrt{b} + \sqrt{4-3b}}{2} + \sqrt{b} = \frac{\sqrt{b} + \sqrt{4-3b}}{2},\] with $1/3 \leq b \leq 1$.  Consider the function $f(x) = \frac{\sqrt{x} + \sqrt{4-3x}}{2}$ with $x \in [1/3, 1]$. The derivative of $f$ is \begin{align*} f'(x) = \frac{1}{4}\left(\frac{1}{\sqrt{x}} - \frac{3}{\sqrt{4-3x}}\right). \end{align*} If $f'(x) = 0$, we obtain $x = 1/3$. When $x > 1/3$, we have $f'(x) < 0$, so function $f$ is strictly decreasing for $x \in (1/3, 1]$. Thus, we have \[\max_{b \in [1/3, 1]} f(b) = \sqrt{c} = f(1/3) = \frac{2\sqrt{3}}{3} \Longrightarrow c \leq \frac{4}{3}.\]
### Solution:
```isabelle
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3:
  fixes a b c :: real
  assumes "a \<le> b \<and> b \<le> c"
    and "a + b + c = 2"
    and "a * b + b * c + c * a = 1" 
  shows "0 \<le> a \<and> a \<le> 1 / 3 \<and> 1 / 3 \<le> b \<and> b \<le> 1 \<and> 1 \<le> c \<and> c \<le> 4 / 3"
```
AI Generated completion (lemma lines higlighted):
```isabelle
theory algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main
begin

(* formal statement copy from the input *)
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: real
  assumes "a \<le> b \<and> b \<le> c"
    and "a + b + c = 2"
    and "a * b + b * c + c * a = 1" 
  shows "0 \<le> a \<and> a \<le> 1 / 3 \<and> 1 / 3 \<le> b \<and> b \<le> 1 \<and> 1 \<le> c \<and> c \<le> 4 / 3"
proof -
  have "0 \<le> a" using assms by sos
  have "a \<le> 1 / 3" using assms by sos
  have "1 / 3 \<le> b" using assms by sos
  have "b \<le> 1" using assms by sos
  have "1 \<le> c" using assms by sos
  have "c \<le> 4 / 3" using assms by sos
  then show ?thesis by (metis \<open>0 \<le> a\<close> \<open>1 / 3 \<le> b\<close> \<open>1 \<le> c\<close> \<open>a \<le> 1 / 3\<close> \<open>b \<le> 1\<close>)
qed
```

## Alternative Proof using algebra_apbon2pownleqapownpbpowon2_3d

```isabelle
theory algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  imports Complex_Main algebra_apbon2pownleqapownpbpowon2_3d
begin

(* formal statement copy from the input *)
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3: %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  fixes a b c :: real
  assumes "a \<le> b \<and> b \<le> c"
    and "a + b + c = 2"
    and "a * b + b * c + c * a = 1" 
  shows "0 \<le> a \<and> a \<le> 1 / 3 \<and> 1 / 3 \<le> b \<and> b \<le> 1 \<and> 1 \<le> c \<and> c \<le> 4 / 3"
proof -
  have "(a + b + c)^2 = (a + b + c) * (a + b + c)" by auto
  also have "... = a^2 + a * b + a * c + b * a + b^2 + b * c + c * a + c^2" by (simp add: algebra_simps)
  also have "... = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a)" by (simp add: algebra_simps)
  also have "... = a^2 + b^2 + c^2 + 2 * 1" using assms by (simp add: algebra_simps)
  also have "... = 2" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) algebra_simps)
  also have "... = (a + b + c)^2" using assms by (simp add: algebra_simps)
  finally have "a^2 + b^2 + c^2 = 2" by simp
  then have "0 \<le> a" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "0 \<le> b" using algebra_apbon2pownleqapown2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "0 \<le> c" using algebra_apbon2pownleqapown2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a + b + c = 2" using assms by (simp add: algebra_simps)
  have "a + b = 2 - c" using assms by (simp add: algebra_simps)
  have "c + b = 2 - a" using assms by (simp add: algebra_simps)
  have "a + c = 2 - b" using assms by (simp add: algebra_simps)
  have "a^2 + b^2 + c^2 = 2" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a^2 + (2 - a - c)^2 + c^2 = 2" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a^2 + 4 - 4a - 4c + 2ac + c^2 = 2" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "2ac = 2a + 2c" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "2ac - 2a - 2c = 0" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "(a - c)^2 = 0" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a - c = 0" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = c" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "b = 1 - a" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "1 - a = b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "1 - b = a" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "1 - a = b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpbpowon2_3d assms by (metis (no_types) assms(2) le_add_diff_inverse2)
  have "a = 1 - b" using algebra_apbon2pownleqapownpb
