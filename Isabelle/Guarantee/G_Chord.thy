theory G_Chord
  imports "HOL-Analysis.Analysis"
begin

section \<open>Chord bounds from a bound on the second derivative\<close>

text \<open>If \<open>|f''| \<le> K\<close>, then on \<open>[a, b]\<close> the function stays within \<open>K (x - a) (b - x) / 2\<close>
  of its chord.\<close>

lemma chord_upper:
  fixes f df ddf :: "real \<Rightarrow> real"
  assumes d1: "\<And>t. DERIV f t :> df t" and d2: "\<And>t. DERIV df t :> ddf t"
    and K: "\<And>t. \<bar>ddf t\<bar> \<le> K" and x: "a \<le> x" "x \<le> b"
  shows "f x \<le> f a + (f b - f a) / (b - a) * (x - a) + K / 2 * ((x - a) * (b - x))"
proof (cases "a = b")
  case True
  with x show ?thesis by simp
next
  case False
  with x have ab: "a < b" by simp
  text \<open>\<open>r\<close> is \<open>f\<close> minus its chord minus the parabola; it vanishes at both ends and is convex.\<close>
  define S where "S = (f b - f a) / (b - a)"
  define r where "r t = f t - (f a + S * (t - a)) - K / 2 * ((t - a) * (b - t))" for t
  define r1 where "r1 t = df t - S - K / 2 * ((b - t) - (t - a))" for t
  have dr: "DERIV r t :> r1 t" for t
    unfolding r_def r1_def by (auto intro!: derivative_eq_intros d1 simp: algebra_simps)
  have dr1: "DERIV r1 t :> ddf t + K" for t
    unfolding r1_def by (auto intro!: derivative_eq_intros d2 simp: algebra_simps)
  have mono: "r1 u \<le> r1 v" if uv: "u \<le> v" for u v
  proof (rule DERIV_nonneg_imp_nondecreasing [OF uv])
    fix y
    have "0 \<le> ddf y + K" using K [of y] by (simp add: abs_le_iff)
    then show "\<exists>z. DERIV r1 y :> z \<and> 0 \<le> z" using dr1 [of y] by blast
  qed
  have "convex_on {a..b} r"
    by (rule convex_on_realI [where f' = r1]) (use dr mono in auto)
  then have "r x \<le> (r b - r a) / (b - a) * (x - a) + r a"
    using x by (intro convex_onD_Icc') auto
  moreover have "r a = 0" by (simp add: r_def)
  moreover have "r b = 0" using ab by (simp add: r_def S_def)
  ultimately have "r x \<le> 0" by simp
  then show ?thesis unfolding r_def S_def by linarith
qed

lemma chord_lower:
  fixes f df ddf :: "real \<Rightarrow> real"
  assumes d1: "\<And>t. DERIV f t :> df t" and d2: "\<And>t. DERIV df t :> ddf t"
    and K: "\<And>t. \<bar>ddf t\<bar> \<le> K" and x: "a \<le> x" "x \<le> b"
  shows "f x \<ge> f a + (f b - f a) / (b - a) * (x - a) - K / 2 * ((x - a) * (b - x))"
proof -
  have m1: "DERIV (\<lambda>t. - f t) t :> - df t" for t by (rule DERIV_minus [OF d1])
  have m2: "DERIV (\<lambda>t. - df t) t :> - ddf t" for t by (rule DERIV_minus [OF d2])
  have m3: "\<bar>- ddf t\<bar> \<le> K" for t using K [of t] by simp
  have u: "- f x \<le> - f a + (- f b - - f a) / (b - a) * (x - a) + K / 2 * ((x - a) * (b - x))"
    using chord_upper [OF m1 m2 m3 x] .
  have e1: "(- f b - - f a) / (b - a) = - ((f b - f a) / (b - a))"
    by (simp add: minus_divide_left)
  have e2: "(- f b - - f a) / (b - a) * (x - a) = - ((f b - f a) / (b - a) * (x - a))"
    unfolding e1 by simp
  from u e2 show ?thesis by linarith
qed

text \<open>The forms used below: the function exceeds the larger end value, or falls below the
  smaller, by at most \<open>K (b - a)\<^sup>2 / 8\<close>.\<close>

lemma chord_quad: "(x - a) * (b - x) \<le> (b - a)\<^sup>2 / 4" for a b x :: real
proof -
  have "(b - a)\<^sup>2 - 4 * ((x - a) * (b - x)) = (2 * x - a - b)\<^sup>2"
    by (simp add: power2_eq_square algebra_simps)
  then show ?thesis using zero_le_power2 [of "2 * x - a - b"] by linarith
qed

lemma chord_between:
  fixes u v a b x :: real
  assumes "a \<le> x" "x \<le> b"
  shows "u + (v - u) / (b - a) * (x - a) \<le> max u v \<and> min u v \<le> u + (v - u) / (b - a) * (x - a)"
proof (cases "a = b")
  case True then show ?thesis by simp
next
  case False
  with assms have ab: "a < b" by simp
  define l where "l = (x - a) / (b - a)"
  have l: "0 \<le> l" "l \<le> 1" using assms ab by (simp_all add: l_def field_simps)
  have e0: "(v - u) / (b - a) * (x - a) = l * (v - u)"
    by (simp add: l_def mult.commute)
  have e: "u + (v - u) / (b - a) * (x - a) = (1 - l) * u + l * v"
    unfolding e0 by (simp add: algebra_simps)
  have "(1 - l) * u + l * v \<le> (1 - l) * max u v + l * max u v"
    using l by (intro add_mono mult_left_mono) auto
  moreover have "(1 - l) * min u v + l * min u v \<le> (1 - l) * u + l * v"
    using l by (intro add_mono mult_left_mono) auto
  ultimately show ?thesis unfolding e by (simp add: algebra_simps)
qed

theorem chord_max:
  fixes f df ddf :: "real \<Rightarrow> real"
  assumes d1: "\<And>t. DERIV f t :> df t" and d2: "\<And>t. DERIV df t :> ddf t"
    and K: "\<And>t. \<bar>ddf t\<bar> \<le> K" and x: "a \<le> x" "x \<le> b"
  shows "f x \<le> max (f a) (f b) + K * (b - a)\<^sup>2 / 8"
proof -
  have K0: "0 \<le> K" using K [of 0] by linarith
  have "K / 2 * ((x - a) * (b - x)) \<le> K / 2 * ((b - a)\<^sup>2 / 4)"
    using K0 chord_quad by (intro mult_left_mono) auto
  moreover have "K / 2 * ((b - a)\<^sup>2 / 4) = K * (b - a)\<^sup>2 / 8" by simp
  ultimately show ?thesis
    using chord_upper [OF d1 d2 K x] chord_between [OF x, of "f a" "f b"] by linarith
qed

theorem chord_min:
  fixes f df ddf :: "real \<Rightarrow> real"
  assumes d1: "\<And>t. DERIV f t :> df t" and d2: "\<And>t. DERIV df t :> ddf t"
    and K: "\<And>t. \<bar>ddf t\<bar> \<le> K" and x: "a \<le> x" "x \<le> b"
  shows "f x \<ge> min (f a) (f b) - K * (b - a)\<^sup>2 / 8"
proof -
  have K0: "0 \<le> K" using K [of 0] by linarith
  have "K / 2 * ((x - a) * (b - x)) \<le> K / 2 * ((b - a)\<^sup>2 / 4)"
    using K0 chord_quad by (intro mult_left_mono) auto
  moreover have "K / 2 * ((b - a)\<^sup>2 / 4) = K * (b - a)\<^sup>2 / 8" by simp
  ultimately show ?thesis
    using chord_lower [OF d1 d2 K x] chord_between [OF x, of "f a" "f b"] by linarith
qed

end
