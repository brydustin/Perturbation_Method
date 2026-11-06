theorem floor_from_certificates:
  fixes Lm :: "nat \<Rightarrow> nat \<Rightarrow> real" and s2 \<delta> \<Lambda> e K :: real and \<Delta> :: nat
  defines "E \<equiv> \<lambda>i k. Gm \<Delta> i k - LLt Lm i k - (if i = k then s2 else 0)"
  assumes Qne: "Qset \<Delta> \<noteq> {}"
    and row: "\<And>i. i < 64 \<Longrightarrow> (\<Sum>k<64. \<bar>E i k\<bar>) \<le> \<delta>" and col: "\<And>k. k < 64 \<Longrightarrow> (\<Sum>i<64. \<bar>E i k\<bar>) \<le> \<delta>"
    and pos: "0 < s2 - \<delta>" and e0: "0 \<le> e" and LK: "\<Lambda> \<le> K" and K1: "1 \<le> K"
    and KK: "e\<^sup>2 * real (card (Qset \<Delta>)) \<le> (K - \<Lambda>)\<^sup>2 * (s2 - \<delta>)"
    and cert: "\<And>\<psi>. \<psi> < M \<Longrightarrow> \<psi> \<notin> Qset \<Delta> \<Longrightarrow> \<exists>\<mu>. certificate \<Delta> \<psi> \<mu> \<Lambda> e"
  shows "maxAll c \<le> K * maxQ \<Delta> c"
