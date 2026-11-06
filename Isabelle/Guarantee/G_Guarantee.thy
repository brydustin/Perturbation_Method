theory G_Guarantee
  imports G_Discrete
begin

section \<open>The guarantee at a stop\<close>

text \<open>Walking through neighbouring samples above \<open>th\<close>, the true pattern stays above
  \<open>th - Hc h\<^sup>2/8\<close> between them (Fact 2, lower form).\<close>

text \<open>A point between \<open>x\<close> and \<open>y\<close> is between \<open>x\<close> and \<open>z\<close> or between \<open>z\<close> and \<open>y\<close>.\<close>
lemma between_split:
  fixes x y z \<theta> :: real
  assumes "min x y \<le> \<theta>" "\<theta> \<le> max x y"
  shows "(min x z \<le> \<theta> \<and> \<theta> \<le> max x z) \<or> (min z y \<le> \<theta> \<and> \<theta> \<le> max z y)"
  using assms unfolding min_def max_def by (smt (verit))

lemma walk_arc:
  assumes w: "(j, q) \<in> (step p N c th)\<^sup>*" and j: "j \<in> above p N c th" and x: "lift j x"
  shows "\<exists>y. lift q y \<and> (\<forall>\<theta>. min x y \<le> \<theta> \<and> \<theta> \<le> max x y \<longrightarrow> pw p N c \<theta> > th - Hc c p N * hM\<^sup>2 / 8)"
  using w j x
proof (induction arbitrary: x rule: converse_rtrancl_induct)
  case base
  have "pw p N c x = sq p N c q" by (rule pw_lift [OF base.prems(2)])
  then have "pw p N c x > th" using base.prems(1) by (simp add: above_def)
  moreover have "0 \<le> Hc c p N * hM\<^sup>2 / 8" using Hc_ge0 [of c p N] by simp
  ultimately have "\<forall>\<theta>. min x x \<le> \<theta> \<and> \<theta> \<le> max x x \<longrightarrow> pw p N c \<theta> > th - Hc c p N * hM\<^sup>2 / 8"
    by (auto simp: antisym)
  with base.prems(2) show ?case by blast
next
  case (step j j')
  from step.hyps(1) have jA: "j \<in> above p N c th" and j'A: "j' \<in> above p N c th"
    and nb: "j' = next_idx j \<or> j' = prev_idx j" by (auto simp: step_def)
  have jM: "j < M" using jA by (simp add: above_def)
  obtain x' where x': "lift j' x'" and dx: "\<bar>x' - x\<bar> = hM"
  proof (cases "j' = next_idx j")
    case True
    then show ?thesis using that [of "x + hM"] lift_next [OF jM step.prems(2)] hM_pos by auto
  next
    case False
    then have "j' = prev_idx j" using nb by simp
    then show ?thesis using that [of "x - hM"] lift_prev [OF jM step.prems(2)] hM_pos by auto
  qed
  have px: "pw p N c x > th" using pw_lift [OF step.prems(2)] jA by (simp add: above_def)
  have px': "pw p N c x' > th" using pw_lift [OF x'] j'A by (simp add: above_def)
  have cell: "pw p N c \<theta> > th - Hc c p N * hM\<^sup>2 / 8" if th1: "min x x' \<le> \<theta>" and th2: "\<theta> \<le> max x x'" for \<theta>
  proof -
    have "pw p N c \<theta> \<ge> min (pw p N c (min x x')) (pw p N c (max x x'))
                       - Hc c p N * (max x x' - min x x')\<^sup>2 / 8"
      by (rule pw_cell_min [OF th1 th2])
    moreover have "(max x x' - min x x')\<^sup>2 = hM\<^sup>2" using dx by (auto simp: abs_if min_def max_def)
    ultimately have "pw p N c \<theta> \<ge> min (pw p N c (min x x')) (pw p N c (max x x')) - Hc c p N * hM\<^sup>2 / 8"
      by simp
    moreover have "min (pw p N c (min x x')) (pw p N c (max x x')) > th"
      using px px' by (auto simp: min_def max_def)
    ultimately show ?thesis by linarith
  qed
  obtain y where y: "lift q y"
    and arc: "\<forall>\<theta>. min x' y \<le> \<theta> \<and> \<theta> \<le> max x' y \<longrightarrow> pw p N c \<theta> > th - Hc c p N * hM\<^sup>2 / 8"
    using step.IH [OF j'A x'] by blast
  have "\<forall>\<theta>. min x y \<le> \<theta> \<and> \<theta> \<le> max x y \<longrightarrow> pw p N c \<theta> > th - Hc c p N * hM\<^sup>2 / 8"
  proof (intro allI impI)
    fix \<theta> assume "min x y \<le> \<theta> \<and> \<theta> \<le> max x y"
    then have "(min x x' \<le> \<theta> \<and> \<theta> \<le> max x x') \<or> (min x' y \<le> \<theta> \<and> \<theta> \<le> max x' y)"
      by (intro between_split) auto
    then show "pw p N c \<theta> > th - Hc c p N * hM\<^sup>2 / 8" using cell arc by blast
  qed
  with y show ?case by blast
qed

text \<open>The main theorem.  If the changed test finds nothing eligible and the margin \<open>dl\<close> covers
  \<open>Hc h\<^sup>2/8\<close>, then every direction where the true pattern is above \<open>-20\<close> dB (relative to the
  largest sample) is joined to the main peak, or to a peak inside the band, by an arc on which the
  true pattern stays above \<open>-20\<close> dB less \<open>2 dl\<close>.\<close>

theorem guarantee_at_stop:
  assumes stop: "gelig p N dl band tm c t = {}" and tr: "tie_rule tm ts"
    and dl: "Hc c p N * hM\<^sup>2 / 8 \<le> dl"
    and phi: "pw p N c \<phi> > sqmax p N c / 100"
  shows "\<exists>q y. lift q y \<and> (q = tm (fmains p N c t) mod M \<or> (q < M \<and> \<not> in_band band t q))
           \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow> pw p N c \<theta> > sqmax p N c / 100 - 2 * dl)"
proof -
  define m0 where "m0 = tm (fmains p N c t)"
  define th where "th = sqmax p N c / 100 - dl"
  define X where "X = {q. q < M \<and> \<not> in_band band t q}"
  define de where "de = Hc c p N * hM\<^sup>2 / 8"
  have de0: "0 \<le> de" using Hc_ge0 [of c p N] by (simp add: de_def)
  have dde: "de \<le> dl" using dl by (simp add: de_def)
  have stop': "q = m0 \<or> q = prev_idx m0 \<or> q = next_idx m0 \<or> q \<in> X"
    if "q \<in> fpeaks p N c" "sq p N c q > th" for q
  proof -
    have "q \<notin> geligible p N dl band c t m0" using stop by (simp add: gelig_def m0_def)
    with that show ?thesis by (auto simp: geligible_def th_def X_def fpeaks_def)
  qed
  have m0P: "fpeaks p N c \<noteq> {} \<Longrightarrow> m0 \<in> fpeaks p N c"
    unfolding m0_def by (rule main_in_fpeaks [OF tr])
  text \<open>The grid cell \<open>[a, a + h]\<close> that contains \<open>\<phi>\<close>.\<close>
  define z where "z = \<lfloor>\<phi> / (2 * pi)\<rfloor>"
  define \<phi>0 where "\<phi>0 = \<phi> - 2 * pi * of_int z"
  have zfl: "of_int z \<le> \<phi> / (2 * pi)" "\<phi> / (2 * pi) < of_int z + 1"
    unfolding z_def by linarith+
  have p0: "0 \<le> \<phi>0" "\<phi>0 < 2 * pi"
  proof -
    have "2 * pi * of_int z \<le> 2 * pi * (\<phi> / (2 * pi))" using zfl(1) by (intro mult_left_mono) auto
    then show "0 \<le> \<phi>0" by (simp add: \<phi>0_def)
    have "2 * pi * (\<phi> / (2 * pi)) < 2 * pi * (of_int z + 1)" using zfl(2) by (intro mult_strict_left_mono) auto
    then show "\<phi>0 < 2 * pi" by (simp add: \<phi>0_def algebra_simps)
  qed
  define m where "m = nat \<lfloor>\<phi>0 / hM\<rfloor>"
  have hM_eq: "hM * real M = 2 * pi" by (simp add: hM_def M_def)
  have q0: "0 \<le> \<phi>0 / hM" using p0 hM_pos by simp
  have qM: "\<phi>0 / hM < real M"
    using p0 hM_pos hM_eq by (simp add: divide_less_eq mult.commute)
  have mfl: "real m \<le> \<phi>0 / hM" "\<phi>0 / hM < real m + 1"
    unfolding m_def using q0 by (simp_all add: of_nat_nat floor_less_cancel)
  have "real m < real M" using mfl(1) qM by linarith
  then have mM: "m < M" by simp
  have gm: "grid m = real m * hM" by (simp add: grid_def hM_def)
  have g1: "grid m \<le> \<phi>0" using mfl(1) hM_pos by (simp add: gm le_divide_eq)
  have g2: "\<phi>0 \<le> grid m + hM" using mfl(2) hM_pos by (simp add: gm divide_less_eq algebra_simps)
  define a where "a = grid m + 2 * pi * of_int z"
  define b where "b = a + hM"
  have ab: "a \<le> \<phi>" "\<phi> \<le> b" using g1 g2 by (simp_all add: a_def b_def \<phi>0_def)
  have la: "lift m a" by (auto simp: lift_def a_def)
  have lb: "lift (next_idx m) b" unfolding b_def by (rule lift_next [OF mM la])
  have up: "pw p N c \<phi> \<le> max (pw p N c a) (pw p N c b) + de"
    using pw_cell_max [OF ab, of p N c] by (simp add: b_def de_def)
  have big: "max (sq p N c m) (sq p N c (next_idx m)) > th"
    using up phi dde pw_lift [OF la] pw_lift [OF lb] by (simp add: th_def)
  obtain je e where je: "je \<in> above p N c th" and le: "lift je e" and ein: "a \<le> e" "e \<le> b"
  proof (cases "sq p N c m > th")
    case True
    then show ?thesis using that [of m a] la mM ab by (auto simp: above_def)
  next
    case False
    then have "sq p N c (next_idx m) > th" using big by (simp add: max_def split: if_splits)
    then show ?thesis using that [of "next_idx m" b] lb ab by (auto simp: above_def idx_next_lt)
  qed
  have seg: "pw p N c \<theta> > th - de" if s1: "min \<phi> e \<le> \<theta>" and s2: "\<theta> \<le> max \<phi> e" for \<theta>
  proof -
    have "pw p N c \<theta> \<ge> min (pw p N c (min \<phi> e)) (pw p N c (max \<phi> e))
                       - Hc c p N * (max \<phi> e - min \<phi> e)\<^sup>2 / 8"
      by (rule pw_cell_min [OF s1 s2])
    moreover have "(max \<phi> e - min \<phi> e)\<^sup>2 \<le> hM\<^sup>2"
      using ab ein by (intro power_mono) (auto simp: b_def min_def max_def)
    then have "Hc c p N * (max \<phi> e - min \<phi> e)\<^sup>2 / 8 \<le> de"
      unfolding de_def using Hc_ge0 [of c p N] by (intro divide_right_mono mult_left_mono) auto
    moreover have "pw p N c \<phi> > th" using phi de0 dde by (simp add: th_def)
    moreover have "pw p N c e > th" using pw_lift [OF le] je by (simp add: above_def)
    then have "min (pw p N c (min \<phi> e)) (pw p N c (max \<phi> e)) > th"
      using \<open>pw p N c \<phi> > th\<close> by (auto simp: min_def max_def)
    ultimately show ?thesis by linarith
  qed
  obtain q where wq: "(je, q) \<in> (step p N c th)\<^sup>*" and q: "q = m0 mod M \<or> q \<in> X"
    using walk_to_main [OF je stop' m0P] by blast
  obtain y where ly: "lift q y"
    and arc: "\<forall>\<theta>. min e y \<le> \<theta> \<and> \<theta> \<le> max e y \<longrightarrow> pw p N c \<theta> > th - de"
    using walk_arc [OF wq je le] unfolding de_def by blast
  have all: "\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow> pw p N c \<theta> > sqmax p N c / 100 - 2 * dl"
  proof (intro allI impI)
    fix \<theta> assume "min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y"
    then have "(min \<phi> e \<le> \<theta> \<and> \<theta> \<le> max \<phi> e) \<or> (min e y \<le> \<theta> \<and> \<theta> \<le> max e y)"
      by (intro between_split) auto
    then have "pw p N c \<theta> > th - de" using seg arc by blast
    then show "pw p N c \<theta> > sqmax p N c / 100 - 2 * dl" using dde by (simp add: th_def)
  qed
  show ?thesis using ly q all by (auto simp: m0_def X_def)
qed

text \<open>Without a band the target is always the main peak.\<close>
corollary guarantee_no_band:
  assumes stop: "gelig p N dl None tm c t = {}" and tr: "tie_rule tm ts"
    and dl: "Hc c p N * hM\<^sup>2 / 8 \<le> dl"
    and phi: "pw p N c \<phi> > sqmax p N c / 100"
  shows "\<exists>y. lift (tm (fmains p N c t)) y
           \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow> pw p N c \<theta> > sqmax p N c / 100 - 2 * dl)"
proof -
  obtain q y where ly: "lift q y" and q: "q = tm (fmains p N c t) mod M"
    and arc: "\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow> pw p N c \<theta> > sqmax p N c / 100 - 2 * dl"
    using guarantee_at_stop [OF stop tr dl phi] by (auto simp: in_band_def)
  define m0 where "m0 = tm (fmains p N c t)"
  have e: "m0 div M * M + m0 mod M = m0" by (rule div_mult_mod_eq)
  have r: "real m0 = real (m0 div M) * real M + real (m0 mod M)"
    by (simp only: of_nat_add [symmetric] of_nat_mult [symmetric] e)
  have g: "grid m0 = grid (m0 mod M) + 2 * pi * real (m0 div M)"
    by (subst grid_def, subst r) (simp add: grid_def M_def field_simps)
  from ly q obtain zz :: int where yz: "y = grid (m0 mod M) + 2 * pi * of_int zz"
    by (auto simp: lift_def m0_def)
  have "y = grid m0 + 2 * pi * of_int (zz - int (m0 div M))"
    using yz g by (simp add: algebra_simps)
  then have "lift m0 y" unfolding lift_def by blast
  with arc show ?thesis by (auto simp: m0_def)
qed

section \<open>Runs of the changed method\<close>

text \<open>Along a run the weights stay in the ball of radius \<open>\<surd>N\<close>, so a fixed margin covers every step:
  \<open>dl \<ge> 2 N\<^sup>2 (G + 2 G\<^sup>2) h\<^sup>2 / 8\<close>, where \<open>G\<close> bounds \<open>k |p\<^sub>j|\<close>.\<close>

theorem grun_guarantee:
  assumes tr: "tie_rule tm ts" and G: "\<And>j. j < N \<Longrightarrow> gam p j \<le> G"
    and dl: "2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2) * hM\<^sup>2 / 8 \<le> dl"
    and stop: "gelig p N dl band tm (grun p N dl band tm ts t n) t = {}"
    and phi: "pw p N (grun p N dl band tm ts t n) \<phi> > sqmax p N (grun p N dl band tm ts t n) / 100"
  shows "\<exists>q y. lift q y \<and> (q = tm (fmains p N (grun p N dl band tm ts t n) t) mod M \<or> (q < M \<and> \<not> in_band band t q))
           \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow>
                pw p N (grun p N dl band tm ts t n) \<theta> > sqmax p N (grun p N dl band tm ts t n) / 100 - 2 * dl)"
proof -
  have "Hc (grun p N dl band tm ts t n) p N \<le> 2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2)"
    by (rule Hc_le_norm [OF G nrm_grun])
  then have "Hc (grun p N dl band tm ts t n) p N * hM\<^sup>2 / 8 \<le> 2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2) * hM\<^sup>2 / 8"
    by (intro divide_right_mono mult_right_mono) auto
  with dl have "Hc (grun p N dl band tm ts t n) p N * hM\<^sup>2 / 8 \<le> dl" by linarith
  then show ?thesis by (rule guarantee_at_stop [OF stop tr _ phi])
qed

text \<open>Stopping within \<open>D\<close> corrections, together with the guarantee at the stop.\<close>
theorem gstops_guarantee:
  assumes st: "gstops_within p N dl band tm ts t D" and tr: "tie_rule tm ts"
    and G: "\<And>j. j < N \<Longrightarrow> gam p j \<le> G"
    and dl: "2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2) * hM\<^sup>2 / 8 \<le> dl"
  shows "\<exists>n \<le> D. gelig p N dl band tm (grun p N dl band tm ts t n) t = {} \<and>
           (\<forall>\<phi>. pw p N (grun p N dl band tm ts t n) \<phi> > sqmax p N (grun p N dl band tm ts t n) / 100 \<longrightarrow>
              (\<exists>q y. lift q y \<and> (q = tm (fmains p N (grun p N dl band tm ts t n) t) mod M \<or> (q < M \<and> \<not> in_band band t q))
                 \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow>
                      pw p N (grun p N dl band tm ts t n) \<theta> > sqmax p N (grun p N dl band tm ts t n) / 100 - 2 * dl)))"
  using st grun_guarantee [OF tr G dl] by (auto simp: gstops_within_def)

ML \<open>writeln ("oracles: " ^ commas (map (#1 o #1) (Thm_Deps.all_oracles
  [@{thm guarantee_at_stop}, @{thm guarantee_no_band}, @{thm grun_guarantee}, @{thm gstops_guarantee}])))\<close>

end
