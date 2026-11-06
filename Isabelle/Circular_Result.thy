theory Circular_Result
  imports Circular_Check Fast_Code Double_Cross
begin

section \<open>The two bands, checked by evaluation\<close>

lemma check20: "circ_check 53 20 cert20 chol20 s2_20 (Float 1 (-20)) (Float 6496480 (-20)) (Float 1 (-20)) (Float 6496753 (-20))"
  by eval

lemma check30: "circ_check 53 30 cert30 chol30 s2_30 (Float 1 (-20)) (Float 8149584 (-20)) (Float 1 (-20)) (Float 8153779 (-20))"
  by eval

section \<open>Theorem C.3 and Corollary C.4\<close>

lemma Qset_500: "500 \<in> Qset \<Delta>" if "\<Delta> \<le> 30"
  using that unfolding Qset_def M_def by simp

lemma floor_from_check:
  assumes chk: "circ_check p \<Delta> certs C s2 \<delta> Lam e K" and \<Delta>: "\<Delta> \<le> 30"
    and v: "v * real_of_float K \<le> 1" and v0: "0 \<le> v"
  shows "v * maxAll cv \<le> maxQ \<Delta> cv"
proof -
  have mq: "0 \<le> maxQ \<Delta> cv" by (rule maxQ_nonneg) (use Qset_500 [OF \<Delta>] in blast)
  have "v * maxAll cv \<le> v * (real_of_float K * maxQ \<Delta> cv)" by (rule mult_left_mono [OF circ_check_sound(1) [OF chk] v0])
  also have "\<dots> = (v * real_of_float K) * maxQ \<Delta> cv" by (simp add: mult.assoc)
  also have "\<dots> \<le> 1 * maxQ \<Delta> cv" by (rule mult_right_mono [OF v mq])
  finally show ?thesis by simp
qed

lemma no_stop_from_check:
  assumes chk: "circ_check p \<Delta> certs C s2 \<delta> Lam e K" and \<Delta>: "\<Delta> \<le> 30"
    and v: "v * real_of_float K \<le> 1" and v1: "1/10 < v" and nz: "\<exists>j<32. cv j \<noteq> 0"
  shows "\<not> maxQ \<Delta> cv \<le> 1/10 * maxAll cv"
proof
  assume S: "maxQ \<Delta> cv \<le> 1/10 * maxAll cv"
  have fl: "v * maxAll cv \<le> maxQ \<Delta> cv" by (rule floor_from_check [OF chk \<Delta> v]) (use v1 in simp)
  have mq: "0 \<le> maxQ \<Delta> cv" by (rule maxQ_nonneg) (use Qset_500 [OF \<Delta>] in blast)
  have "maxAll cv \<le> 0"
  proof (rule ccontr)
    assume "\<not> maxAll cv \<le> 0"
    then have "1/10 * maxAll cv < v * maxAll cv" using v1 by simp
    with fl S show False by linarith
  qed
  then have mq0: "maxQ \<Delta> cv = 0" using S mq by linarith
  have F0: "(cmod (Fc cv q))\<^sup>2 = 0" if "q \<in> Qset \<Delta>" for q
    using maxQ_ge [OF that, of cv] mq0 by simp
  have "(\<Sum>q\<in>Qset \<Delta>. (cmod (Fc cv q))\<^sup>2) = 0" by (simp add: F0)
  with circ_check_sound(2) [OF chk, of cv] circ_check_sound(3) [OF chk]
  have "(\<Sum>j<32. (cmod (cv j))\<^sup>2) \<le> 0" by (simp add: mult_le_0_iff)
  then have "\<forall>j<32. (cmod (cv j))\<^sup>2 = 0" using sum_nonneg_eq_0_iff [of "{..<32}" "\<lambda>j. (cmod (cv j))\<^sup>2"]
    by (simp add: order_antisym sum_nonneg)
  with nz show False by simp blast
qed

lemma K20: "1614 / 10000 * real_of_float (Float 6496753 (-20)) \<le> 1"
proof -
  have "Float 6496753 (-20) * Float 1614 0 \<le> Float 10000 0" by eval
  then show ?thesis unfolding less_eq_float.rep_eq times_float.rep_eq real_of_Float_int by simp
qed

lemma K30: "1286 / 10000 * real_of_float (Float 8153779 (-20)) \<le> 1"
proof -
  have "Float 8153779 (-20) * Float 1286 0 \<le> Float 10000 0" by eval
  then show ?thesis unfolding less_eq_float.rep_eq times_float.rep_eq real_of_Float_int by simp
qed

text \<open>Theorem C.3: for every excitation, the largest grid sidelobe outside the band is at least
  \<open>v\<^sub>\<Delta>\<close> times the pattern maximum (\<open>v\<^sub>2\<^sub>0 = 0.1614\<close>, \<open>v\<^sub>3\<^sub>0 = 0.1286\<close>, i.e. \<open>-15.84\<close> and \<open>-17.81\<close> dB).\<close>

theorem circular_floor_20: "1614 / 10000 * maxAll cv \<le> maxQ 20 cv"
  by (rule floor_from_check [OF check20 _ K20]) simp_all

theorem circular_floor_30: "1286 / 10000 * maxAll cv \<le> maxQ 30 cv"
  by (rule floor_from_check [OF check30 _ K30]) simp_all

text \<open>Corollary C.4: no nonzero excitation meets the specified stopping test (S)
  \<open>max\<^sub>Q |F| \<le> 0.1 max |F|\<close>, so a method stopping on (S) never stops on this array.\<close>

theorem circular_cannot_stop_20: "\<exists>j<32. cv j \<noteq> 0 \<Longrightarrow> \<not> maxQ 20 cv \<le> 1/10 * maxAll cv"
  by (rule no_stop_from_check [OF check20 _ K20]) simp_all

theorem circular_cannot_stop_30: "\<exists>j<32. cv j \<noteq> 0 \<Longrightarrow> \<not> maxQ 30 cv \<le> 1/10 * maxAll cv"
  by (rule no_stop_from_check [OF check30 _ K30]) simp_all

end
