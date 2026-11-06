theory Double_Cross
  imports Exec_Search
begin

section \<open>The three nine-element arrays, positions as exact doubles\<close>

definition double_cross_pos :: "(float \<times> float) list" where
  "double_cross_pos = [(Float 0 0, Float 0 0), (Float (-3041648138404103) (-56), Float 0 0), (Float 3041648138404103 (-56), Float 0 0), (Float 0 0, Float 3041648138404103 (-56)), (Float 0 0, Float (-3041648138404103) (-56)), (Float 5645503481367791 (-57), Float 5645503481367791 (-57)), (Float (-5645503481367791) (-57), Float 5645503481367791 (-57)), (Float (-5645503481367791) (-57), Float (-5645503481367791) (-57)), (Float 5645503481367791 (-57), Float (-5645503481367791) (-57))]"

definition near_octagon_pos :: "(float \<times> float) list" where
  "near_octagon_pos = [(Float 0 0, Float 0 0), (Float 7141401390087967 (-57), Float 0 0), (Float 7877421166571903 (-111), Float 7141401390087967 (-57)), (Float (-7141401390087967) (-57), Float 7877421166571903 (-110)), (Float (-5908065874928927) (-109), Float (-7141401390087967) (-57)), (Float 2497433457657993 (-56), Float 2497433457657993 (-56)), (Float (-2497433457657993) (-56), Float 2497433457657993 (-56)), (Float (-4994866915315987) (-57), Float (-2497433457657993) (-56)), (Float 4994866915315985 (-57), Float (-4994866915315987) (-57))]"

definition octagon_pos :: "(float \<times> float) list" where
  "octagon_pos = [(Float 0 0, Float 0 0), (Float 7032821178101767 (-57), Float 0 0), (Float 969706283524199 (-108), Float 7032821178101767 (-57)), (Float (-7032821178101767) (-57), Float 969706283524199 (-107)), (Float (-2909118850572597) (-108), Float (-7032821178101767) (-57)), (Float 1243238886477031 (-55), Float 4972955545908123 (-57)), (Float (-4972955545908123) (-57), Float 1243238886477031 (-55)), (Float (-4972955545908125) (-57), Float (-4972955545908123) (-57)), (Float 2486477772954061 (-56), Float (-4972955545908125) (-57))]"

definition dc_q :: "nat \<Rightarrow> float \<times> float" where "dc_q j = double_cross_pos ! j"
definition no_q :: "nat \<Rightarrow> float \<times> float" where "no_q j = near_octagon_pos ! j"
definition oc_q :: "nat \<Rightarrow> float \<times> float" where "oc_q j = octagon_pos ! j"

text \<open>\<open>1/9\<close> and \<open>\<pi>/6\<close> as enclosures.\<close>
definition inv9_ivl :: "float interval" where
  "inv9_ivl = Ivl (Float 128102389400760775 (-60)) (Float 128102389400760776 (-60))"

lemma inv9_in: "1 / real 9 \<in>\<^sub>r inv9_ivl"
  unfolding inv9_ivl_def by (intro in_real_intervalI) (simp_all add: Ivl_simps real_of_float_eq)

definition sixth_ivl :: "float interval" where
  "sixth_ivl = Ivl (Float 192153584101141162 (-60)) (Float 192153584101141163 (-60))"

lemma sixth_in: "1 / 6 \<in>\<^sub>r sixth_ivl"
  unfolding sixth_ivl_def by (intro in_real_intervalI) (simp_all add: Ivl_simps real_of_float_eq)

definition band30 :: "nat \<Rightarrow> float interval" where
  "band30 p = mult_float_interval p (pi_ivl p) sixth_ivl"

lemma band30_in: "band_in (Some (pi / 6)) (Some (band30 p))"
  unfolding band_in_def band30_def
  using mult_float_intervalI [OF pi_in sixth_in, of p] by simp

lemma band_none: "band_in None None"
  by (simp add: band_in_def)

section \<open>Memoised constants for the precision in use\<close>

text \<open>The constants derived from \<open>\<pi>\<close> are functions of the precision, so generated code would recompute
  them at every use.  These code equations route the precision \<open>53\<close> through constants, which the
  generated code evaluates once.\<close>

definition pi53 :: "float interval" where "pi53 = pi_float_interval 53"
definition half_pi53 :: "float interval" where "half_pi53 = mult_float_interval 53 (interval_of (Float 1 (-1))) pi53"
definition twopi53 :: "float interval" where "twopi53 = mult_float_interval 53 (interval_of (Float 2 0)) pi53"
definition kw53 :: "float interval" where "kw53 = mult_float_interval 53 (interval_of (Float 20 0)) pi53"
definition inv_M53 :: "float interval" where "inv_M53 = mult_float_interval 53 (interval_of (Float 2 0)) pi53"

lemma pi_ivl_code [code]: "pi_ivl p = (if p = 53 then pi53 else pi_float_interval p)"
  by (simp add: pi_ivl_def pi53_def)
lemma half_pi_ivl_code [code]: "half_pi_ivl p = (if p = 53 then half_pi53 else mult_float_interval p (interval_of (Float 1 (-1))) (pi_ivl p))"
  by (simp add: half_pi_ivl_def half_pi53_def pi53_def pi_ivl_def)
lemma twopi_ivl_code [code]: "twopi_ivl p = (if p = 53 then twopi53 else mult_float_interval p (interval_of (Float 2 0)) (pi_ivl p))"
  by (simp add: twopi_ivl_def twopi53_def pi53_def pi_ivl_def)
lemma kw_ivl_code [code]: "kw_ivl p = (if p = 53 then kw53 else mult_float_interval p (interval_of (Float 20 0)) (pi_ivl p))"
  by (simp add: kw_ivl_def kw53_def pi53_def pi_ivl_def)
lemma grid_ivl_code [code]: "grid_ivl p m = mult_float_interval p (if p = 53 then inv_M53 else mult_float_interval p (interval_of (Float 2 0)) (pi_ivl p))
                    (mult_float_interval p (interval_of (Float (int m) 0)) inv_M_ivl)"
  by (simp add: grid_ivl_def inv_M53_def pi53_def pi_ivl_def)



end
