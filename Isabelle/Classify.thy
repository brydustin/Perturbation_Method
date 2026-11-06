theory Classify
  imports Sector_Bounds
begin

section \<open>The data of a node\<close>

text \<open>A node: precision \<open>p\<close>, float positions \<open>q\<close>, \<open>N\<close> elements with \<open>1/N \<in> IN\<close>, corrections \<open>\<sigma>\<close>,
  sector \<open>[lo, hi]\<close>, and an integer \<open>n0 m\<close> per grid index for the distance reduction.\<close>

text \<open>The node data are given as parameters: \<open>R m j\<close> encloses \<open>rows \<sigma> m j\<close> and \<open>Hb m\<close> bounds
  the curvature constant of row \<open>m\<close>.  The reference instances are \<open>rows_ivl\<close> and \<open>upper (Hc_ivl ...)\<close>.\<close>

definition LOB where "LOB p q N R Hb lo hi m = lo_b p q N (R m) (Hb m) lo hi"
definition UPB where "UPB p q N R Hb lo hi m = up_b p q N (R m) (Hb m) lo hi"
definition DP where "DP p q N R Hb lo hi m = diff_b p q N (R m) (R (prev_idx m))
                                                  (Hb m) (Hb (prev_idx m)) lo hi"
definition DN where "DN p q N R Hb lo hi m = diff_b p q N (R m) (R (next_idx m))
                                                  (Hb m) (Hb (next_idx m)) lo hi"
definition CD where "CD p lo hi n0 m = cd_ivl p (grid_ivl p m) (tc lo hi) (n0 m)"
definition dist_ok where "dist_ok p lo hi n0 m \<longleftrightarrow> upper (abs_interval (w_ivl p (grid_ivl p m) (tc lo hi) (n0 m))) \<le> lower (twopi_ivl p)"
definition DMIN where "DMIN p lo hi n0 m = dmin_b (CD p lo hi n0 m) lo hi"
definition DMAX where "DMAX p lo hi n0 m = dmax_b (CD p lo hi n0 m) lo hi"

subsection \<open>Correctness of the per-index data\<close>

text \<open>The reference instances.\<close>
lemma cin_rows_ivl: "1 / real N \<in>\<^sub>r IN \<Longrightarrow> cin (rows (fpos q) N \<sigma> m j) (rows_ivl p q N IN \<sigma> m j)"
  by (simp add: cin_rows)

lemma Hc_ivl_bound: "1 / real N \<in>\<^sub>r IN \<Longrightarrow> Hc (rows (fpos q) N \<sigma> m) (fpos q) N \<le> real_of_float (upper (Hc_ivl p q N (rows_ivl p q N IN \<sigma> m)))"
  by (intro in_real_upper Hc_in cin_rows_ivl)

text \<open>The squared pattern after corrections \<open>\<sigma>\<close> at focus \<open>t\<close>, index \<open>m\<close>.\<close>
abbreviation SQ :: "(nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "SQ q N \<sigma> t m \<equiv> sq (fpos q) N (exc (fpos q) N (c0 (fpos q) t) \<sigma>) m"

lemma SQ_SS: "SQ q N \<sigma> t m = SS (rows (fpos q) N \<sigma> m) (fpos q) N t"
  by (rule sq_exc_SS)

text \<open>Node data \<open>R, Hb\<close> are valid for \<open>\<sigma>\<close> if they enclose the rows and bound the curvature.\<close>
definition node_ok :: "(nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> float) \<Rightarrow> bool" where
  "node_ok q N \<sigma> R Hb \<longleftrightarrow> (\<forall>m < M. (\<forall>j < N. cin (rows (fpos q) N \<sigma> m j) (R m j)) \<and> Hc (rows (fpos q) N \<sigma> m) (fpos q) N \<le> real_of_float (Hb m))"

lemma node_ok_ref: "1 / real N \<in>\<^sub>r IN \<Longrightarrow> node_ok q N \<sigma> (rows_ivl p q N IN \<sigma>) (\<lambda>m. upper (Hc_ivl p q N (rows_ivl p q N IN \<sigma> m)))"
  by (simp add: node_ok_def cin_rows_ivl Hc_ivl_bound)

lemma SQ_bounds:
  assumes ok: "node_ok q N \<sigma> R Hb" and m: "m < M" and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "real_of_float (LOB p q N R Hb lo hi m) \<le> SQ q N \<sigma> t m" "SQ q N \<sigma> t m \<le> real_of_float (UPB p q N R Hb lo hi m)"
  unfolding SQ_SS LOB_def UPB_def using ok m by (intro SS_sector t; simp add: node_ok_def)+

lemma prev_lt: "prev_idx m < M" and next_lt: "next_idx m < M"
  by (simp_all add: prev_idx_def next_idx_def M_def)

lemma DP_in:
  assumes ok: "node_ok q N \<sigma> R Hb" and m: "m < M" and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "SQ q N \<sigma> t m - SQ q N \<sigma> t (prev_idx m) \<in>\<^sub>r DP p q N R Hb lo hi m"
  unfolding SQ_SS DP_def using ok m prev_lt [of m] by (intro SS_diff_sector t; simp add: node_ok_def)

lemma DN_in:
  assumes ok: "node_ok q N \<sigma> R Hb" and m: "m < M" and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "SQ q N \<sigma> t m - SQ q N \<sigma> t (next_idx m) \<in>\<^sub>r DN p q N R Hb lo hi m"
  unfolding SQ_SS DN_def using ok m next_lt [of m] by (intro SS_diff_sector t; simp add: node_ok_def)

lemma dist_bounds:
  assumes ok: "dist_ok p lo hi n0 m" and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "real_of_float (DMIN p lo hi n0 m) \<le> cdist (grid m) t" "cdist (grid m) t \<le> real_of_float (DMAX p lo hi n0 m)"
proof -
  have cd: "cdist (grid m) (real_of_float (tc lo hi)) \<in>\<^sub>r CD p lo hi n0 m"
    unfolding CD_def by (intro cd_in grid_in ok [unfolded dist_ok_def])
  show "real_of_float (DMIN p lo hi n0 m) \<le> cdist (grid m) t" "cdist (grid m) t \<le> real_of_float (DMAX p lo hi n0 m)"
    unfolding DMIN_def DMAX_def by (rule dist_sector [OF cd t])+
qed

section \<open>The index sets\<close>

text \<open>All predicates range over \<open>m < M\<close>.  \<open>band\<close> is \<open>None\<close> or \<open>Some D\<close> with \<open>D\<close> enclosing the half-width.\<close>

definition PP where "PP p q N R Hb lo hi m \<longleftrightarrow> m < M \<and> 0 < upper (DP p q N R Hb lo hi m) \<and> 0 < upper (DN p q N R Hb lo hi m)"
definition CP where "CP p q N R Hb lo hi m \<longleftrightarrow> m < M \<and> 0 < lower (DP p q N R Hb lo hi m) \<and> 0 < lower (DN p q N R Hb lo hi m)"
definition PO where "PO p lo hi n0 band m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some D \<Rightarrow> lower D < DMAX p lo hi n0 m)"
definition CO where "CO p lo hi n0 band m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some D \<Rightarrow> upper D < DMIN p lo hi n0 m)"
definition PM where "PM p q N R Hb lo hi n0 m \<longleftrightarrow> PP p q N R Hb lo hi m \<and>
   (\<forall>k < M. CP p q N R Hb lo hi k \<longrightarrow> DMIN p lo hi n0 m \<le> DMAX p lo hi n0 k)"

text \<open>Excluded: \<open>m\<close> lies in a run of one or two adjacent possible peaks that is nearer to every focus
  in the sector than every possible peak outside the run.\<close>
definition run_ok where "run_ok p q N R Hb lo hi n0 RS \<longleftrightarrow>
   (\<forall>r \<in> RS. PP p q N R Hb lo hi r) \<and>
   (\<forall>r \<in> RS. \<forall>k < M. PP p q N R Hb lo hi k \<and> k \<notin> RS \<longrightarrow> DMAX p lo hi n0 r < DMIN p lo hi n0 k)"
definition EXC where "EXC p q N R Hb lo hi n0 m \<longleftrightarrow> m < M \<and>
   (run_ok p q N R Hb lo hi n0 {m} \<or> run_ok p q N R Hb lo hi n0 {m, next_idx m} \<or> run_ok p q N R Hb lo hi n0 {prev_idx m, m})"

definition GL where "GL p q N R Hb lo hi = Max ((LOB p q N R Hb lo hi) ` {..<M})"
definition US where "US p q N R Hb lo hi n0 band =
   Max (insert 0 ((UPB p q N R Hb lo hi) ` {m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}))"

definition inv100_ivl :: "float interval" where
  "inv100_ivl = Ivl (Float 11529215046068469 (-60)) (Float 11529215046068470 (-60))"

lemma inv100_in: "1 / 100 \<in>\<^sub>r inv100_ivl"
  unfolding inv100_ivl_def by (intro in_real_intervalI) (simp_all add: Ivl_simps real_of_float_eq)

definition TH where "TH p q N R Hb lo hi = mult_float_interval p (interval_of (GL p q N R Hb lo hi)) inv100_ivl"

definition terminal where "terminal p q N R Hb lo hi n0 band \<longleftrightarrow> US p q N R Hb lo hi n0 band \<le> lower (TH p q N R Hb lo hi)"

definition LL where "LL p q N R Hb lo hi n0 band =
   Max (insert 0 ((LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}))"

definition cand where "cand p q N R Hb lo hi n0 band m \<longleftrightarrow>
   PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m \<and>
   lower (TH p q N R Hb lo hi) \<le> UPB p q N R Hb lo hi m \<and>
   \<not> (0 < LL p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi m < LL p q N R Hb lo hi n0 band)"

section \<open>Soundness (Lemmas 5.1 and 5.2)\<close>

text \<open>The band of the algorithm is enclosed by the band of the checker.\<close>
definition band_in :: "real option \<Rightarrow> float interval option \<Rightarrow> bool" where
  "band_in bd band \<longleftrightarrow> (case (bd, band) of (None, None) \<Rightarrow> True | (Some \<Delta>, Some D) \<Rightarrow> \<Delta> \<in>\<^sub>r D | _ \<Rightarrow> False)"

context
  fixes p :: nat and q :: "nat \<Rightarrow> float \<times> float" and N :: nat and R :: "nat \<Rightarrow> nat \<Rightarrow> civ" and Hb :: "nat \<Rightarrow> float"
    and \<sigma> :: "nat list" and lo hi :: float and n0 :: "nat \<Rightarrow> int" and band :: "float interval option"
    and bd :: "real option" and t :: real
  assumes nok: "node_ok q N \<sigma> R Hb"
    and ok: "\<And>m. m < M \<Longrightarrow> dist_ok p lo hi n0 m"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
    and bd: "band_in bd band"
begin

abbreviation "c \<equiv> exc (fpos q) N (c0 (fpos q) t) \<sigma>"
abbreviation "S \<equiv> SQ q N \<sigma> t"

lemma S_lo: "m < M \<Longrightarrow> real_of_float (LOB p q N R Hb lo hi m) \<le> S m"
  and S_up: "m < M \<Longrightarrow> S m \<le> real_of_float (UPB p q N R Hb lo hi m)"
  by (rule SQ_bounds [OF nok _ t]; assumption)+

lemma DPl: "m < M \<Longrightarrow> S m - S (prev_idx m) \<in>\<^sub>r DP p q N R Hb lo hi m" by (rule DP_in [OF nok _ t])
lemma DNl: "m < M \<Longrightarrow> S m - S (next_idx m) \<in>\<^sub>r DN p q N R Hb lo hi m" by (rule DN_in [OF nok _ t])

lemma peak_PP: "m \<in> peaks (fpos q) N c \<Longrightarrow> PP p q N R Hb lo hi m"
proof -
  assume "m \<in> peaks (fpos q) N c"
  then have m: "m < M" and d1: "0 < S m - S (prev_idx m)" and d2: "0 < S m - S (next_idx m)"
    by (auto simp: peaks_def is_peak_def)
  from in_real_upper [OF DPl [OF m]] d1 have "0 < real_of_float (upper (DP p q N R Hb lo hi m))" by linarith
  moreover from in_real_upper [OF DNl [OF m]] d2 have "0 < real_of_float (upper (DN p q N R Hb lo hi m))" by linarith
  ultimately show ?thesis using m by (simp add: PP_def)
qed

lemma CP_peak: "CP p q N R Hb lo hi m \<Longrightarrow> m \<in> peaks (fpos q) N c"
proof -
  assume cp: "CP p q N R Hb lo hi m"
  then have m: "m < M" and l1: "0 < real_of_float (lower (DP p q N R Hb lo hi m))" and l2: "0 < real_of_float (lower (DN p q N R Hb lo hi m))"
    by (simp_all add: CP_def)
  from in_real_lower [OF DPl [OF m]] l1 have "0 < S m - S (prev_idx m)" by linarith
  moreover from in_real_lower [OF DNl [OF m]] l2 have "0 < S m - S (next_idx m)" by linarith
  ultimately show ?thesis using m by (simp add: peaks_def is_peak_def)
qed

lemma d_lo: "m < M \<Longrightarrow> real_of_float (DMIN p lo hi n0 m) \<le> cdist (grid m) t"
  and d_up: "m < M \<Longrightarrow> cdist (grid m) t \<le> real_of_float (DMAX p lo hi n0 m)"
  by (rule dist_bounds [OF ok [of m] t]; assumption)+

lemma inband_PO: "m < M \<Longrightarrow> in_band bd t m \<Longrightarrow> PO p lo hi n0 band m"
  using bd d_up [of m] unfolding in_band_def PO_def band_in_def
  by (cases bd; cases band) (auto simp: in_real_lower dest: in_real_lower [THEN order_trans] intro: order.strict_trans1)

lemma CO_inband: "m < M \<Longrightarrow> CO p lo hi n0 band m \<Longrightarrow> in_band bd t m"
  using bd d_lo [of m] unfolding in_band_def CO_def band_in_def
  by (cases bd; cases band) (auto dest: in_real_upper intro: order.strict_trans2)

lemma main_PM: "m0 \<in> mains (fpos q) N c t \<Longrightarrow> PM p q N R Hb lo hi n0 m0"
proof -
  assume m0: "m0 \<in> mains (fpos q) N c t"
  then have pk: "m0 \<in> peaks (fpos q) N c" by (simp add: mains_def)
  have "DMIN p lo hi n0 m0 \<le> DMAX p lo hi n0 k" if "k < M" "CP p q N R Hb lo hi k" for k
  proof -
    have "k \<in> peaks (fpos q) N c" by (rule CP_peak [OF that(2)])
    with m0 have "cdist (grid m0) t \<le> cdist (grid k) t" by (simp add: mains_def)
    with d_lo [of m0] d_up [of k] pk that(1) show ?thesis by (simp add: peaks_def; linarith)
  qed
  with peak_PP [OF pk] show ?thesis by (simp add: PM_def)
qed

text \<open>Nothing in an excluded run is eligible (Lemma 5.1(d)).\<close>
lemma EX_not_elig:
  assumes ex: "EXC p q N R Hb lo hi n0 m" and m0: "m0 \<in> mains (fpos q) N c t"
  shows "m \<notin> eligible (fpos q) N bd c t m0"
proof
  assume el: "m \<in> eligible (fpos q) N bd c t m0"
  then have pk: "m \<in> peaks (fpos q) N c" and ne: "m \<noteq> m0" by (simp_all add: eligible_def)
  from ex obtain RS where RS: "run_ok p q N R Hb lo hi n0 RS" "m \<in> RS"
    and R2: "RS = {m} \<or> RS = {m, next_idx m} \<or> RS = {prev_idx m, m}" by (auto simp: EXC_def)
  have mM: "m < M" using pk by (simp add: peaks_def)
  text \<open>No other index of the run is a strict peak (adjacent samples).\<close>
  have only: "r \<in> RS \<Longrightarrow> r \<in> peaks (fpos q) N c \<Longrightarrow> r = m" for r
  proof -
    assume rR: "r \<in> RS" and rp: "r \<in> peaks (fpos q) N c"
    have np: "next_idx (prev_idx m) = m"
      unfolding next_idx_def prev_idx_def
      by (simp only: mod_add_left_eq) (simp add: M_def mM [unfolded M_def])
    have pM: "prev_idx m < M" by (simp add: prev_idx_def M_def)
    have nn: "\<not> is_peak (fpos q) N c (next_idx m)"
      using adjacent_not_both_peaks [OF mM] pk by (auto simp: peaks_def)
    have nprev: "\<not> is_peak (fpos q) N c (prev_idx m)"
      using adjacent_not_both_peaks [OF pM] pk np by (auto simp: peaks_def)
    from R2 rR rp nn nprev show "r = m" by (auto simp: peaks_def)
  qed
  text \<open>Every other strict peak is strictly farther than \<open>m\<close>.\<close>
  have far: "k \<in> peaks (fpos q) N c \<Longrightarrow> k \<noteq> m \<Longrightarrow> cdist (grid m) t < cdist (grid k) t" for k
  proof -
    assume k: "k \<in> peaks (fpos q) N c" "k \<noteq> m"
    then have "k \<notin> RS" using only by blast
    moreover have "PP p q N R Hb lo hi k" by (rule peak_PP [OF k(1)])
    ultimately have "DMAX p lo hi n0 m < DMIN p lo hi n0 k" using RS k by (auto simp: run_ok_def peaks_def)
    with d_up [OF mM] d_lo [of k] k(1) show ?thesis by (simp add: peaks_def)
  qed
  have "m0 \<in> peaks (fpos q) N c" "cdist (grid m0) t \<le> cdist (grid m) t" using m0 pk by (auto simp: mains_def)
  with far [of m0] ne show False by auto
qed

lemma GL_le_sqmax: "real_of_float (GL p q N R Hb lo hi) \<le> sqmax (fpos q) N c"
proof -
  have "GL p q N R Hb lo hi \<in> (LOB p q N R Hb lo hi) ` {..<M}"
    unfolding GL_def by (intro Max_in) (auto simp: M_def lessThan_empty_iff)
  then obtain m where m: "m < M" "GL p q N R Hb lo hi = LOB p q N R Hb lo hi m" by auto
  have "real_of_float (LOB p q N R Hb lo hi m) \<le> S m" by (rule S_lo [OF m(1)])
  also have "S m \<le> sqmax (fpos q) N c" unfolding sqmax_def using m(1) by (intro Max_ge) auto
  finally show ?thesis by (simp add: m(2))
qed

lemma TH_le: "real_of_float (lower (TH p q N R Hb lo hi)) \<le> sqmax (fpos q) N c / 100"
proof -
  have "real_of_float (GL p q N R Hb lo hi) * (1 / 100) \<in>\<^sub>r TH p q N R Hb lo hi"
    unfolding TH_def by (intro mult_float_intervalI interval_of inv100_in)
  then have "real_of_float (lower (TH p q N R Hb lo hi)) \<le> real_of_float (GL p q N R Hb lo hi) * (1 / 100)"
    by (rule in_real_lower)
  also have "\<dots> \<le> sqmax (fpos q) N c / 100" using GL_le_sqmax by simp
  finally show ?thesis .
qed

text \<open>Lemma 5.2 (a): every eligible index is a possible peak, possibly outside, not excluded.\<close>
lemma elig_props:
  assumes m0: "m0 \<in> mains (fpos q) N c t" and el: "m \<in> eligible (fpos q) N bd c t m0"
  shows "PP p q N R Hb lo hi m" "PO p lo hi n0 band m" "\<not> EXC p q N R Hb lo hi n0 m"
proof -
  have pk: "m \<in> peaks (fpos q) N c" and ib: "in_band bd t m" using el by (simp_all add: eligible_def)
  show "PP p q N R Hb lo hi m" by (rule peak_PP [OF pk])
  show "PO p lo hi n0 band m" using pk ib by (intro inband_PO) (simp add: peaks_def)
  show "\<not> EXC p q N R Hb lo hi n0 m" using EX_not_elig [OF _ m0] el by blast
qed

lemma PP_lt: "PP p q N R Hb lo hi m \<Longrightarrow> m < M" by (simp add: PP_def)
lemma CP_lt: "CP p q N R Hb lo hi m \<Longrightarrow> m < M" by (simp add: CP_def)

lemma finite_UPB_set: "finite (insert 0 ((UPB p q N R Hb lo hi) ` {m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}))"
proof -
  have sub: "{m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m} \<subseteq> {..<M}"
  proof
    fix m assume "m \<in> {m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}"
    then have "PP p q N R Hb lo hi m" by (simp only: mem_Collect_eq)
    then show "m \<in> {..<M}" using PP_lt by simp
  qed
  show ?thesis by (simp add: finite_subset [OF sub])
qed

lemma terminal_sound:
  assumes m0: "m0 \<in> mains (fpos q) N c t" and trm: "terminal p q N R Hb lo hi n0 band"
  shows "eligible (fpos q) N bd c t m0 = {}"
proof (rule ccontr)
  assume "eligible (fpos q) N bd c t m0 \<noteq> {}"
  then obtain m where el: "m \<in> eligible (fpos q) N bd c t m0" by auto
  have props: "PP p q N R Hb lo hi m" "PO p lo hi n0 band m" "\<not> EXC p q N R Hb lo hi n0 m" by (rule elig_props [OF m0 el])+
  have "S m \<le> real_of_float (UPB p q N R Hb lo hi m)" by (rule S_up [OF PP_lt [OF props(1)]])
  also have "UPB p q N R Hb lo hi m \<le> US p q N R Hb lo hi n0 band"
  proof -
    have "UPB p q N R Hb lo hi m \<in> insert 0 ((UPB p q N R Hb lo hi) ` {m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m})"
      by (intro insertI2 imageI CollectI conjI props)
    then show ?thesis unfolding US_def by (rule Max_ge [OF finite_UPB_set])
  qed
  also have "US p q N R Hb lo hi n0 band \<le> lower (TH p q N R Hb lo hi)" using trm by (simp add: terminal_def)
  also have "real_of_float (lower (TH p q N R Hb lo hi)) \<le> sqmax (fpos q) N c / 100" by (rule TH_le)
  finally have "S m \<le> sqmax (fpos q) N c / 100" by simp
  moreover have "sqmax (fpos q) N c / 100 < S m" using el by (simp add: eligible_def)
  ultimately show False by simp
qed

text \<open>Lemma 5.2 (b): the selected index is a candidate.\<close>
lemma sel_cand:
  assumes m0: "m0 \<in> mains (fpos q) N c t" and s: "s \<in> sel (fpos q) N c (eligible (fpos q) N bd c t m0)"
  shows "cand p q N R Hb lo hi n0 band s"
proof -
  have el: "s \<in> eligible (fpos q) N bd c t m0" using s by (simp add: sel_def)
  have props: "PP p q N R Hb lo hi s" "PO p lo hi n0 band s" "\<not> EXC p q N R Hb lo hi n0 s" by (rule elig_props [OF m0 el])+
  have thr: "lower (TH p q N R Hb lo hi) \<le> UPB p q N R Hb lo hi s"
  proof -
    have "real_of_float (lower (TH p q N R Hb lo hi)) \<le> sqmax (fpos q) N c / 100" by (rule TH_le)
    also have "\<dots> < S s" using el by (simp add: eligible_def)
    also have "S s \<le> real_of_float (UPB p q N R Hb lo hi s)" by (rule S_up [OF PP_lt [OF props(1)]])
    finally show ?thesis by simp
  qed
  have notL: "\<not> (0 < LL p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi s < LL p q N R Hb lo hi n0 band)"
  proof
    assume a: "0 < LL p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi s < LL p q N R Hb lo hi n0 band"
    have sub: "{k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k} \<subseteq> {..<M}"
    proof
      fix k assume "k \<in> {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}"
      then have "CP p q N R Hb lo hi k" by (simp only: mem_Collect_eq)
      then show "k \<in> {..<M}" using CP_lt by simp
    qed
    have fin: "finite (insert 0 ((LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}))"
      by (simp add: finite_subset [OF sub])
    have "LL p q N R Hb lo hi n0 band \<in> insert 0 ((LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k})"
      unfolding LL_def by (intro Max_in fin) simp
    then have "LL p q N R Hb lo hi n0 band \<in> (LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}"
      using a unfolding insert_iff by (elim disjE) simp_all
    then obtain k where kk: "k \<in> {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}"
      and Lk: "LL p q N R Hb lo hi n0 band = LOB p q N R Hb lo hi k" by (rule imageE)
    have k: "CP p q N R Hb lo hi k" "CO p lo hi n0 band k" "\<not> PM p q N R Hb lo hi n0 k"
      using kk [unfolded mem_Collect_eq] by blast+
    have kM: "k < M" using k(1) by (simp add: CP_def)
    have kpk: "k \<in> peaks (fpos q) N c" by (rule CP_peak [OF k(1)])
    have kib: "in_band bd t k" by (rule CO_inband [OF kM k(2)])
    have kne: "k \<noteq> m0" using k(3) main_PM [OF m0] by auto
    have "real_of_float (LOB p q N R Hb lo hi k) \<le> S k" by (rule S_lo [OF kM])
    moreover have "S s \<le> real_of_float (UPB p q N R Hb lo hi s)" by (rule S_up [OF PP_lt [OF props(1)]])
    moreover have "real_of_float (UPB p q N R Hb lo hi s) < real_of_float (LOB p q N R Hb lo hi k)"
      using a Lk by (simp add: less_float.rep_eq)
    ultimately have Sk: "S s < S k" by linarith
    have "sqmax (fpos q) N c / 100 < S s" using el by (simp add: eligible_def)
    with Sk have "k \<in> eligible (fpos q) N bd c t m0" using kpk kib kne by (simp add: eligible_def)
    then have "S k \<le> S s" using s by (simp only: sel_def mem_Collect_eq)
    with Sk show False by simp
  qed
  show ?thesis using props thr notL by (simp add: cand_def)
qed

end

end
