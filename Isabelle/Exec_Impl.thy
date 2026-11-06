theory Exec_Impl
  imports Exec_Node
begin

section \<open>Memoised node data\<close>

definition Rf :: "civ list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> civ" where "Rf rl m j = rl ! m ! j"
definition Hbf :: "float list \<Rightarrow> nat \<Rightarrow> float" where "Hbf hl m = hl ! m"

text \<open>The initial excitation and its derivative factor at the midpoint, computed once per node.\<close>
definition c0L :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> civ list" where
  "c0L p q N X = map (c0_ivl p q X) [0..<N]"
definition c0pL :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> civ list" where
  "c0pL p q N X = map (\<lambda>j. cscale p (- psi1_ivl p q X j) (imul (c0_ivl p q X j))) [0..<N]"

definition FFi :: "nat \<Rightarrow> nat \<Rightarrow> civ list \<Rightarrow> civ list \<Rightarrow> civ" where
  "FFi p N RL CL = csum p (map (\<lambda>j. cmul p (RL ! j) (CL ! j)) [0..<N])"

lemma FFi_c0: "FFi p N (rl ! m) (c0L p q N X) = FF_ivl p q N (Rf rl m) X"
  unfolding FFi_def FF_ivl_def c0L_def Rf_def by (intro arg_cong [where f = "csum p"] map_upt_cong) simp

lemma FFi_c0p: "FFi p N (rl ! m) (c0pL p q N X) = FF1_ivl p q N (Rf rl m) X"
  unfolding FFi_def FF1_ivl_def c0pL_def Rf_def by (intro arg_cong [where f = "csum p"] map_upt_cong) simp

definition SSi :: "nat \<Rightarrow> nat \<Rightarrow> civ list \<Rightarrow> civ list \<Rightarrow> float interval" where
  "SSi p N RL CL = cnorm2 p (FFi p N RL CL)"
definition SS1i :: "nat \<Rightarrow> nat \<Rightarrow> civ list \<Rightarrow> civ list \<Rightarrow> civ list \<Rightarrow> float interval" where
  "SS1i p N RL CL CPL = interval_of (Float 2 0) * inner_ivl p (FFi p N RL CL) (FFi p N RL CPL)"

lemma SSi_eq: "SSi p N (rl ! m) (c0L p q N X) = SS_ivl p q N (Rf rl m) X"
  unfolding SSi_def SS_ivl_def FFi_c0 ..
lemma SS1i_eq: "SS1i p N (rl ! m) (c0L p q N X) (c0pL p q N X) = SS1_ivl p q N (Rf rl m) X"
  unfolding SS1i_def SS1_ivl_def FFi_c0 FFi_c0p ..

text \<open>Per-node lists.  \<open>X\<close> is the midpoint interval; \<open>CL\<close>, \<open>CPL\<close> are \<open>c0L\<close> and \<open>c0pL\<close>.\<close>
definition sqL :: "nat \<Rightarrow> nat \<Rightarrow> civ list list \<Rightarrow> civ list \<Rightarrow> float interval list" where
  "sqL p N rl CL = map (\<lambda>m. SSi p N (rl ! m) CL) [0..<M]"
definition s1L :: "nat \<Rightarrow> nat \<Rightarrow> civ list list \<Rightarrow> civ list \<Rightarrow> civ list \<Rightarrow> float interval list" where
  "s1L p N rl CL CPL = map (\<lambda>m. SS1i p N (rl ! m) CL CPL) [0..<M]"
definition radL :: "nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float list" where
  "radL p Ds hl lo hi = map (\<lambda>m. upper (radius_ivl p (Ds ! m) (hl ! m) (hw lo hi))) [0..<M]"
definition lobL :: "float interval list \<Rightarrow> float list \<Rightarrow> float list" where
  "lobL Qs RD = map (\<lambda>m. lower (Qs ! m) - RD ! m) [0..<M]"
definition upbL :: "float interval list \<Rightarrow> float list \<Rightarrow> float list" where
  "upbL Qs RD = map (\<lambda>m. upper (Qs ! m) + RD ! m) [0..<M]"
definition diffL :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float interval list" where
  "diffL p nb Qs Ds hl lo hi = map (\<lambda>m. (Qs ! m - Qs ! nb m) +
       Ivl (- upper (radius_ivl p (Ds ! m - Ds ! nb m) (hl ! m + hl ! nb m) (hw lo hi)))
           (upper (radius_ivl p (Ds ! m - Ds ! nb m) (hl ! m + hl ! nb m) (hw lo hi)))) [0..<M]"
definition cdL :: "nat \<Rightarrow> float interval list \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> float interval list" where
  "cdL p gridL lo hi n0 = map (\<lambda>m. cd_ivl p (gridL ! m) (tc lo hi) (n0 m)) [0..<M]"

text \<open>Correctness of the lists against the abstract per-index functions, for \<open>m < M\<close>.\<close>

lemma sqL_nth: "m < M \<Longrightarrow> sqL p N rl (c0L p q N X) ! m = SS_ivl p q N (Rf rl m) X"
  by (simp add: sqL_def SSi_eq)
lemma s1L_nth: "m < M \<Longrightarrow> s1L p N rl (c0L p q N X) (c0pL p q N X) ! m = SS1_ivl p q N (Rf rl m) X"
  by (simp add: s1L_def SS1i_eq)

abbreviation "Xc lo hi \<equiv> interval_of (tc lo hi)"

lemma radL_nth: "m < M \<Longrightarrow> radL p (s1L p N rl (c0L p q N (Xc lo hi)) (c0pL p q N (Xc lo hi))) hl lo hi ! m
                         = rad p q N (Rf rl m) (Hbf hl m) lo hi"
  by (simp add: radL_def rad_def s1L_nth Hbf_def)

lemma lobL_nth: "m < M \<Longrightarrow> lobL (sqL p N rl (c0L p q N (Xc lo hi))) (radL p (s1L p N rl (c0L p q N (Xc lo hi)) (c0pL p q N (Xc lo hi))) hl lo hi) ! m
                         = LOB p q N (Rf rl) (Hbf hl) lo hi m"
  by (simp add: lobL_def LOB_def lo_b_def sqL_nth radL_nth)

lemma upbL_nth: "m < M \<Longrightarrow> upbL (sqL p N rl (c0L p q N (Xc lo hi))) (radL p (s1L p N rl (c0L p q N (Xc lo hi)) (c0pL p q N (Xc lo hi))) hl lo hi) ! m
                         = UPB p q N (Rf rl) (Hbf hl) lo hi m"
  by (simp add: upbL_def UPB_def up_b_def sqL_nth radL_nth)

lemma diffL_prev_nth: "m < M \<Longrightarrow> diffL p prev_idx (sqL p N rl (c0L p q N (Xc lo hi))) (s1L p N rl (c0L p q N (Xc lo hi)) (c0pL p q N (Xc lo hi))) hl lo hi ! m
                         = DP p q N (Rf rl) (Hbf hl) lo hi m"
  by (simp add: diffL_def DP_def diff_b_def rad2_def sqL_nth s1L_nth prev_lt Hbf_def)

lemma diffL_next_nth: "m < M \<Longrightarrow> diffL p next_idx (sqL p N rl (c0L p q N (Xc lo hi))) (s1L p N rl (c0L p q N (Xc lo hi)) (c0pL p q N (Xc lo hi))) hl lo hi ! m
                         = DN p q N (Rf rl) (Hbf hl) lo hi m"
  by (simp add: diffL_def DN_def diff_b_def rad2_def sqL_nth s1L_nth next_lt Hbf_def)

lemma cdL_nth: "m < M \<Longrightarrow> (\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m) \<Longrightarrow> cdL p gridL lo hi n0 ! m = CD p lo hi n0 m"
  by (simp add: cdL_def CD_def)

section \<open>The index sets on lists\<close>

text \<open>A node record: lower/upper bounds, neighbour differences, distance bounds.\<close>
type_synonym node = "float list \<times> float list \<times> float interval list \<times> float interval list \<times> float list \<times> float list"

definition node_impl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> civ list list \<Rightarrow> float list \<Rightarrow> node" where
  "node_impl p q N gridL n0 lo hi rl hl =
     (let X = interval_of (tc lo hi); CL = c0L p q N X; CPL = c0pL p q N X;
          Qs = sqL p N rl CL; Ds = s1L p N rl CL CPL; RD = radL p Ds hl lo hi;
          CDs = cdL p gridL lo hi n0
      in (lobL Qs RD, upbL Qs RD, diffL p prev_idx Qs Ds hl lo hi, diffL p next_idx Qs Ds hl lo hi,
          map (\<lambda>m. dmin_b (CDs ! m) lo hi) [0..<M], map (\<lambda>m. dmax_b (CDs ! m) lo hi) [0..<M]))"

fun nlob :: "node \<Rightarrow> float list" where "nlob (x1, x2, x3, x4, x5, x6) = x1"
fun nupb :: "node \<Rightarrow> float list" where "nupb (x1, x2, x3, x4, x5, x6) = x2"
fun ndp :: "node \<Rightarrow> float interval list" where "ndp (x1, x2, x3, x4, x5, x6) = x3"
fun ndn :: "node \<Rightarrow> float interval list" where "ndn (x1, x2, x3, x4, x5, x6) = x4"
fun ndmin :: "node \<Rightarrow> float list" where "ndmin (x1, x2, x3, x4, x5, x6) = x5"
fun ndmax :: "node \<Rightarrow> float list" where "ndmax (x1, x2, x3, x4, x5, x6) = x6"

lemma node_nth:
  assumes g: "\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m" and m: "m < M"
  shows "nlob (node_impl p q N gridL n0 lo hi rl hl) ! m = LOB p q N (Rf rl) (Hbf hl) lo hi m"
    and "nupb (node_impl p q N gridL n0 lo hi rl hl) ! m = UPB p q N (Rf rl) (Hbf hl) lo hi m"
    and "ndp (node_impl p q N gridL n0 lo hi rl hl) ! m = DP p q N (Rf rl) (Hbf hl) lo hi m"
    and "ndn (node_impl p q N gridL n0 lo hi rl hl) ! m = DN p q N (Rf rl) (Hbf hl) lo hi m"
    and "ndmin (node_impl p q N gridL n0 lo hi rl hl) ! m = DMIN p lo hi n0 m"
    and "ndmax (node_impl p q N gridL n0 lo hi rl hl) ! m = DMAX p lo hi n0 m"
  unfolding node_impl_def Let_def nlob.simps nupb.simps ndp.simps ndn.simps ndmin.simps ndmax.simps
  by (simp_all add: lobL_nth upbL_nth diffL_prev_nth diffL_next_nth m DMIN_def DMAX_def cdL_nth [OF m g])

text \<open>The predicates, computed from the record.\<close>
definition ppI :: "node \<Rightarrow> nat \<Rightarrow> bool" where "ppI nd m \<longleftrightarrow> m < M \<and> 0 < upper (ndp nd ! m) \<and> 0 < upper (ndn nd ! m)"
definition cpI :: "node \<Rightarrow> nat \<Rightarrow> bool" where "cpI nd m \<longleftrightarrow> m < M \<and> 0 < lower (ndp nd ! m) \<and> 0 < lower (ndn nd ! m)"
definition poI :: "float interval option \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> bool" where
  "poI band nd m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some D \<Rightarrow> lower D < ndmax nd ! m)"
definition coI :: "float interval option \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> bool" where
  "coI band nd m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some D \<Rightarrow> upper D < ndmin nd ! m)"
definition pmI :: "node \<Rightarrow> nat \<Rightarrow> bool" where
  "pmI nd m \<longleftrightarrow> ppI nd m \<and> list_all (\<lambda>k. cpI nd k \<longrightarrow> ndmin nd ! m \<le> ndmax nd ! k) [0..<M]"
definition run_okI :: "node \<Rightarrow> nat list \<Rightarrow> bool" where
  "run_okI nd RS \<longleftrightarrow> list_all (ppI nd) RS \<and>
     list_all (\<lambda>r. list_all (\<lambda>k. ppI nd k \<and> k \<notin> set RS \<longrightarrow> ndmax nd ! r < ndmin nd ! k) [0..<M]) RS"
definition excI :: "node \<Rightarrow> nat \<Rightarrow> bool" where
  "excI nd m \<longleftrightarrow> m < M \<and> (run_okI nd [m] \<or> run_okI nd [m, next_idx m] \<or> run_okI nd [prev_idx m, m])"
definition glI :: "node \<Rightarrow> float" where "glI nd = Max (set (nlob nd))"
definition usI :: "float interval option \<Rightarrow> node \<Rightarrow> float" where
  "usI band nd = Max (set (0 # map (\<lambda>m. nupb nd ! m) (filter (\<lambda>m. ppI nd m \<and> poI band nd m \<and> \<not> excI nd m) [0..<M])))"
definition thI :: "nat \<Rightarrow> node \<Rightarrow> float interval" where
  "thI p nd = mult_float_interval p (interval_of (glI nd)) inv100_ivl"
definition terminalI :: "nat \<Rightarrow> float interval option \<Rightarrow> node \<Rightarrow> bool" where
  "terminalI p band nd \<longleftrightarrow> usI band nd \<le> lower (thI p nd)"
definition llI :: "float interval option \<Rightarrow> node \<Rightarrow> float" where
  "llI band nd = Max (set (0 # map (\<lambda>k. nlob nd ! k) (filter (\<lambda>k. cpI nd k \<and> coI band nd k \<and> \<not> pmI nd k) [0..<M])))"
definition candI :: "nat \<Rightarrow> float interval option \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> bool" where
  "candI p band nd m \<longleftrightarrow> ppI nd m \<and> poI band nd m \<and> \<not> excI nd m \<and>
     lower (thI p nd) \<le> nupb nd ! m \<and> \<not> (0 < llI band nd \<and> nupb nd ! m < llI band nd)"
definition candsI :: "nat \<Rightarrow> float interval option \<Rightarrow> node \<Rightarrow> nat list" where
  "candsI p band nd = filter (candI p band nd) [0..<M]"

subsection \<open>Equality with the abstract sets\<close>

context
  fixes p :: nat and q :: "nat \<Rightarrow> float \<times> float" and N :: nat and gridL :: "float interval list"
    and n0 :: "nat \<Rightarrow> int" and lo hi :: float and rl :: "civ list list" and hl :: "float list"
  assumes g: "\<And>m. m < M \<Longrightarrow> gridL ! m = grid_ivl p m"
begin

abbreviation "nd \<equiv> node_impl p q N gridL n0 lo hi rl hl"
abbreviation "R \<equiv> Rf rl"
abbreviation "Hb \<equiv> Hbf hl"

lemma ppI_eq: "ppI nd m = PP p q N R Hb lo hi m"
  unfolding ppI_def PP_def by (cases "m < M") (simp_all add: node_nth [OF g])
lemma cpI_eq: "cpI nd m = CP p q N R Hb lo hi m"
  unfolding cpI_def CP_def by (cases "m < M") (simp_all add: node_nth [OF g])
lemma poI_eq: "m < M \<Longrightarrow> poI band nd m = PO p lo hi n0 band m"
  unfolding poI_def PO_def by (simp add: node_nth [OF g] split: option.split)
lemma coI_eq: "m < M \<Longrightarrow> coI band nd m = CO p lo hi n0 band m"
  unfolding coI_def CO_def by (simp add: node_nth [OF g] split: option.split)

lemma pmI_eq: "pmI nd m = PM p q N R Hb lo hi n0 m"
proof (cases "m < M")
  case True
  then show ?thesis
    unfolding pmI_def PM_def ppI_eq cpI_eq list_all_iff set_upt
    by (simp add: node_nth [OF g] cong: conj_cong) (auto simp: node_nth [OF g] CP_def)
next
  case False
  then show ?thesis unfolding pmI_def PM_def ppI_eq by (simp add: PP_def)
qed

lemma run_okI_eq: "list_all (\<lambda>r. r < M) RS \<Longrightarrow> run_okI nd RS = run_ok p q N R Hb lo hi n0 (set RS)"
  unfolding run_okI_def run_ok_def list_all_iff set_upt ppI_eq
  by (auto simp: node_nth [OF g] PP_def)

lemma excI_eq: "excI nd m = EXC p q N R Hb lo hi n0 m"
  unfolding excI_def EXC_def
  by (cases "m < M") (simp_all add: run_okI_eq next_lt prev_lt)

lemma glI_eq: "glI nd = GL p q N R Hb lo hi"
proof -
  have "set (nlob nd) = (LOB p q N R Hb lo hi) ` {..<M}"
  proof -
    have "nlob nd = map (LOB p q N R Hb lo hi) [0..<M]"
      unfolding node_impl_def Let_def nlob.simps lobL_def by (intro map_upt_cong) (simp add: LOB_def lo_b_def sqL_nth radL_nth)
    then show ?thesis by (simp add: set_upt atLeast0LessThan)
  qed
  then show ?thesis by (simp add: glI_def GL_def)
qed

lemma usI_eq: "usI band nd = US p q N R Hb lo hi n0 band"
proof -
  have "set (map (\<lambda>m. nupb nd ! m) (filter (\<lambda>m. ppI nd m \<and> poI band nd m \<and> \<not> excI nd m) [0..<M]))
        = (UPB p q N R Hb lo hi) ` {m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}"
  proof -
    have eq1: "{m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}
          = set (filter (\<lambda>m. ppI nd m \<and> poI band nd m \<and> \<not> excI nd m) [0..<M])"
      by (auto simp: ppI_eq poI_eq excI_eq PP_def)
    have eq2: "(\<lambda>m. nupb nd ! m) x = UPB p q N R Hb lo hi x"
      if "x \<in> set (filter (\<lambda>m. ppI nd m \<and> poI band nd m \<and> \<not> excI nd m) [0..<M])" for x
      using that by (simp add: node_nth [OF g])
    show ?thesis unfolding set_map eq1 by (rule image_cong [OF refl eq2])
  qed
  then show ?thesis by (simp add: usI_def US_def)
qed

lemma thI_eq: "thI p nd = TH p q N R Hb lo hi"
  by (simp add: thI_def TH_def glI_eq)

lemma terminalI_eq: "terminalI p band nd = terminal p q N R Hb lo hi n0 band"
  by (simp add: terminalI_def terminal_def usI_eq thI_eq)

lemma llI_eq: "llI band nd = LL p q N R Hb lo hi n0 band"
proof -
  have "set (map (\<lambda>k. nlob nd ! k) (filter (\<lambda>k. cpI nd k \<and> coI band nd k \<and> \<not> pmI nd k) [0..<M]))
        = (LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}"
  proof -
    have eq1: "{k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}
          = set (filter (\<lambda>k. cpI nd k \<and> coI band nd k \<and> \<not> pmI nd k) [0..<M])"
      by (auto simp: cpI_eq coI_eq pmI_eq CP_def)
    have eq2: "(\<lambda>k. nlob nd ! k) x = LOB p q N R Hb lo hi x"
      if "x \<in> set (filter (\<lambda>k. cpI nd k \<and> coI band nd k \<and> \<not> pmI nd k) [0..<M])" for x
      using that by (simp add: node_nth [OF g])
    show ?thesis unfolding set_map eq1 by (rule image_cong [OF refl eq2])
  qed
  then show ?thesis by (simp add: llI_def LL_def)
qed

lemma candI_eq: "candI p band nd m = cand p q N R Hb lo hi n0 band m"
proof (cases "m < M")
  case True
  then show ?thesis unfolding candI_def cand_def
    by (simp add: ppI_eq poI_eq excI_eq thI_eq llI_eq node_nth [OF g])
next
  case False
  then show ?thesis unfolding candI_def cand_def by (simp add: ppI_def PP_def)
qed

lemma candsI_eq: "candsI p band nd = cands p q N R Hb lo hi n0 band"
  unfolding candsI_def cands_def by (intro filter_cong refl candI_eq)

end

end
