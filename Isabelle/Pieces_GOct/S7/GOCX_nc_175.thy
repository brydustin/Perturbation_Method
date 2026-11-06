theory GOCX_nc_175
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2800: "goc_sub None 2800"
  by (goc_eval goc_nc_2800)

lemma goc_nc_2801: "goc_sub None 2801"
  by (goc_eval goc_nc_2801)

lemma goc_nc_2802: "goc_sub None 2802"
  by (goc_eval goc_nc_2802)

lemma goc_nc_2803: "goc_sub None 2803"
  by (goc_eval goc_nc_2803)

lemma goc_nc_2804: "goc_sub None 2804"
  by (goc_eval goc_nc_2804)

lemma goc_nc_2805: "goc_sub None 2805"
  by (goc_eval goc_nc_2805)

lemma goc_nc_2806: "goc_sub None 2806"
  by (goc_eval goc_nc_2806)

lemma goc_nc_2807: "goc_sub None 2807"
  by (goc_eval goc_nc_2807)

lemma goc_nc_2808: "goc_sub None 2808"
  by (goc_eval goc_nc_2808)

lemma goc_nc_2809: "goc_sub None 2809"
  by (goc_eval goc_nc_2809)

lemma goc_nc_2810: "goc_sub None 2810"
  by (goc_eval goc_nc_2810)

lemma goc_nc_2811: "goc_sub None 2811"
  by (goc_eval goc_nc_2811)

lemma goc_nc_2812: "goc_sub None 2812"
  by (goc_eval goc_nc_2812)

lemma goc_nc_2813: "goc_sub None 2813"
  by (goc_eval goc_nc_2813)

lemma goc_nc_2814: "goc_sub None 2814"
  by (goc_eval goc_nc_2814)

lemma goc_nc_2815: "goc_sub None 2815"
  by (goc_eval goc_nc_2815)

lemma gupt_nc_175: "[2800..<2816] = [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]"
  by (simp add: upt_rec)

lemma gsec_nc_175: "\<forall>j\<in>{16 * 175..<16 * 175 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 175..<16 * 175 + 16}"
  then have "j \<in> set [2800..<2816]" unfolding set_upt by simp
  then have "j \<in> set [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]" unfolding gupt_nc_175 .
  then show "goc_sub None j" using goc_nc_2800 goc_nc_2801 goc_nc_2802 goc_nc_2803 goc_nc_2804 goc_nc_2805 goc_nc_2806 goc_nc_2807 goc_nc_2808 goc_nc_2809 goc_nc_2810 goc_nc_2811 goc_nc_2812 goc_nc_2813 goc_nc_2814 goc_nc_2815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
