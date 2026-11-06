theory GOCX_nc_159
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2544: "goc_sub None 2544"
  by (goc_eval goc_nc_2544)

lemma goc_nc_2545: "goc_sub None 2545"
  by (goc_eval goc_nc_2545)

lemma goc_nc_2546: "goc_sub None 2546"
  by (goc_eval goc_nc_2546)

lemma goc_nc_2547: "goc_sub None 2547"
  by (goc_eval goc_nc_2547)

lemma goc_nc_2548: "goc_sub None 2548"
  by (goc_eval goc_nc_2548)

lemma goc_nc_2549: "goc_sub None 2549"
  by (goc_eval goc_nc_2549)

lemma goc_nc_2550: "goc_sub None 2550"
  by (goc_eval goc_nc_2550)

lemma goc_nc_2551: "goc_sub None 2551"
  by (goc_eval goc_nc_2551)

lemma goc_nc_2552: "goc_sub None 2552"
  by (goc_eval goc_nc_2552)

lemma goc_nc_2553: "goc_sub None 2553"
  by (goc_eval goc_nc_2553)

lemma goc_nc_2554: "goc_sub None 2554"
  by (goc_eval goc_nc_2554)

lemma goc_nc_2555: "goc_sub None 2555"
  by (goc_eval goc_nc_2555)

lemma goc_nc_2556: "goc_sub None 2556"
  by (goc_eval goc_nc_2556)

lemma goc_nc_2557: "goc_sub None 2557"
  by (goc_eval goc_nc_2557)

lemma goc_nc_2558: "goc_sub None 2558"
  by (goc_eval goc_nc_2558)

lemma goc_nc_2559: "goc_sub None 2559"
  by (goc_eval goc_nc_2559)

lemma gupt_nc_159: "[2544..<2560] = [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]"
  by (simp add: upt_rec)

lemma gsec_nc_159: "\<forall>j\<in>{16 * 159..<16 * 159 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 159..<16 * 159 + 16}"
  then have "j \<in> set [2544..<2560]" unfolding set_upt by simp
  then have "j \<in> set [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]" unfolding gupt_nc_159 .
  then show "goc_sub None j" using goc_nc_2544 goc_nc_2545 goc_nc_2546 goc_nc_2547 goc_nc_2548 goc_nc_2549 goc_nc_2550 goc_nc_2551 goc_nc_2552 goc_nc_2553 goc_nc_2554 goc_nc_2555 goc_nc_2556 goc_nc_2557 goc_nc_2558 goc_nc_2559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
