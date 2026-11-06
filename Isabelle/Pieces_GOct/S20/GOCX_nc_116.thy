theory GOCX_nc_116
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1856: "goc_sub None 1856"
  by (goc_eval goc_nc_1856)

lemma goc_nc_1857: "goc_sub None 1857"
  by (goc_eval goc_nc_1857)

lemma goc_nc_1858: "goc_sub None 1858"
  by (goc_eval goc_nc_1858)

lemma goc_nc_1859: "goc_sub None 1859"
  by (goc_eval goc_nc_1859)

lemma goc_nc_1860: "goc_sub None 1860"
  by (goc_eval goc_nc_1860)

lemma goc_nc_1861: "goc_sub None 1861"
  by (goc_eval goc_nc_1861)

lemma goc_nc_1862: "goc_sub None 1862"
  by (goc_eval goc_nc_1862)

lemma goc_nc_1863: "goc_sub None 1863"
  by (goc_eval goc_nc_1863)

lemma goc_nc_1864: "goc_sub None 1864"
  by (goc_eval goc_nc_1864)

lemma goc_nc_1865: "goc_sub None 1865"
  by (goc_eval goc_nc_1865)

lemma goc_nc_1866: "goc_sub None 1866"
  by (goc_eval goc_nc_1866)

lemma goc_nc_1867: "goc_sub None 1867"
  by (goc_eval goc_nc_1867)

lemma goc_nc_1868: "goc_sub None 1868"
  by (goc_eval goc_nc_1868)

lemma goc_nc_1869: "goc_sub None 1869"
  by (goc_eval goc_nc_1869)

lemma goc_nc_1870: "goc_sub None 1870"
  by (goc_eval goc_nc_1870)

lemma goc_nc_1871: "goc_sub None 1871"
  by (goc_eval goc_nc_1871)

lemma gupt_nc_116: "[1856..<1872] = [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]"
  by (simp add: upt_rec)

lemma gsec_nc_116: "\<forall>j\<in>{16 * 116..<16 * 116 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 116..<16 * 116 + 16}"
  then have "j \<in> set [1856..<1872]" unfolding set_upt by simp
  then have "j \<in> set [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]" unfolding gupt_nc_116 .
  then show "goc_sub None j" using goc_nc_1856 goc_nc_1857 goc_nc_1858 goc_nc_1859 goc_nc_1860 goc_nc_1861 goc_nc_1862 goc_nc_1863 goc_nc_1864 goc_nc_1865 goc_nc_1866 goc_nc_1867 goc_nc_1868 goc_nc_1869 goc_nc_1870 goc_nc_1871
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
