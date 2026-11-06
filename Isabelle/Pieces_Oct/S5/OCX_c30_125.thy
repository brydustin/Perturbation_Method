theory OCX_c30_125
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2000: "oc_sub oc_b30 2000"
  by (oc_eval oc_c30_2000)

lemma oc_c30_2001: "oc_sub oc_b30 2001"
  by (oc_eval oc_c30_2001)

lemma oc_c30_2002: "oc_sub oc_b30 2002"
  by (oc_eval oc_c30_2002)

lemma oc_c30_2003: "oc_sub oc_b30 2003"
  by (oc_eval oc_c30_2003)

lemma oc_c30_2004: "oc_sub oc_b30 2004"
  by (oc_eval oc_c30_2004)

lemma oc_c30_2005: "oc_sub oc_b30 2005"
  by (oc_eval oc_c30_2005)

lemma oc_c30_2006: "oc_sub oc_b30 2006"
  by (oc_eval oc_c30_2006)

lemma oc_c30_2007: "oc_sub oc_b30 2007"
  by (oc_eval oc_c30_2007)

lemma oc_c30_2008: "oc_sub oc_b30 2008"
  by (oc_eval oc_c30_2008)

lemma oc_c30_2009: "oc_sub oc_b30 2009"
  by (oc_eval oc_c30_2009)

lemma oc_c30_2010: "oc_sub oc_b30 2010"
  by (oc_eval oc_c30_2010)

lemma oc_c30_2011: "oc_sub oc_b30 2011"
  by (oc_eval oc_c30_2011)

lemma oc_c30_2012: "oc_sub oc_b30 2012"
  by (oc_eval oc_c30_2012)

lemma oc_c30_2013: "oc_sub oc_b30 2013"
  by (oc_eval oc_c30_2013)

lemma oc_c30_2014: "oc_sub oc_b30 2014"
  by (oc_eval oc_c30_2014)

lemma oc_c30_2015: "oc_sub oc_b30 2015"
  by (oc_eval oc_c30_2015)

lemma upt_c30_125: "[2000..<2016] = [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]"
  by (simp add: upt_rec)

lemma sec_c30_125: "\<forall>j\<in>{16 * 125..<16 * 125 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 125..<16 * 125 + 16}"
  then have "j \<in> set [2000..<2016]" unfolding set_upt by simp
  then have "j \<in> set [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]" unfolding upt_c30_125 .
  then show "oc_sub oc_b30 j" using oc_c30_2000 oc_c30_2001 oc_c30_2002 oc_c30_2003 oc_c30_2004 oc_c30_2005 oc_c30_2006 oc_c30_2007 oc_c30_2008 oc_c30_2009 oc_c30_2010 oc_c30_2011 oc_c30_2012 oc_c30_2013 oc_c30_2014 oc_c30_2015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
