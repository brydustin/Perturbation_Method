lemma sel_cand:
  assumes m0: "m0 \<in> mains (fpos q) N c t" and s: "s \<in> sel (fpos q) N c (eligible (fpos q) N bd c t m0)"
  shows "cand p q N R Hb lo hi n0 band s"
