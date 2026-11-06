lemma terminal_sound:
  assumes m0: "m0 \<in> mains (fpos q) N c t" and trm: "terminal p q N R Hb lo hi n0 band"
  shows "eligible (fpos q) N bd c t m0 = {}"
