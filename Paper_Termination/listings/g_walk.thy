theorem walk_to_main:
  assumes j: "j \<in> above p N c th"
    and stop: "\<And>q. q \<in> fpeaks p N c \<Longrightarrow> sq p N c q > th \<Longrightarrow>
                 q = m0 \<or> q = prev_idx m0 \<or> q = next_idx m0 \<or> q \<in> X"
    and m0: "fpeaks p N c \<noteq> {} \<Longrightarrow> m0 \<in> fpeaks p N c"
  shows "\<exists>q. (j, q) \<in> (step p N c th)\<^sup>* \<and> (q = m0 mod M \<or> q \<in> X)"
