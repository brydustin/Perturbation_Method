lemma thl_while_seq [hoare_safe]:
  assumes
    "\<And> old z. H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old) \<and> G \<and> Var = \<guillemotleft>z\<guillemotright>] Body [@(Inv old) \<and> Var < \<guillemotleft>z\<guillemotright>]"
    "\<And> old. `P \<and> \<guillemotleft>old\<guillemotright> = $\<^bold>v \<longrightarrow> @(Inv old)`"
    "\<And> old. H[\<not> G \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)] Rest [Post]"
  shows "H[P] (while G inv @(Inv old) var Var do Body od) ;; Rest [Post]"
