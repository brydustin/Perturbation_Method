theory DCS_9_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_148: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 148) (-8)) (Float (int 148 + 1) (-8))"
  by eval

lemma dc_nc_148: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 148) (-8)) (Float (int 148 + 1) (-8))"
  by eval

lemma dc_c30_149: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 149) (-8)) (Float (int 149 + 1) (-8))"
  by eval

lemma dc_nc_149: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 149) (-8)) (Float (int 149 + 1) (-8))"
  by eval

lemma dc_c30_150: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 150) (-8)) (Float (int 150 + 1) (-8))"
  by eval

lemma dc_nc_150: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 150) (-8)) (Float (int 150 + 1) (-8))"
  by eval

lemma dc_c30_151: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 151) (-8)) (Float (int 151 + 1) (-8))"
  by eval

lemma dc_nc_151: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 151) (-8)) (Float (int 151 + 1) (-8))"
  by eval

end
