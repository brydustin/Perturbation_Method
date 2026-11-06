theory DCS_9_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_156: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 156) (-8)) (Float (int 156 + 1) (-8))"
  by eval

lemma dc_nc_156: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 156) (-8)) (Float (int 156 + 1) (-8))"
  by eval

lemma dc_c30_157: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 157) (-8)) (Float (int 157 + 1) (-8))"
  by eval

lemma dc_nc_157: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 157) (-8)) (Float (int 157 + 1) (-8))"
  by eval

lemma dc_c30_158: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 158) (-8)) (Float (int 158 + 1) (-8))"
  by eval

lemma dc_nc_158: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 158) (-8)) (Float (int 158 + 1) (-8))"
  by eval

lemma dc_c30_159: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 159) (-8)) (Float (int 159 + 1) (-8))"
  by eval

lemma dc_nc_159: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 159) (-8)) (Float (int 159 + 1) (-8))"
  by eval

end
