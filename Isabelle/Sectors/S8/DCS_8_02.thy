theory DCS_8_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_136: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 136) (-8)) (Float (int 136 + 1) (-8))"
  by eval

lemma dc_nc_136: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 136) (-8)) (Float (int 136 + 1) (-8))"
  by eval

lemma dc_c30_137: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 137) (-8)) (Float (int 137 + 1) (-8))"
  by eval

lemma dc_nc_137: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 137) (-8)) (Float (int 137 + 1) (-8))"
  by eval

lemma dc_c30_138: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 138) (-8)) (Float (int 138 + 1) (-8))"
  by eval

lemma dc_nc_138: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 138) (-8)) (Float (int 138 + 1) (-8))"
  by eval

lemma dc_c30_139: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 139) (-8)) (Float (int 139 + 1) (-8))"
  by eval

lemma dc_nc_139: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 139) (-8)) (Float (int 139 + 1) (-8))"
  by eval

end
