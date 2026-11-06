theory DCS_9_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_152: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 152) (-8)) (Float (int 152 + 1) (-8))"
  by eval

lemma dc_nc_152: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 152) (-8)) (Float (int 152 + 1) (-8))"
  by eval

lemma dc_c30_153: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 153) (-8)) (Float (int 153 + 1) (-8))"
  by eval

lemma dc_nc_153: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 153) (-8)) (Float (int 153 + 1) (-8))"
  by eval

lemma dc_c30_154: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 154) (-8)) (Float (int 154 + 1) (-8))"
  by eval

lemma dc_nc_154: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 154) (-8)) (Float (int 154 + 1) (-8))"
  by eval

lemma dc_c30_155: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 155) (-8)) (Float (int 155 + 1) (-8))"
  by eval

lemma dc_nc_155: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 155) (-8)) (Float (int 155 + 1) (-8))"
  by eval

end
