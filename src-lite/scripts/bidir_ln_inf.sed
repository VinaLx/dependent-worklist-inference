/^Hint Immediate degree_bexpr_wrt_bexpr_open_bexpr_wrt_bexpr_inv/a\
Hint Resolve degree_bexpr_wrt_bexpr_open_bexpr_wrt_bexpr_inv : lngen_fix.

/^Lemma degree_app_fun_wrt_bexpr_of_lc_app_fun_mutual/,/^Qed.$/ {
  s/eauto with lngen/eauto with lngen lngen_fix/
}

/^Lemma lc_fun_pi_exists/,/^Qed.$/ {
  s/eauto with lngen/eauto 6 with lngen lngen_fix/
}
