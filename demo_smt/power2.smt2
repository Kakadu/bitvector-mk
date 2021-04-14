
; from https://stackoverflow.com/questions/44380279/z3-quantifiers-elimination-in-smtlib-syntax
(assert
  (exists ((x (_ BitVec 4)))
    (= #x0 (bvand x (bvsub x #x1)))))



(apply (using-params qe :qe-nonlinear true))
