(declare-fun five () Int)
(declare-fun a () Int)
(declare-fun cmp () Bool)
(assert (exists ((five Int) (cmp Bool)) (and (= five a)
                                            (= cmp (< five 1000))
                                            (= cmp false)  )))
(apply (using-params qe :qe-nonlinear true))
