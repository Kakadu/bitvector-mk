(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))

(assert (exists ((x (_ BitVec 4))) (bvult a  (bvshl b x))))


(apply (using-params qe :qe-nonlinear true))
