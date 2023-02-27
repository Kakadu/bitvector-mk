(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))

(push)
(assert
  (let ( (input (forall ((x (_ BitVec 4))) (bvult (bvshl a x) (bvshl b x)) ))
         (predi (bvult a b) )
  )
  (not (equiv input predi))
  ))

(apply (using-params qe :qe-nonlinear true))
(pop)
