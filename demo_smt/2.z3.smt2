(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))



(push)
(assert (exists ((x (_ BitVec 4))) (bvult a  (bvshl b x))))
(apply (using-params qe :qe-nonlinear true))
(pop)

(push)
(assert
  (let  ( (input (exists ((x (_ BitVec 4))) (bvult a  (bvshl b x))))
          (a!1 (not (bvule (concat ((_ extract 1 0) b) #b00) a)))
          (a!2 (not (bvule (concat ((_ extract 0 0) b) #b000) a)))
          (a!3 (not (bvule (concat ((_ extract 2 0) b) #b0) a)))
        )
  (let  ( (answ (or (not (bvule b a)) a!1 a!2 a!3)) )
    (not (equiv input answ))
  )))

(check-sat)
(pop)

(push)
(assert
  (let  ( (input (exists ((x (_ BitVec 4))) (bvult a  (bvshl b x))))
          (a!1 (not (bvule (concat ((_ extract 1 0) b) #b00) a)))
          (a!2 (not (bvule (concat ((_ extract 0 0) b) #b000) a)))
          (a!3 (not (bvule (concat ((_ extract 2 0) b) #b0) a)))
        )
  (let  ( (answ (or (not (bvule b a)) a!1 a!2 a!3)) )
    (not (equiv input answ))
  )))

(check-sat)
(pop)

(push)
(assert
  (let  ( (input (exists ((x (_ BitVec 4))) (bvult a  (bvshl b x))))
          (a!1 (not (bvule (bvshl b #x2) a)))
          (a!2 (not (bvule (bvshl b #x3) a)))
          (a!3 (not (bvule (bvshl b #x1) a)))
        )
  (let  ( (answ (or (not (bvule b a)) a!3 a!2 a!1)) )
    (not (equiv input answ))
  )))

(check-sat)
(pop)

(push)
    (declare-fun five () Int)
    (declare-fun u () Int)
    (declare-fun cmp () Bool)
    (assert (exists ((five Int) (cmp Bool)) (and (= five u)
                                            (= cmp (< five 1000))
                                            (= cmp false)  )))
    (apply (using-params qe :qe-nonlinear true))
(pop)
