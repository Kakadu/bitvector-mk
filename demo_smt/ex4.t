BV size 2
  $ cat <<-EOF > input.smt
  > (declare-fun a () (_ BitVec 2))
  > (declare-fun b () (_ BitVec 2))
  > (assert
  >   (exists ((x (_ BitVec 2)))
  >     (bvult a (bvshl b x))
  >     ))
  > (apply (using-params qe :qe-nonlinear true))
  > EOF
  $ z3 input.smt
  (goals
  (goal
    (let ((a!1 (not (bvule (concat ((_ extract 0 0) b) #b0) a))))
      (or (not (bvule b a)) a!1))
    :precision precise :depth 1)
  )
  $ cat <<-EOF > verify.smt
  > (declare-fun a () (_ BitVec 2))
  > (declare-fun b () (_ BitVec 2))
  > (assert
  >   (not (iff
  >     (exists ((x (_ BitVec 2)))
  >       (bvult a (bvshl b x))
  >       )
  >     (or (not (bvule b a))
  >         (not (bvule (bvshl b #b01) a)) )
  >     ;(or (= a #x0) (= a #x2) )
  >     )))
  > (check-sat)
  > EOF
  $ z3 verify.smt
  unsat

BV size 3
  $ cat <<-EOF > input.smt
  > (declare-fun a () (_ BitVec 3))
  > (declare-fun b () (_ BitVec 3))
  > (assert
  >   (exists ((x (_ BitVec 3)))
  >     (bvult a (bvshl b x))
  >     ))
  > (apply (using-params qe :qe-nonlinear true))
  > EOF
  $ z3 input.smt
  (goals
  (goal
    (let ((a!1 (not (bvule (concat ((_ extract 1 0) b) #b0) a)))
          (a!2 (not (bvule (concat ((_ extract 0 0) b) #b00) a))))
      (or (not (bvule b a)) a!1 a!2))
    :precision precise :depth 1)
  )
  $ cat <<-EOF > input.smt
  > (declare-fun a () (_ BitVec 3))
  > (declare-fun b () (_ BitVec 3))
  > (assert
  >   (not (iff
  >     (exists ((x (_ BitVec 3)))
  >       (bvult a (bvshl b x))
  >     )
  >     (or (not (bvule b a))
  >         (not (bvule (bvshl b #b001) a))
  >         (not (bvule (bvshl b #b010) a)) )
  >   )))
  > (check-sat)
  > EOF
  $ z3 input.smt
  unsat
