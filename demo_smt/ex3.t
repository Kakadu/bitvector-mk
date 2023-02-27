BV size 2
  $ cat <<-EOF > input.smt
  > (declare-fun a () (_ BitVec 2))
  > (push)
  > (assert
  >   (exists ((y (_ BitVec 2)))
  >     (and (bvule #b00 y)
  >          (= a (bvshl #b10 y))
  >     )))
  > (apply (using-params qe :qe-nonlinear true))
  > EOF
  $ z3 input.smt
  (goals
  (goal
    (or (= a #b00) (= a #b10))
    :precision precise :depth 1)
  )
  $ cat <<-EOF > input.smt
  > (declare-fun a () (_ BitVec 2))
  > (push)
  > (assert
  >   (not (iff
  >     (exists ((y (_ BitVec 2)))
  >       (and (bvule #b00 y)
  >          (= a (bvshl #b10 y))))
  >     (bvule a (bvshl a (bvshl a #b01)))
  >     ;(or (= a #x0) (= a #x2) )
  >     )))
  > (check-sat)
  > EOF
  $ z3 input.smt
  unsat

BV size 3
  $ cat <<-EOF > input.smt
  > (declare-fun a () (_ BitVec 3))
  > (push)
  > (assert
  >   (exists ((y (_ BitVec 3)))
  >     (and (bvule #b000 y)
  >          (= a (bvshl #b010 y))
  >     )))
  > (apply (using-params qe :qe-nonlinear true))
  > EOF
  $ z3 input.smt
  (goals
  (goal
    (or (= a #b000) (= a #b010) (= a #b100))
    :precision precise :depth 1)
  )
  $ cat <<-EOF > verify.smt
  > (declare-fun a () (_ BitVec 3))
  > (assert
  >   (not (iff
  >     (exists ((y (_ BitVec 3)))
  >       (and (bvule #b000 y)
  >          (= a (bvshl #b010 y))))
  >     ;
  >     (or (= a #b000) (= a #b010) (= a #b100) )
  >     )))
  > (check-sat)
  > EOF
  $ z3 verify.smt
  unsat
