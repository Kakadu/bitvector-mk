(or
 (bvult a
	(concat
	 ((_ extract 0 0)
	  b)
	 (_ bv0 3)))
 (bvult a
	(concat
	 ((_ extract 1 0)
	  b)
	 (_ bv0 2)))
 (bvult a
	(concat
	 ((_ extract 2 0)
	  b)
	 (_ bv0 1)))
 (bvult a b)
 (bvult a
	(bvshl b
	       (CHOICE
		((x0
		  (_ BitVec 4)))
		(or
		 (=
		  (bvshl b x0)
		  (bvadd a
			 (_ bv1 4)))
		 (and
		  (not
		   (=
		    (bvadd a
			   (_ bv1 4))
		    b))
		  (not
		   (=
		    (concat
		     ((_ extract 2 0)
		      b)
		     (_ bv0 1))
		    (bvadd a
			   (_ bv1 4))))
		  (not
		   (=
		    (concat
		     ((_ extract 1 0)
		      b)
		     (_ bv0 2))
		    (bvadd a
			   (_ bv1 4))))
		  (not
		   (=
		    (concat
		     ((_ extract 0 0)
		      b)
		     (_ bv0 3))
		    (bvadd a
			   (_ bv1 4))))
		  (not
		   (=
		    (_ bv15 4)
		    a))))))))
