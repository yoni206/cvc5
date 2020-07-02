(set-logic BV)
(assert (exists ((c__detect__main__1__i_36_C (_ BitVec 32))) (forall ((termination__pre__0__c__detect__main__1__i (_ BitVec 32))) (forall ((c__detect__main__1__s_0 (_ BitVec 32))) (forall ((c__detect__main__1__i_35_0 (_ BitVec 32))) (forall ((c__detect__main__1__i (_ BitVec 32))) (=> (and (= termination__pre__0__c__detect__main__1__i c__detect__main__1__i_35_0) (= c__detect__main__1__i_35_0 (_ bv0 32)) (not (= c__detect__main__1__s_0 (_ bv0 32))) (= c__detect__main__1__i (bvadd c__detect__main__1__i_35_0 (_ bv1 32)))) (bvslt (bvmul ((_ sign_extend 32) c__detect__main__1__i_36_C) ((_ sign_extend 32) c__detect__main__1__i)) (bvmul ((_ sign_extend 32) c__detect__main__1__i_36_C) ((_ sign_extend 32) termination__pre__0__c__detect__main__1__i)))) ) ) ) ) ))
(check-sat)
(exit)
