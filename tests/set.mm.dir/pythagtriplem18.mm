include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cgcd.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "cv.mm"
include "wrex.mm"
include "eqid.mm"
include "pythagtriplem13.mm"
include "pythagtriplem11.mm"
include "pythagtriplem15.mm"
include "pythagtriplem16.mm"
include "pythagtriplem17.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "3anbi123d.mm"
include "oveq1d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"

theorem pythagtriplem18
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n

  disjoint A m
  disjoint A n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint C m
  disjoint C n
  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> E. n e. NN E. m e. NN ( A = ( ( m ^ 2 ) - ( n ^ 2 ) ) /\ B = ( 2 x. ( m x. n ) ) /\ C = ( ( m ^ 2 ) + ( n ^ 2 ) ) ) )

  proof
    cA
    cn
    wcel
    cB
    cn
    wcel
    cC
    cn
    wcel
    w3a
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    caddc
    co
    cC
    c2
    cexp
    co
    wceq
    cA
    cB
    cgcd
    co
    c1
    wceq
    c2
    cA
    cdvds
    wbr
    wn
    wa
    w3a
    cC
    cB
    caddc
    co
    csqrt
    cfv
    #
    cC
    cB
    cmin
    co
    csqrt
    cfv
    #
    cmin
    co
    c2
    cdiv
    co
    #
    cn
    wcel
    @0
    @1
    caddc
    co
    c2
    cdiv
    co
    #
    cn
    wcel
    cA
    @3
    c2
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    cmin
    co
    #
    wceq
    #
    cB
    c2
    @3
    @2
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    cC
    @4
    @5
    caddc
    co
    #
    wceq
    #
    cA
    vm
    cv
    #
    c2
    cexp
    co
    #
    vn
    cv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    wceq
    #
    cB
    c2
    @13
    @15
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    cC
    @14
    @16
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vm
    cn
    wrex
    vn
    cn
    wrex
    cA
    cB
    cC
    @2
    @2
    eqid
    #
    pythagtriplem13
    cA
    cB
    cC
    @3
    @3
    eqid
    #
    pythagtriplem11
    cA
    cB
    cC
    @3
    @2
    @26
    @25
    pythagtriplem15
    cA
    cB
    cC
    @3
    @2
    @26
    @25
    pythagtriplem16
    cA
    cB
    cC
    @3
    @2
    @26
    @25
    pythagtriplem17
    @24
    @7
    @10
    @12
    w3a
    cA
    @14
    @5
    cmin
    co
    #
    wceq
    #
    cB
    c2
    @13
    @2
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    cC
    @14
    @5
    caddc
    co
    #
    wceq
    #
    w3a
    vn
    vm
    @2
    @3
    cn
    cn
    @15
    @2
    wceq
    #
    @18
    @28
    @21
    @31
    @23
    @33
    @34
    @17
    @27
    cA
    @34
    @16
    @5
    @14
    cmin
    @15
    @2
    c2
    cexp
    oveq1
    #
    oveq2d
    eqeq2d
    @34
    @20
    @30
    cB
    @34
    @19
    @29
    c2
    cmul
    @15
    @2
    @13
    cmul
    oveq2
    oveq2d
    eqeq2d
    @34
    @22
    @32
    cC
    @34
    @16
    @5
    @14
    caddc
    @35
    oveq2d
    eqeq2d
    3anbi123d
    @13
    @3
    wceq
    #
    @28
    @7
    @31
    @10
    @33
    @12
    @36
    @27
    @6
    cA
    @36
    @14
    @4
    @5
    cmin
    @13
    @3
    c2
    cexp
    oveq1
    #
    oveq1d
    eqeq2d
    @36
    @30
    @9
    cB
    @36
    @29
    @8
    c2
    cmul
    @13
    @3
    @2
    cmul
    oveq1
    oveq2d
    eqeq2d
    @36
    @32
    @11
    cC
    @36
    @14
    @4
    @5
    caddc
    @37
    oveq1d
    eqeq2d
    3anbi123d
    rspc2ev
    syl113anc
end
