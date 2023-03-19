include "cv.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "w3a.mm"
include "cee.mm"
include "cfv.mm"
include "ccgr3.mm"
include "cn.mm"
include "wceq.mm"
include "opeq1.mm"
include "breq1d.mm"
include "3anbi12d.mm"
include "opeq2.mm"
include "3anbi13d.mm"
include "3anbi23d.mm"
include "breq2d.mm"
include "fveq2.mm"
include "df-cgr3.mm"
include "br6.mm"

theorem brcgr3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <-> ( <. A , B >. Cgr <. D , E >. /\ <. A , C >. Cgr <. D , F >. /\ <. B , C >. Cgr <. E , F >. ) ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    vd
    cv
    #
    ve
    cv
    #
    cop
    #
    ccgr
    wbr
    #
    @0
    vc
    cv
    #
    cop
    #
    @3
    vf
    cv
    #
    cop
    #
    ccgr
    wbr
    #
    @1
    @7
    cop
    #
    @4
    @9
    cop
    #
    ccgr
    wbr
    #
    w3a
    cA
    @1
    cop
    #
    @5
    ccgr
    wbr
    #
    cA
    @7
    cop
    #
    @10
    ccgr
    wbr
    #
    @14
    w3a
    cA
    cB
    cop
    #
    @5
    ccgr
    wbr
    #
    @18
    cB
    @7
    cop
    #
    @13
    ccgr
    wbr
    #
    w3a
    @20
    cA
    cC
    cop
    #
    @10
    ccgr
    wbr
    #
    cB
    cC
    cop
    #
    @13
    ccgr
    wbr
    #
    w3a
    @19
    cD
    @4
    cop
    #
    ccgr
    wbr
    #
    @23
    cD
    @9
    cop
    #
    ccgr
    wbr
    #
    @26
    w3a
    @19
    cD
    cE
    cop
    #
    ccgr
    wbr
    #
    @30
    @25
    cE
    @9
    cop
    #
    ccgr
    wbr
    #
    w3a
    @32
    @23
    cD
    cF
    cop
    #
    ccgr
    wbr
    #
    @25
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    w3a
    vn
    cA
    cB
    cC
    cD
    vn
    cv
    #
    cee
    cfv
    cN
    cee
    cfv
    ccgr3
    cn
    ve
    vf
    cE
    cF
    cN
    vq
    vp
    va
    vb
    vc
    vd
    @0
    cA
    wceq
    #
    @6
    @16
    @11
    @18
    @14
    @40
    @2
    @15
    @5
    ccgr
    @0
    cA
    @1
    opeq1
    breq1d
    @40
    @8
    @17
    @10
    ccgr
    @0
    cA
    @7
    opeq1
    breq1d
    3anbi12d
    @1
    cB
    wceq
    #
    @16
    @20
    @14
    @22
    @18
    @41
    @15
    @19
    @5
    ccgr
    @1
    cB
    cA
    opeq2
    breq1d
    @41
    @12
    @21
    @13
    ccgr
    @1
    cB
    @7
    opeq1
    breq1d
    3anbi13d
    @7
    cC
    wceq
    #
    @18
    @24
    @22
    @26
    @20
    @42
    @17
    @23
    @10
    ccgr
    @7
    cC
    cA
    opeq2
    breq1d
    @42
    @21
    @25
    @13
    ccgr
    @7
    cC
    cB
    opeq2
    breq1d
    3anbi23d
    @3
    cD
    wceq
    #
    @20
    @28
    @24
    @30
    @26
    @43
    @5
    @27
    @19
    ccgr
    @3
    cD
    @4
    opeq1
    breq2d
    @43
    @10
    @29
    @23
    ccgr
    @3
    cD
    @9
    opeq1
    breq2d
    3anbi12d
    @4
    cE
    wceq
    #
    @28
    @32
    @26
    @34
    @30
    @44
    @27
    @31
    @19
    ccgr
    @4
    cE
    cD
    opeq2
    breq2d
    @44
    @13
    @33
    @25
    ccgr
    @4
    cE
    @9
    opeq1
    breq2d
    3anbi13d
    @9
    cF
    wceq
    #
    @30
    @36
    @34
    @38
    @32
    @45
    @29
    @35
    @23
    ccgr
    @9
    cF
    cD
    opeq2
    breq2d
    @45
    @33
    @37
    @25
    ccgr
    @9
    cF
    cE
    opeq2
    breq2d
    3anbi23d
    @39
    cN
    cee
    fveq2
    ve
    vf
    vn
    vq
    vp
    va
    vb
    vc
    vd
    df-cgr3
    br6
end
