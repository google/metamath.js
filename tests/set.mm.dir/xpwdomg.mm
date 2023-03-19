include "cwdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wex.mm"
include "cxp.mm"
include "brwdom3i.mm"
include "adantr.mm"
include "adantl.mm"
include "wi.mm"
include "cvv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wcel.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "xpexg.mm"
include "syl2an.mm"
include "brrelex2i.mm"
include "pm3.2.mm"
include "ralimdv.mm"
include "com12.mm"
include "impcom.mm"
include "reximdv.mm"
include "2ralimi.mm"
include "syl.mm"
include "eqeq1.mm"
include "vex.mm"
include "opth.mm"
include "syl6bb.mm"
include "2rexbidv.mm"
include "ralxp.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "opeq12d.mm"
include "eqeq2d.mm"
include "rexxp.mm"
include "adantll.mm"
include "wdom2d.mm"
include "expr.mm"
include "exlimdv.mm"
include "ex.mm"
include "mp2d.mm"

theorem xpwdomg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vd: setvar d


  assert |- ( ( A ~<_* B /\ C ~<_* D ) -> ( A X. C ) ~<_* ( B X. D ) )

  proof
    cA
    cB
    cwdom
    wbr
    #
    cC
    cD
    cwdom
    wbr
    #
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    vf
    cv
    #
    cfv
    #
    wceq
    #
    vb
    cB
    wrex
    #
    va
    cA
    wral
    #
    vf
    wex
    #
    vc
    cv
    #
    vd
    cv
    #
    vg
    cv
    #
    cfv
    #
    wceq
    #
    vd
    cD
    wrex
    #
    vc
    cC
    wral
    #
    vg
    wex
    #
    cA
    cC
    cxp
    #
    cB
    cD
    cxp
    #
    cwdom
    wbr
    #
    @0
    @10
    @1
    va
    vb
    vf
    cA
    cB
    brwdom3i
    adantr
    @1
    @18
    @0
    vc
    vd
    vg
    cC
    cD
    brwdom3i
    adantl
    @2
    @9
    @18
    @21
    wi
    #
    vf
    @2
    @9
    @22
    @2
    @9
    wa
    @17
    @21
    vg
    @2
    @9
    @17
    @21
    @2
    @9
    @17
    wa
    #
    wa
    vx
    vy
    @19
    @20
    cvv
    cvv
    vy
    cv
    #
    c1st
    cfv
    #
    @5
    cfv
    #
    @24
    c2nd
    cfv
    #
    @13
    cfv
    #
    cop
    #
    @2
    @19
    cvv
    wcel
    #
    @23
    @0
    cA
    cvv
    wcel
    cC
    cvv
    wcel
    @30
    @1
    cA
    cB
    cwdom
    relwdom
    brrelexi
    cC
    cD
    cwdom
    relwdom
    brrelexi
    cA
    cC
    cvv
    cvv
    xpexg
    syl2an
    adantr
    @2
    @20
    cvv
    wcel
    #
    @23
    @0
    cB
    cvv
    wcel
    cD
    cvv
    wcel
    @31
    @1
    cA
    cB
    cwdom
    relwdom
    brrelex2i
    cC
    cD
    cwdom
    relwdom
    brrelex2i
    cB
    cD
    cvv
    cvv
    xpexg
    syl2an
    adantr
    @23
    vx
    cv
    #
    @19
    wcel
    #
    @32
    @29
    wceq
    #
    vy
    @20
    wrex
    #
    @2
    @23
    @33
    wa
    @32
    @6
    @14
    cop
    #
    wceq
    #
    vd
    cD
    wrex
    vb
    cB
    wrex
    #
    @35
    @23
    @38
    vx
    @19
    @23
    @7
    @15
    wa
    #
    vd
    cD
    wrex
    #
    vb
    cB
    wrex
    #
    vc
    cC
    wral
    va
    cA
    wral
    #
    @38
    vx
    @19
    wral
    @23
    @8
    @16
    wa
    #
    vc
    cC
    wral
    #
    va
    cA
    wral
    #
    @42
    @17
    @9
    @45
    @17
    @8
    @44
    va
    cA
    @8
    @17
    @44
    @8
    @16
    @43
    vc
    cC
    @8
    @16
    pm3.2
    ralimdv
    com12
    ralimdv
    impcom
    @43
    @41
    va
    vc
    cA
    cC
    @16
    @8
    @41
    @16
    @7
    @40
    vb
    cB
    @7
    @16
    @40
    @7
    @15
    @39
    vd
    cD
    @7
    @15
    pm3.2
    reximdv
    com12
    reximdv
    impcom
    2ralimi
    syl
    @38
    @41
    vx
    va
    vc
    cA
    cC
    @32
    @3
    @11
    cop
    #
    wceq
    #
    @37
    @39
    vb
    vd
    cB
    cD
    @47
    @37
    @46
    @36
    wceq
    @39
    @32
    @46
    @36
    eqeq1
    @3
    @11
    @6
    @14
    va
    vex
    vc
    vex
    opth
    syl6bb
    2rexbidv
    ralxp
    sylibr
    r19.21bi
    @34
    @37
    vy
    vb
    vd
    cB
    cD
    @24
    @4
    @12
    cop
    wceq
    #
    @29
    @36
    @32
    @48
    @26
    @6
    @28
    @14
    @48
    @25
    @4
    @5
    @4
    @12
    @24
    vb
    vex
    #
    vd
    vex
    #
    op1std
    fveq2d
    @48
    @27
    @12
    @13
    @4
    @12
    @24
    @49
    @50
    op2ndd
    fveq2d
    opeq12d
    eqeq2d
    rexxp
    sylibr
    adantll
    wdom2d
    expr
    exlimdv
    ex
    exlimdv
    mp2d
end
