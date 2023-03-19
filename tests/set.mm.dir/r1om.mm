include "com.mm"
include "cr1.mm"
include "cfv.mm"
include "cima.mm"
include "cuni.mm"
include "cen.mm"
include "cv.mm"
include "ciun.mm"
include "cvv.mm"
include "wcel.mm"
include "wlim.mm"
include "wceq.mm"
include "omex.mm"
include "limom.mm"
include "r1lim.mm"
include "mp2an.mm"
include "con0.mm"
include "wfn.mm"
include "wfun.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "funiunfv.mm"
include "mp2b.mm"
include "eqtri.mm"
include "cdm.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "csn.mm"
include "cxp.mm"
include "ccrd.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "wf1o.mm"
include "wbr.mm"
include "weq.mm"
include "iuneq1.mm"
include "sneq.mm"
include "pweq.mm"
include "xpeq12d.mm"
include "cbviunv.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "dmeq.mm"
include "pweqd.mm"
include "imaeq1.mm"
include "mpteq12dv.mm"
include "imaeq2.mm"
include "eqid.mm"
include "ackbij2.mm"
include "fvex.mm"
include "eqeltrri.mm"
include "f1oen.mm"
include "ax-mp.mm"
include "eqbrtri.mm"

theorem r1om
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f


  assert |- ( R1 ` _om ) ~~ _om

  proof
    com
    cr1
    cfv
    #
    cr1
    com
    cima
    cuni
    #
    com
    cen
    @0
    va
    com
    va
    cv
    #
    cr1
    cfv
    ciun
    #
    @1
    com
    cvv
    wcel
    com
    wlim
    @0
    @3
    wceq
    omex
    limom
    va
    com
    cvv
    r1lim
    mp2an
    cr1
    con0
    wfn
    cr1
    wfun
    @3
    @1
    wceq
    r1fnon
    con0
    cr1
    fnfun
    va
    com
    cr1
    funiunfv
    mp2b
    eqtri
    #
    @1
    com
    vc
    cvv
    vd
    vc
    cv
    #
    cdm
    #
    cpw
    #
    @5
    vd
    cv
    #
    cima
    #
    ve
    com
    cpw
    cfn
    cin
    #
    vf
    ve
    cv
    #
    vf
    cv
    #
    csn
    #
    @12
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    c0
    crdg
    com
    cima
    cuni
    #
    wf1o
    @1
    com
    cen
    wbr
    va
    vb
    @18
    @21
    @22
    ve
    va
    @10
    @17
    vb
    @2
    vb
    cv
    #
    csn
    #
    @23
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    ve
    va
    weq
    #
    @16
    @27
    ccrd
    @28
    @16
    vf
    @2
    @15
    ciun
    @27
    vf
    @11
    @2
    @15
    iuneq1
    vf
    vb
    @2
    @15
    @26
    vf
    vb
    weq
    @13
    @24
    @14
    @25
    @12
    @23
    sneq
    @12
    @23
    pweq
    xpeq12d
    cbviunv
    syl6eq
    fveq2d
    cbvmptv
    vc
    va
    cvv
    @20
    vb
    @2
    cdm
    #
    cpw
    #
    @2
    @23
    cima
    #
    @18
    cfv
    #
    cmpt
    #
    vc
    va
    weq
    #
    @20
    vd
    @30
    @2
    @8
    cima
    #
    @18
    cfv
    #
    cmpt
    @33
    @34
    vd
    @7
    @19
    @30
    @36
    @34
    @6
    @29
    @5
    @2
    dmeq
    pweqd
    @34
    @9
    @35
    @18
    @5
    @2
    @8
    imaeq1
    fveq2d
    mpteq12dv
    vd
    vb
    @30
    @36
    @32
    vd
    vb
    weq
    @35
    @31
    @18
    @8
    @23
    @2
    imaeq2
    fveq2d
    cbvmptv
    syl6eq
    cbvmptv
    @22
    eqid
    ackbij2
    @1
    com
    @22
    @0
    @1
    cvv
    @4
    com
    cr1
    fvex
    eqeltrri
    f1oen
    ax-mp
    eqbrtri
end
