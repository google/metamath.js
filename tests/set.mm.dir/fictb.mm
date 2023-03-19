include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cfi.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "brdomi.mm"
include "adantl.mm"
include "cvv.mm"
include "wi.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "ccrd.mm"
include "cdm.mm"
include "cint.mm"
include "cmpt.mm"
include "wfo.mm"
include "con0.mm"
include "omelon2.mm"
include "ad2antlr.mm"
include "wss.mm"
include "pwexg.mm"
include "ad2antrr.mm"
include "inex1g.mm"
include "syl.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "crn.mm"
include "cen.mm"
include "cima.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1opwfi.mm"
include "f1oeng.mm"
include "syl2anc.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "sspwb.mm"
include "sylib.mm"
include "ssrin.mm"
include "sylc.mm"
include "cxp.mm"
include "ciun.mm"
include "weq.mm"
include "sneq.mm"
include "pweq.mm"
include "xpeq12d.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "ackbij1.mm"
include "sylancl.mm"
include "domentr.mm"
include "endomtr.mm"
include "domtr.mm"
include "ondomen.mm"
include "eqid.mm"
include "fifo.mm"
include "fodomnum.mm"
include "ex.mm"
include "exlimdv.mm"
include "sylan2.mm"
include "mpd.mm"
include "fvex.mm"
include "ssfii.mm"
include "mpsyl.mm"
include "impbid.mm"

theorem fictb
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. B -> ( A ~<_ _om <-> ( fi ` A ) ~<_ _om ) )

  proof
    cA
    cB
    wcel
    #
    cA
    com
    cdom
    wbr
    #
    cA
    cfi
    cfv
    #
    com
    cdom
    wbr
    #
    @0
    @1
    @3
    @0
    @1
    wa
    cA
    com
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @3
    @1
    @6
    @0
    cA
    com
    vf
    brdomi
    adantl
    @1
    @0
    com
    cvv
    wcel
    #
    @6
    @3
    wi
    cA
    com
    cdom
    reldom
    brrelex2i
    @0
    @7
    wa
    #
    @5
    @3
    vf
    @8
    @5
    @3
    @8
    @5
    wa
    #
    @2
    cA
    cpw
    #
    cfn
    cin
    #
    c0
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    @13
    com
    cdom
    wbr
    #
    @3
    @9
    @13
    ccrd
    cdm
    wcel
    #
    @13
    @2
    vy
    @13
    vy
    cv
    #
    cint
    cmpt
    #
    wfo
    #
    @14
    @9
    com
    con0
    wcel
    #
    @15
    @16
    @7
    @20
    @0
    @5
    omelon2
    ad2antlr
    @9
    @13
    @11
    cdom
    wbr
    #
    @11
    com
    cdom
    wbr
    #
    @15
    @9
    @11
    cvv
    wcel
    #
    @13
    @11
    wss
    @21
    @9
    @10
    cvv
    wcel
    #
    @23
    @0
    @24
    @7
    @5
    cA
    cB
    pwexg
    ad2antrr
    @10
    cfn
    cvv
    inex1g
    syl
    #
    @11
    @12
    difss
    @13
    @11
    cvv
    ssdomg
    mpisyl
    @9
    @11
    @4
    crn
    #
    cpw
    #
    cfn
    cin
    #
    cen
    wbr
    #
    @28
    com
    cdom
    wbr
    #
    @22
    @9
    @23
    @11
    @28
    vx
    @11
    @4
    vx
    cv
    #
    cima
    cmpt
    #
    wf1o
    #
    @29
    @25
    @9
    cA
    @26
    @4
    wf1o
    #
    @33
    @5
    @34
    @8
    cA
    com
    @4
    f1f1orn
    adantl
    cA
    @26
    @4
    vx
    f1opwfi
    syl
    @11
    @28
    cvv
    @32
    f1oeng
    syl2anc
    @9
    @28
    com
    cpw
    #
    cfn
    cin
    #
    cdom
    wbr
    #
    @36
    com
    cen
    wbr
    #
    @30
    @9
    @36
    cvv
    wcel
    #
    @28
    @36
    wss
    #
    @37
    @9
    @35
    cvv
    wcel
    #
    @39
    @7
    @41
    @0
    @5
    com
    cvv
    pwexg
    ad2antlr
    @35
    cfn
    cvv
    inex1g
    syl
    #
    @9
    @27
    @35
    wss
    #
    @40
    @9
    @26
    com
    wss
    #
    @43
    @9
    cA
    com
    @4
    wf
    #
    @44
    @5
    @45
    @8
    cA
    com
    @4
    f1f
    adantl
    cA
    com
    @4
    frn
    syl
    @26
    com
    sspwb
    sylib
    @27
    @35
    cfn
    ssrin
    syl
    @28
    @36
    cvv
    ssdomg
    sylc
    @9
    @39
    @36
    com
    vx
    @36
    vf
    @31
    @4
    csn
    #
    @4
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
    wf1o
    @38
    @42
    vy
    vz
    @51
    vx
    vy
    @36
    @50
    vz
    @17
    vz
    cv
    #
    csn
    #
    @52
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    vx
    vy
    weq
    #
    @49
    @56
    ccrd
    @57
    @49
    vz
    @31
    @55
    ciun
    @56
    vf
    vz
    @31
    @48
    @55
    vf
    vz
    weq
    @46
    @53
    @47
    @54
    @4
    @52
    sneq
    @4
    @52
    pweq
    xpeq12d
    cbviunv
    vz
    @31
    @17
    @55
    iuneq1
    syl5eq
    fveq2d
    cbvmptv
    ackbij1
    @36
    com
    cvv
    @51
    f1oeng
    sylancl
    @28
    @36
    com
    domentr
    syl2anc
    @11
    @28
    com
    endomtr
    syl2anc
    @13
    @11
    com
    domtr
    syl2anc
    #
    com
    @13
    ondomen
    syl2anc
    @0
    @19
    @7
    @5
    vy
    cA
    @18
    cB
    @18
    eqid
    fifo
    ad2antrr
    @13
    @2
    @18
    fodomnum
    sylc
    @58
    @2
    @13
    com
    domtr
    syl2anc
    ex
    exlimdv
    sylan2
    mpd
    ex
    @0
    cA
    @2
    cdom
    wbr
    #
    @3
    @1
    wi
    @2
    cvv
    wcel
    @0
    cA
    @2
    wss
    @59
    cA
    cfi
    fvex
    cA
    cB
    ssfii
    cA
    @2
    cvv
    ssdomg
    mpsyl
    @59
    @3
    @1
    cA
    @2
    com
    domtr
    ex
    syl
    impbid
end
