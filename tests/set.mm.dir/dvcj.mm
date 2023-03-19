include "cc.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "wa.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "cv.mm"
include "ccj.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "wfun.mm"
include "wcel.mm"
include "wbr.mm"
include "wceq.mm"
include "dvf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "dvcjbr.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "mpteq2dva.mm"
include "cjf.mm"
include "fco.mm"
include "mpan.mm"
include "ad2antrr.mm"
include "vex.mm"
include "fvex.mm"
include "breldm.mm"
include "syl.mm"
include "ex.mm"
include "ssrdv.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "cjcjd.mm"
include "cjcld.mm"
include "simpl.mm"
include "feqmptd.mm"
include "a1i.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "dmeqd.mm"
include "sseqtrd.mm"
include "eqssd.mm"
include "feq2d.mm"
include "mpbii.mm"
include "ffvelrni.mm"
include "adantl.mm"

theorem dvcj
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : X --> CC /\ X C_ RR ) -> ( RR _D ( * o. F ) ) = ( * o. ( RR _D F ) ) )

  proof
    cX
    cc
    cF
    wf
    #
    cX
    cr
    wss
    #
    wa
    #
    vx
    cr
    cF
    cdv
    co
    #
    cdm
    #
    vx
    cv
    #
    cr
    ccj
    cF
    ccom
    #
    cdv
    co
    #
    cfv
    #
    cmpt
    vx
    @4
    @5
    @3
    cfv
    #
    ccj
    cfv
    #
    cmpt
    @7
    ccj
    @3
    ccom
    @2
    vx
    @4
    @8
    @10
    @7
    wfun
    #
    @2
    @5
    @4
    wcel
    #
    wa
    #
    @5
    @10
    @7
    wbr
    #
    @8
    @10
    wceq
    @7
    cdm
    #
    cc
    @7
    wf
    #
    @11
    @6
    dvf
    #
    @15
    cc
    @7
    ffun
    ax-mp
    @13
    @5
    cF
    cX
    @0
    @1
    @12
    simpll
    @0
    @1
    @12
    simplr
    @2
    @12
    simpr
    dvcjbr
    #
    @5
    @10
    @7
    funbrfv
    mpsyl
    mpteq2dva
    @2
    vx
    @4
    cc
    @7
    @2
    @16
    @4
    cc
    @7
    wf
    @17
    @2
    @15
    @4
    cc
    @7
    @2
    @15
    @4
    @2
    @15
    cr
    ccj
    @6
    ccom
    #
    cdv
    co
    #
    cdm
    #
    @4
    @2
    vx
    @15
    @21
    @2
    @5
    @15
    wcel
    #
    @5
    @21
    wcel
    #
    @2
    @22
    wa
    #
    @5
    @8
    ccj
    cfv
    #
    @20
    wbr
    @23
    @24
    @5
    @6
    cX
    @0
    cX
    cc
    @6
    wf
    #
    @1
    @22
    cc
    cc
    ccj
    wf
    #
    @0
    @26
    cjf
    cX
    cc
    cc
    ccj
    cF
    fco
    mpan
    ad2antrr
    @0
    @1
    @22
    simplr
    @2
    @22
    simpr
    dvcjbr
    @5
    @25
    @20
    vx
    vex
    #
    @8
    ccj
    fvex
    breldm
    syl
    ex
    ssrdv
    @2
    @20
    @3
    @2
    @19
    cF
    cr
    cdv
    @2
    vx
    cX
    @5
    cF
    cfv
    #
    ccj
    cfv
    #
    ccj
    cfv
    #
    cmpt
    vx
    cX
    @29
    cmpt
    @19
    cF
    @2
    vx
    cX
    @31
    @29
    @2
    @5
    cX
    wcel
    #
    wa
    #
    @29
    @0
    @32
    @29
    cc
    wcel
    @1
    cX
    cc
    @5
    cF
    ffvelrn
    adantlr
    #
    cjcjd
    mpteq2dva
    @2
    vx
    vy
    cX
    cc
    @30
    vy
    cv
    #
    ccj
    cfv
    #
    @31
    @6
    ccj
    @33
    @29
    @34
    cjcld
    @2
    vx
    vy
    cX
    cc
    @29
    @36
    @30
    cF
    ccj
    @34
    @2
    vx
    cX
    cc
    cF
    @0
    @1
    simpl
    feqmptd
    #
    @2
    vy
    cc
    cc
    ccj
    @27
    @2
    cjf
    a1i
    feqmptd
    #
    @35
    @29
    ccj
    fveq2
    fmptco
    @38
    @35
    @30
    ccj
    fveq2
    fmptco
    @37
    3eqtr4d
    oveq2d
    dmeqd
    sseqtrd
    @2
    vx
    @4
    @15
    @2
    @12
    @22
    @13
    @14
    @22
    @18
    @5
    @10
    @7
    @28
    @9
    ccj
    fvex
    breldm
    syl
    ex
    ssrdv
    eqssd
    feq2d
    mpbii
    feqmptd
    @2
    vx
    vy
    @4
    cc
    @9
    @36
    @10
    @3
    ccj
    @12
    @9
    cc
    wcel
    @2
    @4
    cc
    @5
    @3
    cF
    dvf
    #
    ffvelrni
    adantl
    @2
    vx
    @4
    cc
    @3
    @4
    cc
    @3
    wf
    @2
    @39
    a1i
    feqmptd
    @38
    @35
    @9
    ccj
    fveq2
    fmptco
    3eqtr4d
end
