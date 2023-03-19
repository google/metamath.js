include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "wlkwwlkfun.mm"
include "syl3an1.mm"
include "cwwlksn.mm"
include "co.mm"
include "cc0.mm"
include "wa.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "c2nd.mm"
include "c1st.mm"
include "chash.mm"
include "cwlks.mm"
include "crab.mm"
include "wex.mm"
include "wbr.mm"
include "wi.mm"
include "wlklnwwlkn.mm"
include "cop.mm"
include "df-br.mm"
include "vex.mm"
include "op1st.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "op2nd.mm"
include "fveq1i.mm"
include "cvv.mm"
include "opex.mm"
include "a1i.mm"
include "simpll.mm"
include "simpr.mm"
include "anim1i.mm"
include "jca31.mm"
include "eleq1.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "impancom.mm"
include "spcimedv.mm"
include "syl5bi.mm"
include "syl2anb.mm"
include "exlimiv.mm"
include "syl6bir.mm"
include "imp32.mm"
include "elrab.mm"
include "anbi1i.mm"
include "exbii.mm"
include "sylibr.mm"
include "df-rex.mm"
include "rexeqi.mm"
include "fvex.mm"
include "fvmpt.mm"
include "rexbiia.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "3ad2ant1.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem wlkwwlksur
  let vw: setvar w
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume wlkwwlkbij.t: |- T = { p e. ( Walks ` G ) | ( ( # ` ( 1st ` p ) ) = N /\ ( ( 2nd ` p ) ` 0 ) = P ) }
  assume wlkwwlkbij.w: |- W = { w e. ( N WWalksN G ) | ( w ` 0 ) = P }
  assume wlkwwlkbij.f: |- F = ( t e. T |-> ( 2nd ` t ) )

  disjoint G p
  disjoint G t
  disjoint G w
  disjoint p t
  disjoint p w
  disjoint t w
  disjoint N p
  disjoint N t
  disjoint N w
  disjoint P p
  disjoint P t
  disjoint P w
  disjoint T t
  disjoint T w
  disjoint V t
  disjoint W t
  disjoint F w
  disjoint V w
  disjoint F p
  disjoint T p
  disjoint W p
  disjoint F v
  disjoint v w
  disjoint G v
  disjoint p v
  disjoint N v
  disjoint P v
  disjoint T v
  disjoint t v
  disjoint V v
  disjoint F u
  disjoint p u
  disjoint G f
  disjoint G u
  disjoint f p
  disjoint f u
  disjoint f w
  disjoint u w
  disjoint N f
  disjoint N u
  disjoint P f
  disjoint P u
  disjoint T u
  disjoint t u
  disjoint W u
  assert |- ( ( G e. USPGraph /\ P e. V /\ N e. NN0 ) -> F : T -onto-> W )

  proof
    cG
    cuspgr
    wcel
    #
    cP
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    cT
    cW
    cF
    wf
    #
    vp
    cv
    #
    vu
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vu
    cT
    wrex
    #
    vp
    cW
    wral
    #
    cT
    cW
    cF
    wfo
    @0
    cG
    cupgr
    wcel
    @1
    @2
    @3
    cG
    uspgrupgr
    vw
    vt
    cP
    cT
    cF
    cG
    cN
    cV
    cW
    vp
    wlkwwlkbij.t
    wlkwwlkbij.w
    wlkwwlkbij.f
    wlkwwlkfun
    syl3an1
    @0
    @1
    @9
    @2
    @0
    @8
    vp
    cW
    @4
    cW
    wcel
    @0
    @4
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @4
    cfv
    #
    cP
    wceq
    #
    wa
    #
    @8
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    @13
    vw
    @4
    @10
    cW
    vw
    vp
    weq
    @16
    @12
    cP
    cc0
    @15
    @4
    fveq1
    eqeq1d
    wlkwwlkbij.w
    elrab2
    @0
    @14
    wa
    #
    @4
    @5
    c2nd
    cfv
    #
    wceq
    #
    vu
    cT
    wrex
    #
    @8
    @17
    @19
    vu
    @4
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    cc0
    @4
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vp
    cG
    cwlks
    cfv
    #
    crab
    #
    wrex
    #
    @20
    @17
    @5
    @29
    wcel
    #
    @19
    wa
    #
    vu
    wex
    #
    @30
    @17
    @5
    @28
    wcel
    #
    @5
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    cc0
    @18
    cfv
    #
    cP
    wceq
    #
    wa
    #
    wa
    #
    @19
    wa
    #
    vu
    wex
    #
    @33
    @0
    @11
    @13
    @43
    @0
    @11
    vf
    cv
    #
    @4
    @28
    wbr
    #
    @44
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vf
    wex
    @13
    @43
    wi
    #
    @4
    vf
    cG
    cN
    wlklnwwlkn
    @48
    @49
    vf
    @45
    @44
    @4
    cop
    #
    @28
    wcel
    #
    @50
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    @49
    @47
    @44
    @4
    @28
    df-br
    @46
    @53
    cN
    @44
    @52
    chash
    @52
    @44
    @44
    @4
    vf
    vex
    #
    vp
    vex
    #
    op1st
    eqcomi
    fveq2i
    eqeq1i
    @13
    cc0
    @50
    c2nd
    cfv
    #
    cfv
    #
    cP
    wceq
    #
    @51
    @54
    wa
    #
    @43
    @12
    @58
    cP
    cc0
    @4
    @57
    @57
    @4
    @44
    @4
    @55
    @56
    op2nd
    eqcomi
    #
    fveq1i
    eqeq1i
    @60
    @42
    @59
    vu
    @50
    cvv
    @50
    cvv
    wcel
    @60
    @44
    @4
    opex
    a1i
    @60
    @59
    @5
    @50
    wceq
    #
    @42
    @60
    @59
    wa
    #
    @42
    @62
    @51
    @54
    @59
    wa
    #
    wa
    #
    @4
    @57
    wceq
    #
    wa
    @63
    @51
    @64
    @66
    @51
    @54
    @59
    simpll
    @60
    @54
    @59
    @51
    @54
    simpr
    anim1i
    @66
    @63
    @61
    a1i
    jca31
    @62
    @41
    @65
    @19
    @66
    @62
    @34
    @51
    @40
    @64
    @5
    @50
    @28
    eleq1
    @62
    @37
    @54
    @39
    @59
    @62
    @36
    @53
    cN
    @62
    @35
    @52
    chash
    @5
    @50
    c1st
    fveq2
    fveq2d
    eqeq1d
    @62
    @38
    @58
    cP
    @62
    cc0
    @18
    @57
    @5
    @50
    c2nd
    fveq2
    #
    fveq1d
    eqeq1d
    anbi12d
    anbi12d
    @62
    @18
    @57
    @4
    @67
    eqeq2d
    anbi12d
    syl5ibrcom
    impancom
    spcimedv
    syl5bi
    syl2anb
    exlimiv
    syl6bir
    imp32
    @32
    @42
    vu
    @31
    @41
    @19
    @27
    @40
    vp
    @5
    @28
    vp
    vu
    weq
    #
    @23
    @37
    @26
    @39
    @68
    @22
    @36
    cN
    @68
    @21
    @35
    chash
    @4
    @5
    c1st
    fveq2
    fveq2d
    eqeq1d
    @68
    @25
    @38
    cP
    @68
    cc0
    @24
    @18
    @4
    @5
    c2nd
    fveq2
    fveq1d
    eqeq1d
    anbi12d
    elrab
    anbi1i
    exbii
    sylibr
    @19
    vu
    @29
    df-rex
    sylibr
    @19
    vu
    cT
    @29
    wlkwwlkbij.t
    rexeqi
    sylibr
    @7
    @19
    vu
    cT
    @5
    cT
    wcel
    @6
    @18
    @4
    vt
    @5
    vt
    cv
    #
    c2nd
    cfv
    @18
    cT
    cF
    @69
    @5
    c2nd
    fveq2
    wlkwwlkbij.f
    @5
    c2nd
    fvex
    fvmpt
    eqeq2d
    rexbiia
    sylibr
    sylan2b
    ralrimiva
    3ad2ant1
    vu
    vp
    cT
    cW
    cF
    dffo3
    sylanbrc
end
