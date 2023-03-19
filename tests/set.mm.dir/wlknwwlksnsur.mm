include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "wlknwwlksnfun.mm"
include "sylan.mm"
include "cwwlksn.mm"
include "co.mm"
include "eleq2i.mm"
include "c2nd.mm"
include "c1st.mm"
include "chash.mm"
include "cwlks.mm"
include "crab.mm"
include "wex.mm"
include "wbr.mm"
include "wb.mm"
include "wlklnwwlkn.mm"
include "adantr.mm"
include "cop.mm"
include "df-br.mm"
include "vex.mm"
include "op1st.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "cvv.mm"
include "elex.mm"
include "eleq1.mm"
include "biimparc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "biimpar.mm"
include "op2nd.mm"
include "syl6req.mm"
include "jca31.mm"
include "ex.mm"
include "spcimedv.mm"
include "imp.mm"
include "syl2anb.mm"
include "exlimiv.mm"
include "syl6bir.mm"
include "weq.mm"
include "elrab.mm"
include "anbi1i.mm"
include "exbii.mm"
include "sylibr.mm"
include "df-rex.mm"
include "rexeqi.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqeq2d.mm"
include "rexbiia.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem wlknwwlksnsur
  let vt: setvar t
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vp: setvar p
  let vv: setvar v
  let vw: setvar w
  let vu: setvar u
  let vf: setvar f
  assume wlknwwlksnbij.t: |- T = { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N }
  assume wlknwwlksnbij.w: |- W = ( N WWalksN G )
  assume wlknwwlksnbij.f: |- F = ( t e. T |-> ( 2nd ` t ) )

  disjoint G p
  disjoint G t
  disjoint p t
  disjoint N p
  disjoint N t
  disjoint T t
  disjoint W t
  disjoint F p
  disjoint T p
  disjoint W p
  disjoint F v
  disjoint F w
  disjoint v w
  disjoint G v
  disjoint G w
  disjoint p v
  disjoint p w
  disjoint t v
  disjoint t w
  disjoint N v
  disjoint N w
  disjoint T v
  disjoint T w
  disjoint F u
  disjoint p u
  disjoint G f
  disjoint G u
  disjoint f p
  disjoint f u
  disjoint N f
  disjoint N u
  disjoint T u
  disjoint t u
  disjoint W u
  assert |- ( ( G e. USPGraph /\ N e. NN0 ) -> F : T -onto-> W )

  proof
    cG
    cuspgr
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
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
    cT
    cW
    cF
    wfo
    @0
    cG
    cupgr
    wcel
    @1
    @3
    cG
    uspgrupgr
    vt
    cT
    cF
    cG
    cN
    cW
    vp
    wlknwwlksnbij.t
    wlknwwlksnbij.w
    wlknwwlksnbij.f
    wlknwwlksnfun
    sylan
    @2
    @8
    vp
    cW
    @4
    cW
    wcel
    @2
    @4
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    @8
    cW
    @9
    @4
    wlknwwlksnbij.w
    eleq2i
    @2
    @10
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
    @11
    @13
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
    vp
    cG
    cwlks
    cfv
    #
    crab
    #
    wrex
    #
    @14
    @11
    @5
    @19
    wcel
    #
    @13
    wa
    #
    vu
    wex
    #
    @20
    @11
    @5
    @18
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
    wa
    #
    @13
    wa
    #
    vu
    wex
    #
    @23
    @2
    @10
    @30
    @2
    @10
    vf
    cv
    #
    @4
    @18
    wbr
    #
    @31
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
    #
    @30
    @0
    @36
    @10
    wb
    @1
    @4
    vf
    cG
    cN
    wlklnwwlkn
    adantr
    @35
    @30
    vf
    @32
    @31
    @4
    cop
    #
    @18
    wcel
    #
    @37
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    @30
    @34
    @31
    @4
    @18
    df-br
    @33
    @40
    cN
    @31
    @39
    chash
    @39
    @31
    @31
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
    @38
    @41
    @30
    @38
    @29
    @41
    vu
    @37
    cvv
    @37
    @18
    elex
    @38
    @5
    @37
    wceq
    #
    wa
    #
    @41
    @29
    @45
    @41
    wa
    @24
    @27
    @13
    @45
    @24
    @41
    @44
    @24
    @38
    @5
    @37
    @18
    eleq1
    biimparc
    adantr
    @45
    @27
    @41
    @44
    @27
    @41
    wb
    @38
    @44
    @26
    @40
    cN
    @44
    @25
    @39
    chash
    @5
    @37
    c1st
    fveq2
    fveq2d
    eqeq1d
    adantl
    biimpar
    @45
    @13
    @41
    @44
    @13
    @38
    @44
    @12
    @37
    c2nd
    cfv
    @4
    @5
    @37
    c2nd
    fveq2
    @31
    @4
    @42
    @43
    op2nd
    syl6req
    adantl
    adantr
    jca31
    ex
    spcimedv
    imp
    syl2anb
    exlimiv
    syl6bir
    imp
    @22
    @29
    vu
    @21
    @28
    @13
    @17
    @27
    vp
    @5
    @18
    vp
    vu
    weq
    #
    @16
    @26
    cN
    @46
    @15
    @25
    chash
    @4
    @5
    c1st
    fveq2
    fveq2d
    eqeq1d
    elrab
    anbi1i
    exbii
    sylibr
    @13
    vu
    @19
    df-rex
    sylibr
    @13
    vu
    cT
    @19
    wlknwwlksnbij.t
    rexeqi
    sylibr
    @7
    @13
    vu
    cT
    @5
    cT
    wcel
    @6
    @12
    @4
    vt
    @5
    vt
    cv
    #
    c2nd
    cfv
    @12
    cT
    cF
    @47
    @5
    c2nd
    fveq2
    wlknwwlksnbij.f
    @5
    c2nd
    fvex
    fvmpt
    eqeq2d
    rexbiia
    sylibr
    sylan2b
    ralrimiva
    vu
    vp
    cT
    cW
    cF
    dffo3
    sylanbrc
end
