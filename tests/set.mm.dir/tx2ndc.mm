include "c2ndc.mm"
include "wcel.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ctb.mm"
include "wrex.mm"
include "ctx.mm"
include "co.mm"
include "is2ndc.mm"
include "reeanv.mm"
include "an4.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "txbasval.mm"
include "eqid.mm"
include "txval.mm"
include "eqtrd.mm"
include "adantr.mm"
include "txbas.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "cen.mm"
include "vex.mm"
include "xpdom1.mm"
include "omex.mm"
include "xpdom2.mm"
include "domtr.mm"
include "syl2an.mm"
include "adantl.mm"
include "xpomen.mm"
include "domentr.mm"
include "sylancl.mm"
include "ondomen.mm"
include "sylancr.mm"
include "wfn.mm"
include "xpex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "dffn4.mm"
include "sylib.mm"
include "fodomnum.mm"
include "sylc.mm"
include "syl2anc.mm"
include "2ndci.mm"
include "eqeltrd.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem tx2ndc
  let cR: class R
  let cS: class S
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R e. 2ndc /\ S e. 2ndc ) -> ( R tX S ) e. 2ndc )

  proof
    cR
    c2ndc
    wcel
    vr
    cv
    #
    com
    cdom
    wbr
    #
    @0
    ctg
    cfv
    #
    cR
    wceq
    #
    wa
    #
    vr
    ctb
    wrex
    #
    vs
    cv
    #
    com
    cdom
    wbr
    #
    @6
    ctg
    cfv
    #
    cS
    wceq
    #
    wa
    #
    vs
    ctb
    wrex
    #
    cR
    cS
    ctx
    co
    #
    c2ndc
    wcel
    #
    cS
    c2ndc
    wcel
    vr
    cR
    is2ndc
    vs
    cS
    is2ndc
    @5
    @11
    wa
    @4
    @10
    wa
    #
    vs
    ctb
    wrex
    vr
    ctb
    wrex
    @13
    @4
    @10
    vr
    vs
    ctb
    ctb
    reeanv
    @14
    @13
    vr
    vs
    ctb
    ctb
    @14
    @1
    @7
    wa
    #
    @3
    @9
    wa
    #
    wa
    @0
    ctb
    wcel
    @6
    ctb
    wcel
    wa
    #
    @13
    @1
    @3
    @7
    @9
    an4
    @17
    @15
    @16
    @13
    @17
    @15
    wa
    #
    @2
    @8
    ctx
    co
    #
    c2ndc
    wcel
    @16
    @13
    @18
    @19
    vx
    vy
    @0
    @6
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    c2ndc
    @17
    @19
    @25
    wceq
    @15
    @17
    @19
    @0
    @6
    ctx
    co
    @25
    @0
    @6
    ctb
    ctb
    txbasval
    vx
    vy
    @24
    @0
    @6
    ctb
    ctb
    @24
    eqid
    #
    txval
    eqtrd
    adantr
    @18
    @24
    ctb
    wcel
    #
    @24
    com
    cdom
    wbr
    #
    @25
    c2ndc
    wcel
    @17
    @27
    @15
    vx
    vy
    @24
    @0
    @6
    @26
    txbas
    adantr
    @18
    @24
    @0
    @6
    cxp
    #
    cdom
    wbr
    #
    @29
    com
    cdom
    wbr
    #
    @28
    @18
    @29
    ccrd
    cdm
    wcel
    #
    @29
    @24
    @23
    wfo
    #
    @30
    @18
    com
    con0
    wcel
    @31
    @32
    omelon
    @18
    @29
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @34
    com
    cen
    wbr
    @31
    @15
    @35
    @17
    @1
    @29
    com
    @6
    cxp
    #
    cdom
    wbr
    @36
    @34
    cdom
    wbr
    @35
    @7
    @0
    com
    @6
    vs
    vex
    xpdom1
    @6
    com
    com
    omex
    xpdom2
    @29
    @36
    @34
    domtr
    syl2an
    adantl
    xpomen
    @29
    @34
    com
    domentr
    sylancl
    #
    com
    @29
    ondomen
    sylancr
    @18
    @23
    @29
    wfn
    #
    @33
    @38
    @18
    vx
    vy
    @0
    @6
    @22
    @23
    @23
    eqid
    @20
    @21
    vx
    vex
    vy
    vex
    xpex
    fnmpt2i
    a1i
    @29
    @23
    dffn4
    sylib
    @29
    @24
    @23
    fodomnum
    sylc
    @37
    @24
    @29
    com
    domtr
    syl2anc
    @24
    2ndci
    syl2anc
    eqeltrd
    @16
    @19
    @12
    c2ndc
    @2
    cR
    @8
    cS
    ctx
    oveq12
    eleq1d
    syl5ibcom
    expimpd
    syl5bi
    rexlimivv
    sylbir
    syl2anb
end
