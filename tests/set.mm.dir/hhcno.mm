include "cv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "chil.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cmap.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "ccop.mm"
include "ccn.mm"
include "df-rab.mm"
include "df-cnop.mm"
include "wf.mm"
include "wceq.mm"
include "hilmetdval.mm"
include "normsub.mm"
include "eqtrd.mm"
include "adantll.mm"
include "breq1d.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "syl.mm"
include "anassrs.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "pm5.32i.mm"
include "cxmt.mm"
include "wb.mm"
include "hilxmet.mm"
include "metcn.mm"
include "mp2an.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "abbi2i.mm"
include "3eqtr4i.mm"

theorem hhcno
  let cD: class D
  let cJ: class J
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cK: class K
  assume hhcn.1: |- D = ( normh o. -h )
  assume hhcn.2: |- J = ( MetOpen ` D )


  assert |- ContOp = ( J Cn J )

  proof
    vw
    cv
    #
    vx
    cv
    #
    cmv
    co
    cno
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @0
    vt
    cv
    #
    cfv
    #
    @1
    @5
    cfv
    #
    cmv
    co
    cno
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    chil
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    chil
    wral
    #
    vt
    chil
    chil
    cmap
    co
    #
    crab
    @5
    @16
    wcel
    #
    @15
    wa
    #
    vt
    cab
    ccop
    cJ
    cJ
    ccn
    co
    #
    @15
    vt
    @16
    df-rab
    vx
    vy
    vz
    vw
    vt
    df-cnop
    @18
    vt
    @19
    chil
    chil
    @5
    wf
    #
    @1
    @0
    cD
    co
    #
    @3
    clt
    wbr
    #
    @7
    @6
    cD
    co
    #
    @9
    clt
    wbr
    #
    wi
    #
    vw
    chil
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    chil
    wral
    #
    wa
    #
    @20
    @15
    wa
    @5
    @19
    wcel
    #
    @18
    @20
    @29
    @15
    @20
    @28
    @14
    vx
    chil
    @20
    @1
    chil
    wcel
    #
    wa
    #
    @27
    @13
    vy
    crp
    @33
    @26
    @12
    vz
    crp
    @33
    @25
    @11
    vw
    chil
    @33
    @0
    chil
    wcel
    #
    wa
    #
    @22
    @4
    @24
    @10
    @35
    @21
    @2
    @3
    clt
    @32
    @34
    @21
    @2
    wceq
    @20
    @32
    @34
    wa
    #
    @21
    @1
    @0
    cmv
    co
    cno
    cfv
    @2
    @1
    @0
    cD
    hhcn.1
    hilmetdval
    @1
    @0
    normsub
    eqtrd
    adantll
    breq1d
    @35
    @23
    @8
    @9
    clt
    @20
    @32
    @34
    @23
    @8
    wceq
    #
    @20
    @36
    wa
    @7
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    wa
    #
    @37
    @20
    @32
    @38
    @34
    @39
    chil
    chil
    @1
    @5
    ffvelrn
    chil
    chil
    @0
    @5
    ffvelrn
    anim12dan
    @40
    @23
    @7
    @6
    cmv
    co
    cno
    cfv
    @8
    @7
    @6
    cD
    hhcn.1
    hilmetdval
    @7
    @6
    normsub
    eqtrd
    syl
    anassrs
    breq1d
    imbi12d
    ralbidva
    rexbidv
    ralbidv
    ralbidva
    pm5.32i
    cD
    chil
    cxmt
    cfv
    wcel
    #
    @41
    @31
    @30
    wb
    cD
    hhcn.1
    hilxmet
    #
    @42
    vx
    vy
    vz
    vw
    cD
    cD
    @5
    cJ
    cJ
    chil
    chil
    hhcn.2
    hhcn.2
    metcn
    mp2an
    @17
    @20
    @15
    chil
    chil
    @5
    ax-hilex
    ax-hilex
    elmap
    anbi1i
    3bitr4i
    abbi2i
    3eqtr4i
end
