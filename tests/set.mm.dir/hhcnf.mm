include "cv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "wi.mm"
include "chil.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cc.mm"
include "cmap.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "ccnfn.mm"
include "ccn.mm"
include "df-rab.mm"
include "df-cnfn.mm"
include "wf.mm"
include "ccom.mm"
include "wceq.mm"
include "hilmetdval.mm"
include "normsub.mm"
include "eqtrd.mm"
include "adantll.mm"
include "breq1d.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "abssub.mm"
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
include "cnxmet.mm"
include "cnfldtopn.mm"
include "metcn.mm"
include "mp2an.mm"
include "cnex.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "abbi2i.mm"
include "3eqtr4i.mm"

theorem hhcnf
  let cD: class D
  let cJ: class J
  let cK: class K
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  assume hhcn.1: |- D = ( normh o. -h )
  assume hhcn.2: |- J = ( MetOpen ` D )
  assume hhcn.4: |- K = ( TopOpen ` CCfld )


  assert |- ContFn = ( J Cn K )

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
    cmin
    co
    cabs
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
    cc
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
    ccnfn
    cJ
    cK
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
    df-cnfn
    @18
    vt
    @19
    chil
    cc
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
    cabs
    cmin
    ccom
    #
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
    @30
    @15
    @20
    @29
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
    @28
    @13
    vy
    crp
    @34
    @27
    @12
    vz
    crp
    @34
    @26
    @11
    vw
    chil
    @34
    @0
    chil
    wcel
    #
    wa
    #
    @22
    @4
    @25
    @10
    @36
    @21
    @2
    @3
    clt
    @33
    @35
    @21
    @2
    wceq
    @20
    @33
    @35
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
    @36
    @24
    @8
    @9
    clt
    @20
    @33
    @35
    @24
    @8
    wceq
    #
    @20
    @37
    wa
    @7
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    wa
    #
    @38
    @20
    @33
    @39
    @35
    @40
    chil
    cc
    @1
    @5
    ffvelrn
    chil
    cc
    @0
    @5
    ffvelrn
    anim12dan
    @41
    @24
    @7
    @6
    cmin
    co
    cabs
    cfv
    @8
    @7
    @6
    @23
    @23
    eqid
    cnmetdval
    @7
    @6
    abssub
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
    @23
    cc
    cxmt
    cfv
    wcel
    @32
    @31
    wb
    cD
    hhcn.1
    hilxmet
    cnxmet
    vx
    vy
    vz
    vw
    cD
    @23
    @5
    cJ
    cK
    chil
    cc
    hhcn.2
    cK
    hhcn.4
    cnfldtopn
    metcn
    mp2an
    @17
    @20
    @15
    cc
    chil
    @5
    cnex
    ax-hilex
    elmap
    anbi1i
    3bitr4i
    abbi2i
    3eqtr4i
end
