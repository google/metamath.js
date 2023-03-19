include "wss.mm"
include "cpjh.mm"
include "cfv.mm"
include "chod.mm"
include "co.mm"
include "cort.mm"
include "cin.mm"
include "wceq.mm"
include "crn.mm"
include "wcel.mm"
include "pjssdif2i.mm"
include "cch.mm"
include "wfn.mm"
include "pjmfn.mm"
include "choccli.mm"
include "chincli.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "cc0.mm"
include "cv.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "wrex.mm"
include "wb.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "wa.mm"
include "pjige0.mm"
include "adantlr.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "ad2antlr.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "pjssposi.mm"
include "bitri.mm"
include "sylib.mm"
include "impbii.mm"

theorem pjssdif1i
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ H <-> ( ( projh ` H ) -op ( projh ` G ) ) e. ran projh )

  proof
    cG
    cH
    wss
    #
    cH
    cpjh
    cfv
    cG
    cpjh
    cfv
    chod
    co
    #
    cH
    cG
    cort
    cfv
    #
    cin
    #
    cpjh
    cfv
    #
    wceq
    #
    @1
    cpjh
    crn
    #
    wcel
    #
    cG
    cH
    pjco.1
    pjco.2
    pjssdif2i
    #
    @5
    @7
    @5
    @7
    @4
    @6
    wcel
    #
    cpjh
    cch
    wfn
    #
    @3
    cch
    wcel
    @9
    pjmfn
    cH
    @2
    pjco.2
    cG
    pjco.1
    choccli
    chincli
    cch
    @3
    cpjh
    fnfvelrn
    mp2an
    @1
    @4
    @6
    eleq1
    mpbiri
    @7
    cc0
    vy
    cv
    #
    @1
    cfv
    #
    @11
    csp
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    @5
    @7
    vx
    cv
    #
    cpjh
    cfv
    #
    @1
    wceq
    #
    vx
    cch
    wrex
    #
    @15
    @10
    @7
    @19
    wb
    pjmfn
    vx
    cch
    @1
    cpjh
    fvelrnb
    ax-mp
    @18
    @15
    vx
    cch
    @16
    cch
    wcel
    #
    @18
    wa
    #
    @14
    vy
    chil
    @21
    @11
    chil
    wcel
    #
    wa
    cc0
    @11
    @17
    cfv
    #
    @11
    csp
    co
    #
    cle
    wbr
    #
    @14
    @20
    @22
    @25
    @18
    @11
    @16
    pjige0
    adantlr
    @18
    @25
    @14
    wb
    @20
    @22
    @18
    @24
    @13
    cc0
    cle
    @18
    @23
    @12
    @11
    csp
    @11
    @17
    @1
    fveq1
    oveq1d
    breq2d
    ad2antlr
    mpbid
    ralrimiva
    rexlimiva
    sylbi
    @15
    @0
    @5
    vy
    cG
    cH
    pjco.1
    pjco.2
    pjssposi
    @8
    bitri
    sylib
    impbii
    bitri
end
