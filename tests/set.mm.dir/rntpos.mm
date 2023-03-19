include "cdm.mm"
include "wrel.mm"
include "ctpos.mm"
include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wex.mm"
include "vex.mm"
include "elrn.mm"
include "cop.mm"
include "wceq.mm"
include "ccnv.mm"
include "breldm.mm"
include "dmtpos.mm"
include "eleq2d.mm"
include "syl5ib.mm"
include "relcnv.mm"
include "elrel.mm"
include "mpan.mm"
include "syl6.mm"
include "wi.mm"
include "breq1.mm"
include "cvv.mm"
include "wb.mm"
include "brtpos.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "opex.mm"
include "brelrn.mm"
include "syl6bi.mm"
include "exlimivv.mm"
include "syli.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ex.mm"
include "syl5.mm"
include "syl6bbr.mm"
include "impbid.mm"
include "eqrdv.mm"

theorem rntpos
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel dom F -> ran tpos F = ran F )

  proof
    cF
    cdm
    #
    wrel
    #
    vz
    cF
    ctpos
    #
    crn
    #
    cF
    crn
    #
    @1
    vz
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @6
    vw
    cv
    #
    @5
    @2
    wbr
    #
    vw
    wex
    @1
    @7
    vw
    @5
    @2
    vz
    vex
    #
    elrn
    @1
    @9
    @7
    vw
    @9
    @1
    @8
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    #
    @7
    @1
    @9
    @8
    @0
    ccnv
    #
    wcel
    #
    @15
    @9
    @8
    @2
    cdm
    #
    wcel
    @1
    @17
    @8
    @5
    @2
    vw
    vex
    #
    @10
    breldm
    @1
    @18
    @16
    @8
    cF
    dmtpos
    eleq2d
    syl5ib
    @16
    wrel
    @17
    @15
    @0
    relcnv
    vx
    vy
    @8
    @16
    elrel
    mpan
    syl6
    @14
    @9
    @7
    wi
    vx
    vy
    @14
    @9
    @12
    @11
    cop
    #
    @5
    cF
    wbr
    #
    @7
    @14
    @9
    @13
    @5
    @2
    wbr
    #
    @21
    @8
    @13
    @5
    @2
    breq1
    @5
    cvv
    wcel
    @22
    @21
    wb
    @10
    @11
    @12
    @5
    cF
    cvv
    brtpos
    ax-mp
    #
    syl6bb
    @20
    @5
    cF
    @12
    @11
    opex
    @10
    brelrn
    syl6bi
    exlimivv
    syli
    exlimdv
    syl5bi
    @7
    @8
    @5
    cF
    wbr
    #
    vw
    wex
    @1
    @6
    vw
    @5
    cF
    @10
    elrn
    @1
    @24
    @6
    vw
    @24
    @1
    @8
    @20
    wceq
    #
    vx
    wex
    vy
    wex
    #
    @6
    @24
    @8
    @0
    wcel
    #
    @1
    @26
    @8
    @5
    cF
    @19
    @10
    breldm
    @1
    @27
    @26
    vy
    vx
    @8
    @0
    elrel
    ex
    syl5
    @25
    @24
    @6
    wi
    vy
    vx
    @25
    @24
    @22
    @6
    @25
    @24
    @21
    @22
    @8
    @20
    @5
    cF
    breq1
    @23
    syl6bbr
    @13
    @5
    @2
    @11
    @12
    opex
    @10
    brelrn
    syl6bi
    exlimivv
    syli
    exlimdv
    syl5bi
    impbid
    eqrdv
end
