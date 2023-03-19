include "cdomn.mm"
include "wcel.mm"
include "cnzr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "domnnzr.mm"
include "opprnzr.mm"
include "syl.mm"
include "w3a.mm"
include "wb.mm"
include "eqid.mm"
include "domneq0.mm"
include "3com23.mm"
include "opprmul.mm"
include "eqeq1i.mm"
include "orcom.mm"
include "3bitr4g.mm"
include "biimpd.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "opprbas.mm"
include "oppr0.mm"
include "isdomn.mm"
include "sylanbrc.mm"

theorem opprdomn
  let cR: class R
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume opprdomn.1: |- O = ( oppR ` R )


  assert |- ( R e. Domn -> O e. Domn )

  proof
    cR
    cdomn
    wcel
    #
    cO
    cnzr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cO
    cmulr
    cfv
    #
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    @2
    @6
    wceq
    #
    @3
    @6
    wceq
    #
    wo
    #
    wi
    #
    vy
    cR
    cbs
    cfv
    #
    wral
    vx
    @12
    wral
    cO
    cdomn
    wcel
    @0
    cR
    cnzr
    wcel
    @1
    cR
    domnnzr
    cR
    cO
    opprdomn.1
    opprnzr
    syl
    @0
    @11
    vx
    vy
    @12
    @12
    @0
    @2
    @12
    wcel
    #
    @3
    @12
    wcel
    #
    @11
    @0
    @13
    @14
    w3a
    #
    @7
    @10
    @15
    @3
    @2
    cR
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    @9
    @8
    wo
    #
    @7
    @10
    @0
    @14
    @13
    @18
    @19
    wb
    @12
    cR
    @16
    @3
    @2
    @6
    @12
    eqid
    #
    @16
    eqid
    #
    @6
    eqid
    #
    domneq0
    3com23
    @5
    @17
    @6
    @12
    cR
    @4
    @16
    cO
    @2
    @3
    @20
    @21
    opprdomn.1
    @4
    eqid
    #
    opprmul
    eqeq1i
    @8
    @9
    orcom
    3bitr4g
    biimpd
    3expb
    ralrimivva
    vx
    vy
    @12
    cO
    @4
    @6
    @12
    cR
    cO
    opprdomn.1
    @20
    opprbas
    @23
    cR
    cO
    @6
    opprdomn.1
    @22
    oppr0
    isdomn
    sylanbrc
end
