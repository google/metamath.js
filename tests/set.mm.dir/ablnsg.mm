include "cabl.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "csubg.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wb.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "ablcom.mm"
include "3expb.mm"
include "eleq1d.mm"
include "ralrimivva.mm"
include "isnsg.mm"
include "rbaib.mm"
include "syl.mm"
include "eqrdv.mm"

theorem ablnsg
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( G e. Abel -> ( NrmSGrp ` G ) = ( SubGrp ` G ) )

  proof
    cG
    cabl
    wcel
    #
    vx
    cG
    cnsg
    cfv
    #
    cG
    csubg
    cfv
    #
    @0
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    vx
    cv
    #
    wcel
    @4
    @3
    @5
    co
    #
    @7
    wcel
    wb
    #
    vz
    cG
    cbs
    cfv
    #
    wral
    vy
    @10
    wral
    #
    @7
    @1
    wcel
    #
    @7
    @2
    wcel
    #
    wb
    @0
    @9
    vy
    vz
    @10
    @10
    @0
    @3
    @10
    wcel
    #
    @4
    @10
    wcel
    #
    wa
    wa
    @6
    @8
    @7
    @0
    @14
    @15
    @6
    @8
    wceq
    @10
    @5
    cG
    @3
    @4
    @10
    eqid
    #
    @5
    eqid
    #
    ablcom
    3expb
    eleq1d
    ralrimivva
    @12
    @13
    @11
    vy
    vz
    @5
    @7
    cG
    @10
    @16
    @17
    isnsg
    rbaib
    syl
    eqrdv
end
