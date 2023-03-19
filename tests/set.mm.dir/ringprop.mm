include "crg.mm"
include "wcel.mm"
include "wb.mm"
include "wtru.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "wceq.mm"
include "a1i.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wa.mm"
include "oveqi.mm"
include "cmulr.mm"
include "ringpropd.mm"
include "trud.mm"

theorem ringprop
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume ringprop.b: |- ( Base ` K ) = ( Base ` L )
  assume ringprop.p: |- ( +g ` K ) = ( +g ` L )
  assume ringprop.m: |- ( .r ` K ) = ( .r ` L )


  assert |- ( K e. Ring <-> L e. Ring )

  proof
    cK
    crg
    wcel
    cL
    crg
    wcel
    wb
    wtru
    vx
    vy
    cK
    cbs
    cfv
    #
    cK
    cL
    wtru
    @0
    eqidd
    @0
    cL
    cbs
    cfv
    wceq
    wtru
    ringprop.b
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    @1
    @2
    cL
    cplusg
    cfv
    #
    co
    wceq
    wtru
    @1
    @0
    wcel
    @2
    @0
    wcel
    wa
    wa
    #
    @3
    @4
    @1
    @2
    ringprop.p
    oveqi
    a1i
    @1
    @2
    cK
    cmulr
    cfv
    #
    co
    @1
    @2
    cL
    cmulr
    cfv
    #
    co
    wceq
    @5
    @6
    @7
    @1
    @2
    ringprop.m
    oveqi
    a1i
    ringpropd
    trud
end
