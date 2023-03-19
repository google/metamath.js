include "cabl.mm"
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
include "ablpropd.mm"
include "trud.mm"

theorem ablprop
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume ablprop.b: |- ( Base ` K ) = ( Base ` L )
  assume ablprop.p: |- ( +g ` K ) = ( +g ` L )


  assert |- ( K e. Abel <-> L e. Abel )

  proof
    cK
    cabl
    wcel
    cL
    cabl
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
    ablprop.b
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
    @3
    @4
    @1
    @2
    ablprop.p
    oveqi
    a1i
    ablpropd
    trud
end
