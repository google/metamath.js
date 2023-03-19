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
include "eqid.mm"
include "isdomn.mm"
include "simplbi.mm"

theorem domnnzr
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let c.0: class .0.
  let cB: class B
  let c.x: class .x.
  let cX: class X
  let cY: class Y


  assert |- ( R e. Domn -> R e. NzRing )

  proof
    cR
    cdomn
    wcel
    cR
    cnzr
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cR
    c0g
    cfv
    #
    wceq
    @0
    @3
    wceq
    @1
    @3
    wceq
    wo
    wi
    vy
    cR
    cbs
    cfv
    #
    wral
    vx
    @4
    wral
    vx
    vy
    @4
    cR
    @2
    @3
    @4
    eqid
    @2
    eqid
    @3
    eqid
    isdomn
    simplbi
end
