include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "iscmn.mm"
include "simplbi.mm"

theorem cmnmnd
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( G e. CMnd -> G e. Mnd )

  proof
    cG
    ccmn
    wcel
    cG
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    @1
    @0
    @2
    co
    wceq
    vy
    cG
    cbs
    cfv
    #
    wral
    vx
    @3
    wral
    vx
    vy
    @3
    @2
    cG
    @3
    eqid
    @2
    eqid
    iscmn
    simplbi
end
