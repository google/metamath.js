include "cga.mm"
include "co.mm"
include "wcel.mm"
include "cgrp.mm"
include "cvv.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cv.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "eqid.mm"
include "isga.mm"
include "simplbi.mm"
include "simprd.mm"

theorem gaset
  let c.po: class .(+)
  let cG: class G
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( .(+) e. ( G GrpAct Y ) -> Y e. _V )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cG
    cgrp
    wcel
    #
    cY
    cvv
    wcel
    #
    @0
    @1
    @2
    wa
    cG
    cbs
    cfv
    #
    cY
    cxp
    cY
    c.po
    wf
    cG
    c0g
    cfv
    #
    vx
    cv
    #
    c.po
    co
    @5
    wceq
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
    @5
    c.po
    co
    @6
    @7
    @5
    c.po
    co
    c.po
    co
    wceq
    vz
    @3
    wral
    vy
    @3
    wral
    wa
    vx
    cY
    wral
    wa
    vx
    vy
    vz
    @8
    c.po
    cG
    @3
    cY
    @4
    @3
    eqid
    @8
    eqid
    @4
    eqid
    isga
    simplbi
    simprd
end
