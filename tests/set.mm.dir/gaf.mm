include "cga.mm"
include "co.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "wa.mm"
include "cgrp.mm"
include "cvv.mm"
include "eqid.mm"
include "isga.mm"
include "simprbi.mm"
include "simpld.mm"

theorem gaf
  let c.po: class .(+)
  let cG: class G
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gaf.1: |- X = ( Base ` G )


  assert |- ( .(+) e. ( G GrpAct Y ) -> .(+) : ( X X. Y ) --> Y )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cX
    cY
    cxp
    cY
    c.po
    wf
    #
    cG
    c0g
    cfv
    #
    vx
    cv
    #
    c.po
    co
    @3
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
    @3
    c.po
    co
    @4
    @5
    @3
    c.po
    co
    c.po
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    wa
    vx
    cY
    wral
    #
    @0
    cG
    cgrp
    wcel
    cY
    cvv
    wcel
    wa
    @1
    @7
    wa
    vx
    vy
    vz
    @6
    c.po
    cG
    cX
    cY
    @2
    gaf.1
    @6
    eqid
    @2
    eqid
    isga
    simprbi
    simpld
end
