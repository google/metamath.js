include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqidd.mm"
include "ringgrp.mm"
include "cv.mm"
include "eqid.mm"
include "ringcom.mm"
include "isabld.mm"

theorem ringabl
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. Ring -> R e. Abel )

  proof
    cR
    crg
    wcel
    #
    vx
    vy
    cR
    cbs
    cfv
    #
    cR
    cplusg
    cfv
    #
    cR
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    cR
    ringgrp
    @1
    @2
    cR
    vx
    cv
    vy
    cv
    @1
    eqid
    @2
    eqid
    ringcom
    isabld
end
