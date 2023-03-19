include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "isgrp.mm"
include "simplbi.mm"

theorem grpmnd
  let cG: class G
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let va: setvar a
  let vm: setvar m
  let c.pl: class .+
  let cX: class X
  let c.0: class .0.


  assert |- ( G e. Grp -> G e. Mnd )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    vm
    cv
    va
    cv
    cG
    cplusg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    vm
    cG
    cbs
    cfv
    #
    wrex
    va
    @2
    wral
    @2
    @0
    vm
    cG
    @1
    va
    @2
    eqid
    @0
    eqid
    @1
    eqid
    isgrp
    simplbi
end
