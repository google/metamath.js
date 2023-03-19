include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "eqidd.mm"
include "lmodgrp.mm"
include "cv.mm"
include "eqid.mm"
include "lmodcom.mm"
include "isabld.mm"

theorem lmodabl
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( W e. LMod -> W e. Abel )

  proof
    cW
    clmod
    wcel
    #
    vx
    vy
    cW
    cbs
    cfv
    #
    cW
    cplusg
    cfv
    #
    cW
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    cW
    lmodgrp
    @2
    @1
    cW
    vx
    cv
    vy
    cv
    @1
    eqid
    @2
    eqid
    lmodcom
    isabld
end
