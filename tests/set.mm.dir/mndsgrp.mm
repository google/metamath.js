include "cmnd.mm"
include "wcel.mm"
include "csgrp.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "wrex.mm"
include "eqid.mm"
include "ismnddef.mm"
include "simplbi.mm"

theorem mndsgrp
  let cG: class G
  let ve: setvar e
  let vx: setvar x


  assert |- ( G e. Mnd -> G e. SGrp )

  proof
    cG
    cmnd
    wcel
    cG
    csgrp
    wcel
    ve
    cv
    #
    vx
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    @1
    wceq
    @1
    @0
    @2
    co
    @1
    wceq
    wa
    vx
    cG
    cbs
    cfv
    #
    wral
    ve
    @3
    wrex
    @3
    @2
    ve
    cG
    vx
    @3
    eqid
    @2
    eqid
    ismnddef
    simplbi
end
