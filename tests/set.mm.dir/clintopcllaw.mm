include "cclintop.mm"
include "cfv.mm"
include "wcel.mm"
include "ccllaw.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "clintop.mm"
include "wfn.mm"
include "ffnov.mm"
include "simprbi.mm"
include "syl.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "iscllaw.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem clintopcllaw
  let cM: class M
  let c.op: class .o.
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( .o. e. ( clIntOp ` M ) -> .o. clLaw M )

  proof
    c.op
    cM
    cclintop
    cfv
    #
    wcel
    #
    c.op
    cM
    ccllaw
    wbr
    #
    vx
    cv
    vy
    cv
    c.op
    co
    cM
    wcel
    vy
    cM
    wral
    vx
    cM
    wral
    #
    @1
    cM
    cM
    cxp
    #
    cM
    c.op
    wf
    #
    @3
    cM
    c.op
    clintop
    @5
    c.op
    @4
    wfn
    @3
    vx
    vy
    cM
    cM
    cM
    c.op
    ffnov
    simprbi
    syl
    @1
    cM
    cvv
    wcel
    @2
    @3
    wb
    c.op
    cM
    cclintop
    elfvex
    vx
    vy
    cM
    @0
    cvv
    c.op
    iscllaw
    mpdan
    mpbird
end
