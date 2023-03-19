include "wcel.mm"
include "cclintop.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "clintopval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "sqxpexg.mm"
include "elmapg.mm"
include "mpdan.mm"
include "bitrd.mm"

theorem isclintop
  let cM: class M
  let cV: class V
  let c.op: class .o.
  let vk: setvar k
  let vx: setvar x


  assert |- ( M e. V -> ( .o. e. ( clIntOp ` M ) <-> .o. : ( M X. M ) --> M ) )

  proof
    cM
    cV
    wcel
    #
    c.op
    cM
    cclintop
    cfv
    #
    wcel
    c.op
    cM
    cM
    cM
    cxp
    #
    cmap
    co
    #
    wcel
    #
    @2
    cM
    c.op
    wf
    #
    @0
    @1
    @3
    c.op
    cM
    cV
    clintopval
    eleq2d
    @0
    @2
    cvv
    wcel
    @4
    @5
    wb
    cM
    cV
    sqxpexg
    cM
    @2
    c.op
    cV
    cvv
    elmapg
    mpdan
    bitrd
end
