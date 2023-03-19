include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cintop.mm"
include "co.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cmap.mm"
include "df-intop.mm"
include "elmpt2cl.mm"
include "intopval.mm"
include "eleq2d.mm"
include "elmapi.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem intop
  let cM: class M
  let cN: class N
  let c.op: class .o.
  let vm: setvar m
  let vn: setvar n
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( .o. e. ( M intOp N ) -> .o. : ( M X. M ) --> N )

  proof
    cM
    cvv
    wcel
    cN
    cvv
    wcel
    wa
    #
    c.op
    cM
    cN
    cintop
    co
    #
    wcel
    #
    cM
    cM
    cxp
    #
    cN
    c.op
    wf
    #
    vm
    vn
    cvv
    cvv
    vn
    cv
    vm
    cv
    #
    @5
    cxp
    cmap
    co
    cM
    cN
    cintop
    c.op
    vm
    vn
    df-intop
    elmpt2cl
    @0
    @2
    c.op
    cN
    @3
    cmap
    co
    #
    wcel
    @4
    @0
    @1
    @6
    c.op
    cM
    cN
    cvv
    cvv
    intopval
    eleq2d
    c.op
    cN
    @3
    elmapi
    syl6bi
    mpcom
end
