include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "omex.mm"
include "domtri.mm"
include "mpan.mm"
include "isfinite.mm"
include "notbii.mm"
include "syl6rbbr.mm"

theorem infinf
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( -. A e. Fin <-> _om ~<_ A ) )

  proof
    cA
    cB
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    cA
    com
    csdm
    wbr
    #
    wn
    #
    cA
    cfn
    wcel
    #
    wn
    com
    cvv
    wcel
    @0
    @1
    @3
    wb
    omex
    com
    cA
    cvv
    cB
    domtri
    mpan
    @4
    @2
    cA
    isfinite
    notbii
    syl6rbbr
end
