include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "opelvvg.mm"
include "wb.mm"
include "opex.mm"
include "relsng.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem relsnopg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> Rel { <. A , B >. } )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cB
    cop
    #
    csn
    wrel
    #
    @1
    cvv
    cvv
    cxp
    wcel
    #
    cA
    cB
    cV
    cW
    opelvvg
    @1
    cvv
    wcel
    @2
    @3
    wb
    @0
    cA
    cB
    opex
    @1
    cvv
    relsng
    mp1i
    mpbird
end
