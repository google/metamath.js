include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wo.mm"
include "entri2.mm"
include "sdomdom.mm"
include "orim2i.mm"
include "syl.mm"

theorem entri3
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ~<_ B \/ B ~<_ A ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    csdm
    wbr
    #
    wo
    @0
    cB
    cA
    cdom
    wbr
    #
    wo
    cA
    cB
    cV
    cW
    entri2
    @1
    @2
    @0
    cB
    cA
    sdomdom
    orim2i
    syl
end
