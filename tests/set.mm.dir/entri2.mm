include "wcel.mm"
include "wa.mm"
include "csdm.mm"
include "wbr.mm"
include "cen.mm"
include "w3o.mm"
include "cdom.mm"
include "wo.mm"
include "entric.mm"
include "brdom2.mm"
include "orbi1i.mm"
include "df-3or.mm"
include "bitr4i.mm"
include "sylibr.mm"

theorem entri2
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ~<_ B \/ B ~< A ) )

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
    csdm
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    cB
    cA
    csdm
    wbr
    #
    w3o
    #
    cA
    cB
    cdom
    wbr
    #
    @2
    wo
    #
    cA
    cB
    cV
    cW
    entric
    @5
    @0
    @1
    wo
    #
    @2
    wo
    @3
    @4
    @6
    @2
    cA
    cB
    brdom2
    orbi1i
    @0
    @1
    @2
    df-3or
    bitr4i
    sylibr
end
