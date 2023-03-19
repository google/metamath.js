include "wcel.mm"
include "wa.mm"
include "csdm.mm"
include "wbr.mm"
include "cen.mm"
include "wo.mm"
include "w3o.mm"
include "wn.mm"
include "cdom.mm"
include "domtri.mm"
include "biimprd.mm"
include "brdom2.mm"
include "syl6ib.mm"
include "con1d.mm"
include "orrd.mm"
include "df-3or.mm"
include "sylibr.mm"

theorem entric
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ~< B \/ A ~~ B \/ B ~< A ) )

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
    csdm
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wo
    #
    cB
    cA
    csdm
    wbr
    #
    wo
    @1
    @2
    @4
    w3o
    @0
    @3
    @4
    @0
    @4
    @3
    @0
    @4
    wn
    #
    cA
    cB
    cdom
    wbr
    #
    @3
    @0
    @6
    @5
    cA
    cB
    cV
    cW
    domtri
    biimprd
    cA
    cB
    brdom2
    syl6ib
    con1d
    orrd
    @1
    @2
    @4
    df-3or
    sylibr
end
