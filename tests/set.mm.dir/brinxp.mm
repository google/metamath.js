include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "brinxp2.mm"
include "df-3an.mm"
include "bitri.mm"
include "baibr.mm"

theorem brinxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( A e. C /\ B e. D ) -> ( A R B <-> A ( R i^i ( C X. D ) ) B ) )

  proof
    cA
    cB
    cR
    cC
    cD
    cxp
    cin
    wbr
    #
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    cA
    cB
    cR
    wbr
    #
    @0
    @1
    @2
    @4
    w3a
    @3
    @4
    wa
    cA
    cB
    cC
    cD
    cR
    brinxp2
    @1
    @2
    @4
    df-3an
    bitri
    baibr
end
