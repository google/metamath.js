include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "w3a.mm"
include "brin.mm"
include "ancom.mm"
include "brxp.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem brinxp2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( A ( R i^i ( C X. D ) ) B <-> ( A e. C /\ B e. D /\ A R B ) )

  proof
    cA
    cB
    cR
    cC
    cD
    cxp
    #
    cin
    wbr
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    @0
    wbr
    #
    wa
    @2
    @1
    wa
    #
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    @1
    w3a
    #
    cA
    cB
    cR
    @0
    brin
    @1
    @2
    ancom
    @3
    @4
    @5
    wa
    #
    @1
    wa
    @6
    @2
    @7
    @1
    cA
    cB
    cC
    cD
    brxp
    anbi1i
    @4
    @5
    @1
    df-3an
    bitr4i
    3bitri
end
