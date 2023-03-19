include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "brin.mm"
include "ancom.mm"
include "brxp.mm"
include "anbi1i.mm"
include "3bitri.mm"

theorem brinxp2ALTV
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( C ( R i^i ( A X. B ) ) D <-> ( ( C e. A /\ D e. B ) /\ C R D ) )

  proof
    cC
    cD
    cR
    cA
    cB
    cxp
    #
    cin
    wbr
    cC
    cD
    cR
    wbr
    #
    cC
    cD
    @0
    wbr
    #
    wa
    @2
    @1
    wa
    cC
    cA
    wcel
    cD
    cB
    wcel
    wa
    #
    @1
    wa
    cC
    cD
    cR
    @0
    brin
    @1
    @2
    ancom
    @2
    @3
    @1
    cC
    cD
    cA
    cB
    brxp
    anbi1i
    3bitri
end
