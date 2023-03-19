include "cres.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "brres2.mm"
include "brresALTV.mm"
include "syl5bbr.mm"

theorem brinxprnres
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V


  assert |- ( C e. V -> ( B ( R i^i ( A X. ran ( R |` A ) ) ) C <-> ( B e. A /\ B R C ) ) )

  proof
    cB
    cC
    cR
    cA
    cR
    cA
    cres
    #
    crn
    cxp
    cin
    wbr
    cB
    cC
    @0
    wbr
    cC
    cV
    wcel
    cB
    cA
    wcel
    cB
    cC
    cR
    wbr
    wa
    cA
    cB
    cC
    cR
    brres2
    cA
    cB
    cC
    cR
    cV
    brresALTV
    syl5bbr
end
