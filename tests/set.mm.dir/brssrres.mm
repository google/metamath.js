include "wcel.mm"
include "cssr.mm"
include "cres.mm"
include "wbr.mm"
include "wa.mm"
include "wss.mm"
include "brresALTV.mm"
include "brssr.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem brssrres
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( C e. V -> ( B ( _S |` A ) C <-> ( B e. A /\ B C_ C ) ) )

  proof
    cC
    cV
    wcel
    #
    cB
    cC
    cssr
    cA
    cres
    wbr
    cB
    cA
    wcel
    #
    cB
    cC
    cssr
    wbr
    #
    wa
    @1
    cB
    cC
    wss
    #
    wa
    cA
    cB
    cC
    cssr
    cV
    brresALTV
    @0
    @2
    @3
    @1
    cB
    cC
    cV
    brssr
    anbi2d
    bitrd
end
