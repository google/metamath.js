include "ctsk.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wb.mm"
include "elpw2g.mm"
include "adantl.mm"
include "tskpwss.mm"
include "sseld.mm"
include "sylbird.mm"
include "3impia.mm"

theorem tskss
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. T /\ B C_ A ) -> B e. T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    cT
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cT
    wcel
    #
    @0
    @1
    wa
    #
    @2
    cB
    cA
    cpw
    #
    wcel
    #
    @3
    @1
    @6
    @2
    wb
    @0
    cB
    cA
    cT
    elpw2g
    adantl
    @4
    @5
    cT
    cB
    cA
    cT
    tskpwss
    sseld
    sylbird
    3impia
end
