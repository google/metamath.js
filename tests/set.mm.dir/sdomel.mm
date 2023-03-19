include "con0.mm"
include "wcel.mm"
include "csdm.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wss.mm"
include "cdom.mm"
include "wn.mm"
include "ssdomg.mm"
include "adantl.mm"
include "ontri1.mm"
include "domtriord.mm"
include "3imtr3d.mm"
include "con4d.mm"
include "ancoms.mm"

theorem sdomel
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A ~< B -> A e. B ) )

  proof
    cB
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    wcel
    #
    wi
    @0
    @1
    wa
    #
    @3
    @2
    @4
    cB
    cA
    wss
    #
    cB
    cA
    cdom
    wbr
    #
    @3
    wn
    @2
    wn
    @1
    @5
    @6
    wi
    @0
    cB
    cA
    con0
    ssdomg
    adantl
    cB
    cA
    ontri1
    cB
    cA
    domtriord
    3imtr3d
    con4d
    ancoms
end
