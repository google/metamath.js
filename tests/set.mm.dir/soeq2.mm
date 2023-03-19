include "wceq.mm"
include "wor.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "wb.mm"
include "soss.mm"
include "anim12i.mm"
include "eqss.mm"
include "dfbi2.mm"
include "3imtr4i.mm"
include "bicomd.mm"

theorem soeq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R Or A <-> R Or B ) )

  proof
    cA
    cB
    wceq
    #
    cB
    cR
    wor
    #
    cA
    cR
    wor
    #
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    @1
    @2
    wi
    #
    @2
    @1
    wi
    #
    wa
    @0
    @1
    @2
    wb
    @3
    @5
    @4
    @6
    cA
    cB
    cR
    soss
    cB
    cA
    cR
    soss
    anim12i
    cA
    cB
    eqss
    @1
    @2
    dfbi2
    3imtr4i
    bicomd
end
