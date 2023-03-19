include "wss.mm"
include "cdif.mm"
include "wceq.mm"
include "dfss4.mm"
include "eqcom.mm"
include "sylbb.mm"
include "difeq2.mm"
include "eqcomd.mm"
include "sylan9eq.mm"

theorem ssdifim
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A C_ V /\ B = ( V \ A ) ) -> A = ( V \ B ) )

  proof
    cA
    cV
    wss
    #
    cB
    cV
    cA
    cdif
    #
    wceq
    #
    cA
    cV
    @1
    cdif
    #
    cV
    cB
    cdif
    #
    @0
    @3
    cA
    wceq
    cA
    @3
    wceq
    cA
    cV
    dfss4
    @3
    cA
    eqcom
    sylbb
    @2
    @4
    @3
    cB
    @1
    cV
    difeq2
    eqcomd
    sylan9eq
end
