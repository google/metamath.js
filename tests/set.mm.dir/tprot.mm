include "cv.mm"
include "wceq.mm"
include "w3o.mm"
include "cab.mm"
include "ctp.mm"
include "3orrot.mm"
include "abbii.mm"
include "dftp2.mm"
include "3eqtr4i.mm"

theorem tprot
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- { A , B , C } = { B , C , A }

  proof
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    #
    @0
    cC
    wceq
    #
    w3o
    #
    vx
    cab
    @2
    @3
    @1
    w3o
    #
    vx
    cab
    cA
    cB
    cC
    ctp
    cB
    cC
    cA
    ctp
    @4
    @5
    vx
    @1
    @2
    @3
    3orrot
    abbii
    vx
    cA
    cB
    cC
    dftp2
    vx
    cB
    cC
    cA
    dftp2
    3eqtr4i
end
