include "cin.mm"
include "wss.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "inss2.mm"
include "orci.mm"
include "inss.mm"
include "ax-mp.mm"
include "inssdif0.mm"
include "mpbi.mm"

theorem inindif
  let cA: class A
  let cC: class C


  assert |- ( ( A i^i C ) i^i ( A \ C ) ) = (/)

  proof
    cA
    cC
    cin
    #
    cA
    cin
    cC
    wss
    #
    @0
    cA
    cC
    cdif
    cin
    c0
    wceq
    @0
    cC
    wss
    #
    cA
    cC
    wss
    #
    wo
    @1
    @2
    @3
    cA
    cC
    inss2
    orci
    @0
    cA
    cC
    inss
    ax-mp
    @0
    cA
    cC
    inssdif0
    mpbi
end
