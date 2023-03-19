include "cgru.mm"
include "wcel.mm"
include "wtr.mm"
include "wss.mm"
include "grutr.mm"
include "trss.mm"
include "imp.mm"
include "sylan.mm"

theorem gruelss
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U ) -> A C_ U )

  proof
    cU
    cgru
    wcel
    cU
    wtr
    #
    cA
    cU
    wcel
    #
    cA
    cU
    wss
    #
    cU
    grutr
    @0
    @1
    @2
    cU
    cA
    trss
    imp
    sylan
end
