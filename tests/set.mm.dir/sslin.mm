include "wss.mm"
include "cin.mm"
include "ssrin.mm"
include "incom.mm"
include "3sstr4g.mm"

theorem sslin
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ B -> ( C i^i A ) C_ ( C i^i B ) )

  proof
    cA
    cB
    wss
    cA
    cC
    cin
    cB
    cC
    cin
    cC
    cA
    cin
    cC
    cB
    cin
    cA
    cB
    cC
    ssrin
    cC
    cA
    incom
    cC
    cB
    incom
    3sstr4g
end
