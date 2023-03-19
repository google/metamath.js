include "cgru.mm"
include "wcel.mm"
include "wa.mm"
include "gruelss.mm"
include "sseld.mm"
include "3impia.mm"

theorem gruel
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B e. A ) -> B e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cA
    wcel
    cB
    cU
    wcel
    @0
    @1
    wa
    cA
    cU
    cB
    cA
    cU
    gruelss
    sseld
    3impia
end
