include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "elin.mm"
include "exbii.mm"
include "bitri.mm"

theorem ndisj
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A i^i B ) =/= (/) <-> E. x ( x e. A /\ x e. B ) )

  proof
    cA
    cB
    cin
    #
    c0
    wne
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @1
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    vx
    wex
    vx
    @0
    n0
    @2
    @3
    vx
    @1
    cA
    cB
    elin
    exbii
    bitri
end
