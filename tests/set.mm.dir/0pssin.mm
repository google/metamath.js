include "c0.mm"
include "cin.mm"
include "wpss.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "0pss.mm"
include "ndisj.mm"
include "bitri.mm"

theorem 0pssin
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( (/) C. ( A i^i B ) <-> E. x ( x e. A /\ x e. B ) )

  proof
    c0
    cA
    cB
    cin
    #
    wpss
    @0
    c0
    wne
    vx
    cv
    #
    cA
    wcel
    @1
    cB
    wcel
    wa
    vx
    wex
    @0
    0pss
    vx
    cA
    cB
    ndisj
    bitri
end
