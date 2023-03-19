include "cv.mm"
include "wcel.mm"
include "wmo.mm"
include "cab.mm"
include "c1o.mm"
include "cdom.mm"
include "wbr.mm"
include "modom.mm"
include "abid2.mm"
include "breq1i.mm"
include "bitri.mm"

theorem modom2
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E* x x e. A <-> A ~<_ 1o )

  proof
    vx
    cv
    cA
    wcel
    #
    vx
    wmo
    @0
    vx
    cab
    #
    c1o
    cdom
    wbr
    cA
    c1o
    cdom
    wbr
    @0
    vx
    modom
    @1
    cA
    c1o
    cdom
    vx
    cA
    abid2
    breq1i
    bitri
end
