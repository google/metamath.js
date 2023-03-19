include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "wn.mm"
include "brdom2.mm"
include "sdomnsym.mm"
include "sdomnen.mm"
include "ensym.mm"
include "nsyl3.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem domnsym
  let cA: class A
  let cB: class B


  assert |- ( A ~<_ B -> -. B ~< A )

  proof
    cA
    cB
    cdom
    wbr
    cA
    cB
    csdm
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    wo
    cB
    cA
    csdm
    wbr
    #
    wn
    #
    cA
    cB
    brdom2
    @0
    @3
    @1
    cA
    cB
    sdomnsym
    @2
    cB
    cA
    cen
    wbr
    @1
    cB
    cA
    sdomnen
    cA
    cB
    ensym
    nsyl3
    jaoi
    sylbi
end
