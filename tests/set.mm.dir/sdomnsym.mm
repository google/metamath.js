include "csdm.mm"
include "wbr.mm"
include "cen.mm"
include "sdomnen.mm"
include "cdom.mm"
include "sdomdom.mm"
include "sbth.mm"
include "syl2an.mm"
include "mtand.mm"

theorem sdomnsym
  let cA: class A
  let cB: class B


  assert |- ( A ~< B -> -. B ~< A )

  proof
    cA
    cB
    csdm
    wbr
    #
    cB
    cA
    csdm
    wbr
    #
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    sdomnen
    @0
    cA
    cB
    cdom
    wbr
    cB
    cA
    cdom
    wbr
    @2
    @1
    cA
    cB
    sdomdom
    cB
    cA
    sdomdom
    cA
    cB
    sbth
    syl2an
    mtand
end
