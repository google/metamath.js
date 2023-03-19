include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "pwexg.mm"
include "enmappw.mm"
include "mpancom.mm"

theorem enmappwid
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( ~P A ^m ~P A ) ~~ ( ~P ~P A ^m A ) )

  proof
    cA
    cpw
    #
    cvv
    wcel
    cA
    cV
    wcel
    @0
    @0
    cmap
    co
    @0
    cpw
    cA
    cmap
    co
    cen
    wbr
    cA
    cV
    pwexg
    @0
    cA
    cvv
    cV
    enmappw
    mpancom
end
