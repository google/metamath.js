include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "domen.mm"
include "ensym.mm"
include "anim2i.mm"
include "ancoms.mm"
include "eximi.mm"
include "sylbi.mm"

theorem infcntss
  let vx: setvar x
  let cA: class A
  assume infcntss.1: |- A e. _V

  disjoint A x
  assert |- ( _om ~<_ A -> E. x ( x C_ A /\ x ~~ _om ) )

  proof
    com
    cA
    cdom
    wbr
    com
    vx
    cv
    #
    cen
    wbr
    #
    @0
    cA
    wss
    #
    wa
    #
    vx
    wex
    @2
    @0
    com
    cen
    wbr
    #
    wa
    #
    vx
    wex
    vx
    com
    cA
    infcntss.1
    domen
    @3
    @5
    vx
    @2
    @1
    @5
    @1
    @4
    @2
    com
    @0
    ensym
    anim2i
    ancoms
    eximi
    sylbi
end
