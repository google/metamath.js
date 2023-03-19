include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cen.mm"
include "wa.mm"
include "cab.mm"
include "cvv.mm"
include "ovex.mm"
include "numth3.mm"
include "ax-mp.mm"
include "infmap2.mm"
include "mp3an3.mm"

theorem infmap
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( _om ~<_ A /\ B ~<_ A ) -> ( A ^m B ) ~~ { x | ( x C_ A /\ x ~~ B ) } )

  proof
    com
    cA
    cdom
    wbr
    cB
    cA
    cdom
    wbr
    cA
    cB
    cmap
    co
    #
    ccrd
    cdm
    wcel
    #
    @0
    vx
    cv
    #
    cA
    wss
    @2
    cB
    cen
    wbr
    wa
    vx
    cab
    cen
    wbr
    @0
    cvv
    wcel
    @1
    cA
    cB
    cmap
    ovex
    @0
    cvv
    numth3
    ax-mp
    vx
    cA
    cB
    infmap2
    mp3an3
end
