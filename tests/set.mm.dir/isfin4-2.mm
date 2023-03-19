include "wcel.mm"
include "cfin4.mm"
include "cv.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "com.mm"
include "cdom.mm"
include "isfin4.mm"
include "infpssr.mm"
include "exlimiv.mm"
include "infpss.mm"
include "impbii.mm"
include "notbii.mm"
include "syl6bb.mm"

theorem isfin4-2
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. Fin4 <-> -. _om ~<_ A ) )

  proof
    cA
    cV
    wcel
    cA
    cfin4
    wcel
    vx
    cv
    #
    cA
    wpss
    @0
    cA
    cen
    wbr
    wa
    #
    vx
    wex
    #
    wn
    com
    cA
    cdom
    wbr
    #
    wn
    vx
    cA
    cV
    isfin4
    @2
    @3
    @2
    @3
    @1
    @3
    vx
    cA
    @0
    infpssr
    exlimiv
    vx
    cA
    infpss
    impbii
    notbii
    syl6bb
end
