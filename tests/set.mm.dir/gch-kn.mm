include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "cale.mm"
include "cfv.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "wb.mm"
include "alephexp2.mm"
include "enen2.mm"
include "syl.mm"
include "bicomd.mm"

theorem gch-kn
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. On -> ( ( aleph ` suc A ) ~~ { x | ( x C_ ( aleph ` A ) /\ x ~~ ( aleph ` A ) ) } <-> ( aleph ` suc A ) ~~ ( 2o ^m ( aleph ` A ) ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    cale
    cfv
    #
    c2o
    cA
    cale
    cfv
    #
    cmap
    co
    #
    cen
    wbr
    #
    @1
    vx
    cv
    #
    @2
    wss
    @5
    @2
    cen
    wbr
    wa
    vx
    cab
    #
    cen
    wbr
    #
    @0
    @3
    @6
    cen
    wbr
    @4
    @7
    wb
    vx
    cA
    alephexp2
    @3
    @6
    @1
    enen2
    syl
    bicomd
end
