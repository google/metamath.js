include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cab.mm"
include "c2o.mm"
include "com.mm"
include "cdom.mm"
include "alephgeom.mm"
include "cvv.mm"
include "wi.mm"
include "fvex.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "sylbi.mm"
include "domrefg.mm"
include "infmap.mm"
include "sylancl.mm"
include "wb.mm"
include "pm3.2.mm"
include "pm2.43i.mm"
include "ssid.mm"
include "alephexp1.mm"
include "enen1.mm"
include "syl.mm"
include "mpbid.mm"

theorem alephexp2
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. On -> ( 2o ^m ( aleph ` A ) ) ~~ { x | ( x C_ ( aleph ` A ) /\ x ~~ ( aleph ` A ) ) } )

  proof
    cA
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    @1
    cmap
    co
    #
    vx
    cv
    #
    @1
    wss
    @3
    @1
    cen
    wbr
    wa
    vx
    cab
    #
    cen
    wbr
    #
    c2o
    @1
    cmap
    co
    #
    @4
    cen
    wbr
    #
    @0
    com
    @1
    cdom
    wbr
    #
    @1
    @1
    cdom
    wbr
    #
    @5
    @0
    com
    @1
    wss
    #
    @8
    cA
    alephgeom
    @1
    cvv
    wcel
    #
    @10
    @8
    wi
    cA
    cale
    fvex
    #
    com
    @1
    cvv
    ssdomg
    ax-mp
    sylbi
    @11
    @9
    @12
    @1
    cvv
    domrefg
    ax-mp
    vx
    @1
    @1
    infmap
    sylancl
    @0
    @2
    @6
    cen
    wbr
    #
    @5
    @7
    wb
    @0
    @0
    @0
    wa
    #
    cA
    cA
    wss
    @13
    @0
    @14
    @0
    @0
    pm3.2
    pm2.43i
    cA
    ssid
    cA
    cA
    alephexp1
    sylancl
    @2
    @6
    @4
    enen1
    syl
    mpbid
end
