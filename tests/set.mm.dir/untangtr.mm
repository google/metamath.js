include "wtr.mm"
include "wel.mm"
include "wn.mm"
include "wral.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "wi.mm"
include "df-tr.mm"
include "ssralv.mm"
include "sylbi.mm"
include "weq.mm"
include "elequ1.mm"
include "elequ2.mm"
include "bitrd.mm"
include "notbid.mm"
include "cbvralv.mm"
include "untuni.mm"
include "bitri.mm"
include "syl6ib.mm"
include "untelirr.mm"
include "ralimi.mm"
include "impbid1.mm"

theorem untangtr
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Tr A -> ( A. x e. A -. x e. x <-> A. x e. A A. y e. x -. y e. y ) )

  proof
    cA
    wtr
    #
    vx
    vx
    wel
    #
    wn
    #
    vx
    cA
    wral
    #
    vy
    vy
    wel
    #
    wn
    #
    vy
    vx
    cv
    #
    wral
    #
    vx
    cA
    wral
    #
    @0
    @3
    @2
    vx
    cA
    cuni
    #
    wral
    #
    @8
    @0
    @9
    cA
    wss
    @3
    @10
    wi
    cA
    df-tr
    @2
    vx
    @9
    cA
    ssralv
    sylbi
    @10
    @5
    vy
    @9
    wral
    @8
    @2
    @5
    vx
    vy
    @9
    vx
    vy
    weq
    #
    @1
    @4
    @11
    @1
    vy
    vx
    wel
    @4
    vx
    vy
    vx
    elequ1
    vx
    vy
    vy
    elequ2
    bitrd
    notbid
    cbvralv
    vy
    vx
    cA
    untuni
    bitri
    syl6ib
    @7
    @2
    vx
    cA
    vy
    @6
    untelirr
    ralimi
    impbid1
end
