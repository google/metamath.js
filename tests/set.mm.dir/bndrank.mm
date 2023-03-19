include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "csuc.mm"
include "cr1.mm"
include "word.mm"
include "wb.mm"
include "rankon.mm"
include "onordi.mm"
include "eloni.mm"
include "ordsucsssuc.mm"
include "sylancr.mm"
include "wi.mm"
include "onsuci.mm"
include "suceloni.mm"
include "r1ord3.mm"
include "sylbid.mm"
include "vex.mm"
include "rankid.mm"
include "ssel.mm"
include "syl6mpi.mm"
include "ralimdv.mm"
include "dfss3.mm"
include "fvex.mm"
include "ssex.mm"
include "sylbir.mm"
include "syl6.mm"
include "rexlimiv.mm"

theorem bndrank
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( E. x e. On A. y e. A ( rank ` y ) C_ x -> A e. _V )

  proof
    vy
    cv
    #
    crnk
    cfv
    #
    vx
    cv
    #
    wss
    #
    vy
    cA
    wral
    #
    cA
    cvv
    wcel
    #
    vx
    con0
    @2
    con0
    wcel
    #
    @4
    @0
    @2
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @5
    @6
    @3
    @9
    vy
    cA
    @6
    @3
    @1
    csuc
    #
    cr1
    cfv
    #
    @8
    wss
    #
    @0
    @12
    wcel
    @9
    @6
    @3
    @11
    @7
    wss
    #
    @13
    @6
    @1
    word
    @2
    word
    @3
    @14
    wb
    @1
    @0
    rankon
    #
    onordi
    @2
    eloni
    @1
    @2
    ordsucsssuc
    sylancr
    @6
    @11
    con0
    wcel
    @7
    con0
    wcel
    @14
    @13
    wi
    @1
    @15
    onsuci
    @2
    suceloni
    @11
    @7
    r1ord3
    sylancr
    sylbid
    @0
    vy
    vex
    rankid
    @12
    @8
    @0
    ssel
    syl6mpi
    ralimdv
    @10
    cA
    @8
    wss
    @5
    vy
    cA
    @8
    dfss3
    cA
    @8
    @7
    cr1
    fvex
    ssex
    sylbir
    syl6
    rexlimiv
end
