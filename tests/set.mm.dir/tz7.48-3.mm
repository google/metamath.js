include "cv.mm"
include "cfv.mm"
include "cima.mm"
include "cdif.mm"
include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "cvv.mm"
include "crn.mm"
include "cdm.mm"
include "onprc.mm"
include "wfn.mm"
include "wceq.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq1i.mm"
include "mtbir.mm"
include "ccnv.mm"
include "wfun.mm"
include "wi.mm"
include "tz7.48-2.mm"
include "funrnex.mm"
include "com12.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "3imtr4g.mm"
include "syl.mm"
include "mtoi.mm"
include "wss.mm"
include "tz7.48-1.mm"
include "ssexg.mm"
include "ex.mm"
include "mtod.mm"

theorem tz7.48-3
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume tz7.48.1: |- F Fn On

  disjoint F x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint F y
  disjoint F z
  disjoint F w
  assert |- ( A. x e. On ( F ` x ) e. ( A \ ( F " x ) ) -> -. A e. _V )

  proof
    vx
    cv
    #
    cF
    cfv
    cA
    cF
    @0
    cima
    cdif
    wcel
    vx
    con0
    wral
    #
    cA
    cvv
    wcel
    #
    cF
    crn
    #
    cvv
    wcel
    #
    @1
    @4
    cF
    cdm
    #
    cvv
    wcel
    #
    @6
    con0
    cvv
    wcel
    onprc
    @5
    con0
    cvv
    cF
    con0
    wfn
    @5
    con0
    wceq
    tz7.48.1
    con0
    cF
    fndm
    ax-mp
    eleq1i
    mtbir
    @1
    cF
    ccnv
    #
    wfun
    #
    @4
    @6
    wi
    vx
    cA
    cF
    tz7.48.1
    tz7.48-2
    @8
    @7
    cdm
    #
    cvv
    wcel
    #
    @7
    crn
    #
    cvv
    wcel
    #
    @4
    @6
    @10
    @8
    @12
    cvv
    @7
    funrnex
    com12
    @3
    @9
    cvv
    cF
    df-rn
    eleq1i
    @5
    @11
    cvv
    cF
    dfdm4
    eleq1i
    3imtr4g
    syl
    mtoi
    @1
    @3
    cA
    wss
    #
    @2
    @4
    wi
    vx
    cA
    cF
    tz7.48.1
    tz7.48-1
    @13
    @2
    @4
    @3
    cA
    cvv
    ssexg
    ex
    syl
    mtod
end
