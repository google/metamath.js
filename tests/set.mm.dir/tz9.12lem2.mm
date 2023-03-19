include "cima.mm"
include "cuni.mm"
include "con0.mm"
include "wss.mm"
include "wcel.mm"
include "tz9.12lem1.mm"
include "wfun.mm"
include "cvv.mm"
include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "funmpt2.mm"
include "funimaex.mm"
include "ax-mp.mm"
include "ssonunii.mm"
include "onsuci.mm"

theorem tz9.12lem2
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume tz9.12lem.1: |- A e. _V
  assume tz9.12lem.2: |- F = ( z e. _V |-> |^| { v e. On | z e. ( R1 ` v ) } )

  disjoint v z
  disjoint A z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint v y
  disjoint A y
  disjoint F x
  disjoint F y
  assert |- suc U. ( F " A ) e. On

  proof
    cF
    cA
    cima
    #
    cuni
    #
    @0
    con0
    wss
    @1
    con0
    wcel
    vz
    vv
    cA
    cF
    tz9.12lem.1
    tz9.12lem.2
    tz9.12lem1
    @0
    cF
    wfun
    @0
    cvv
    wcel
    vz
    cvv
    vz
    cv
    vv
    cv
    cr1
    cfv
    wcel
    vv
    con0
    crab
    cint
    cF
    tz9.12lem.2
    funmpt2
    cF
    cA
    tz9.12lem.1
    funimaex
    ax-mp
    ssonunii
    ax-mp
    onsuci
end
