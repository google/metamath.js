include "cuni.mm"
include "cdm.mm"
include "cv.mm"
include "ciun.mm"
include "dmuni.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "df-iun.mm"
include "nfcii.mm"
include "nfcv.mm"
include "nfv.mm"
include "weq.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "cbvrexf.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem bnj1400
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume bnj1400.1: |- ( y e. A -> A. x y e. A )

  disjoint A y
  disjoint x y
  disjoint A z
  disjoint y z
  disjoint x z
  assert |- dom U. A = U_ x e. A dom x

  proof
    cA
    cuni
    cdm
    vz
    cA
    vz
    cv
    #
    cdm
    #
    ciun
    #
    vx
    cA
    vx
    cv
    #
    cdm
    #
    ciun
    #
    vz
    cA
    dmuni
    @5
    vy
    cv
    #
    @4
    wcel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    @2
    vx
    vy
    cA
    @4
    df-iun
    @2
    @6
    @1
    wcel
    #
    vz
    cA
    wrex
    #
    vy
    cab
    @9
    vz
    vy
    cA
    @1
    df-iun
    @8
    @11
    vy
    @7
    @10
    vx
    vz
    cA
    vx
    vy
    cA
    bnj1400.1
    nfcii
    vz
    cA
    nfcv
    @7
    vz
    nfv
    @10
    vx
    nfv
    vx
    vz
    weq
    @4
    @1
    @6
    @3
    @0
    dmeq
    eleq2d
    cbvrexf
    abbii
    eqtr4i
    eqtr4i
    eqtr4i
end
