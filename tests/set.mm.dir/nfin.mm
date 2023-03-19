include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "dfin5.mm"
include "nfcri.mm"
include "nfrab.mm"
include "nfcxfr.mm"

theorem nfin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfin.1: |- F/_ x A
  assume nfin.2: |- F/_ x B


  assert |- F/_ x ( A i^i B )

  proof
    vx
    cA
    cB
    cin
    vy
    cv
    cB
    wcel
    #
    vy
    cA
    crab
    vy
    cA
    cB
    dfin5
    @0
    vx
    vy
    cA
    vx
    vy
    cB
    nfin.2
    nfcri
    nfin.1
    nfrab
    nfcxfr
end
