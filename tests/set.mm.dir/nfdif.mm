include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "dfdif2.mm"
include "nfcri.mm"
include "nfn.mm"
include "nfrab.mm"
include "nfcxfr.mm"

theorem nfdif
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfdif.1: |- F/_ x A
  assume nfdif.2: |- F/_ x B


  assert |- F/_ x ( A \ B )

  proof
    vx
    cA
    cB
    cdif
    vy
    cv
    cB
    wcel
    #
    wn
    #
    vy
    cA
    crab
    vy
    cA
    cB
    dfdif2
    @1
    vx
    vy
    cA
    @0
    vx
    vx
    vy
    cB
    nfdif.2
    nfcri
    nfn
    nfdif.1
    nfrab
    nfcxfr
end
