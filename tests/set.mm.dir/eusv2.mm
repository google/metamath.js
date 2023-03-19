include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "weu.mm"
include "wnfc.mm"
include "wal.mm"
include "eusv2nf.mm"
include "cvv.mm"
include "wcel.mm"
include "eusvnfb.mm"
include "mpbiran2.mm"
include "bitr4i.mm"

theorem eusv2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume eusv2.1: |- A e. _V

  disjoint x y
  disjoint A y
  assert |- ( E! y E. x y = A <-> E! y A. x y = A )

  proof
    vy
    cv
    cA
    wceq
    #
    vx
    wex
    vy
    weu
    vx
    cA
    wnfc
    #
    @0
    vx
    wal
    vy
    weu
    #
    vx
    vy
    cA
    eusv2.1
    eusv2nf
    @2
    @1
    cA
    cvv
    wcel
    eusv2.1
    vx
    vy
    cA
    eusvnfb
    mpbiran2
    bitr4i
end
