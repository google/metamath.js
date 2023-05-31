include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "isset.mm"
include "nfeq2.mm"
include "nfv.mm"
include "eqeq1.mm"
include "cbvex.mm"
include "bitri.mm"

theorem issetf
  param vx: setvar x
  param cA: class A
  let vy: setvar y
  assume issetf.1: |- F/_ x A


  assert |- ( A e. _V <-> E. x x = A )

  proof
    cA
    cvv
    wcel
    vy
    cv
    #
    cA
    wceq
    #
    vy
    wex
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    vy
    cA
    isset
    @1
    @3
    vy
    vx
    vx
    @0
    cA
    issetf.1
    nfeq2
    @3
    vy
    nfv
    @0
    @2
    cA
    eqeq1
    cbvex
    bitri
end
