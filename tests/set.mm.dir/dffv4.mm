include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cio.mm"
include "cab.mm"
include "wceq.mm"
include "cuni.mm"
include "dffv3.mm"
include "df-iota.mm"
include "abid2.mm"
include "eqeq1i.mm"
include "abbii.mm"
include "unieqi.mm"
include "3eqtri.mm"

theorem dffv4
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  assert |- ( F ` A ) = U. { x | ( F " { A } ) = { x } }

  proof
    cA
    cF
    cfv
    vy
    cv
    cF
    cA
    csn
    cima
    #
    wcel
    #
    vy
    cio
    @1
    vy
    cab
    #
    vx
    cv
    csn
    #
    wceq
    #
    vx
    cab
    #
    cuni
    @0
    @3
    wceq
    #
    vx
    cab
    #
    cuni
    vy
    cA
    cF
    dffv3
    @1
    vy
    vx
    df-iota
    @5
    @7
    @4
    @6
    vx
    @2
    @0
    @3
    vy
    @0
    abid2
    eqeq1i
    abbii
    unieqi
    3eqtri
end
