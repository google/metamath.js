include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "eqvinc.mm"
include "nfeq2.mm"
include "nfan.mm"
include "nfv.mm"
include "eqeq1.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitri.mm"

theorem eqvincf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume eqvincf.1: |- F/_ x A
  assume eqvincf.2: |- F/_ x B
  assume eqvincf.3: |- A e. _V


  assert |- ( A = B <-> E. x ( x = A /\ x = B ) )

  proof
    cA
    cB
    wceq
    vy
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    #
    wa
    #
    vy
    wex
    vx
    cv
    #
    cA
    wceq
    #
    @4
    cB
    wceq
    #
    wa
    #
    vx
    wex
    vy
    cA
    cB
    eqvincf.3
    eqvinc
    @3
    @7
    vy
    vx
    @1
    @2
    vx
    vx
    @0
    cA
    eqvincf.1
    nfeq2
    vx
    @0
    cB
    eqvincf.2
    nfeq2
    nfan
    @7
    vy
    nfv
    @0
    @4
    wceq
    @1
    @5
    @2
    @6
    @0
    @4
    cA
    eqeq1
    @0
    @4
    cB
    eqeq1
    anbi12d
    cbvex
    bitri
end
