include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "wcel.mm"
include "weu.mm"
include "eqtr3.mm"
include "gen2.mm"
include "biantru.mm"
include "isset.mm"
include "eqeq1.mm"
include "eu4.mm"
include "3bitr4i.mm"

theorem eueq
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. _V <-> E! x x = A )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    @2
    @1
    vy
    cv
    #
    cA
    wceq
    #
    wa
    @0
    @3
    wceq
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    cA
    cvv
    wcel
    @1
    vx
    weu
    @6
    @2
    @5
    vx
    vy
    @0
    @3
    cA
    eqtr3
    gen2
    biantru
    vx
    cA
    isset
    @1
    @4
    vx
    vy
    @0
    @3
    cA
    eqeq1
    eu4
    3bitr4i
end
