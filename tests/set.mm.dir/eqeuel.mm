include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "weu.mm"
include "n0.mm"
include "biimpi.mm"
include "anim1i.mm"
include "eleq1w.mm"
include "eu4.mm"
include "sylibr.mm"

theorem eqeuel
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A =/= (/) /\ A. x A. y ( ( x e. A /\ y e. A ) -> x = y ) ) -> E! x x e. A )

  proof
    cA
    c0
    wne
    #
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cA
    wcel
    #
    wa
    vx
    vy
    weq
    wi
    vy
    wal
    vx
    wal
    #
    wa
    @1
    vx
    wex
    #
    @3
    wa
    @1
    vx
    weu
    @0
    @4
    @3
    @0
    @4
    vx
    cA
    n0
    biimpi
    anim1i
    @1
    @2
    vx
    vy
    vx
    vy
    cA
    eleq1w
    eu4
    sylibr
end
