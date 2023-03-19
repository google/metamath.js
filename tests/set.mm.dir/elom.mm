include "cv.mm"
include "wlim.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "con0.mm"
include "com.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi2d.mm"
include "albidv.mm"
include "df-om.mm"
include "elrab2.mm"

theorem elom
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. _om <-> ( A e. On /\ A. x ( Lim x -> A e. x ) ) )

  proof
    vx
    cv
    #
    wlim
    #
    vy
    cv
    #
    @0
    wcel
    #
    wi
    #
    vx
    wal
    @1
    cA
    @0
    wcel
    #
    wi
    #
    vx
    wal
    vy
    cA
    con0
    com
    @2
    cA
    wceq
    #
    @4
    @6
    vx
    @7
    @3
    @5
    @1
    @2
    cA
    @0
    eleq1
    imbi2d
    albidv
    vy
    vx
    df-om
    elrab2
end
