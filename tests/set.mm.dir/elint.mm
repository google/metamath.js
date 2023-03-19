include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cint.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi2d.mm"
include "albidv.mm"
include "df-int.mm"
include "elab2.mm"

theorem elint
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume elint.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. |^| B <-> A. x ( x e. B -> A e. x ) )

  proof
    vx
    cv
    #
    cB
    wcel
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
    cB
    cint
    elint.1
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
    cB
    df-int
    elab2
end
